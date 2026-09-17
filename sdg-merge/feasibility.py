"""
Type-II interference — is the merged graph *feasible*?

Type I asks whether `G_M` preserves the contributors' behaviour; Type II asks
whether any program has `G_M` as its PDG at all. It is an ordering problem,
decided one region at a time (a region is one emitted block — see
`reconstitute.regions`, which emission calls too), so the program printed is
the witness of the schedule that was checked.

Four constraint families:

  C1  unique control parent. A statement with two CDG parents would have to be
      emitted inside two different blocks.
  C2  precedence. A flow dependence `d →(x)→ u` orders two members of a
      region; a cycle among members admits no linear order.
  C3  non-interposition. A sibling `d'` that also defines `x` and does not
      flow to `u` must not be scheduled between `d` and `u`, which would kill
      the definition `G_M` says reaches `u`.
  C4  def-order agreement. A stand-in for graphs carrying no def-order edges,
      recovering each contributor's asserted order from its own source
      positions. It defers wherever real `DO` edges are present, and fires
      only on an A-vs-B disagreement — Base's assertion alone would refuse
      good one-sided merges.

The scheduler is greedy with bounded backtracking; PDG feasibility is
NP-complete (HPR '89), and exhausting the budget is reported as infeasible, so
the check errs toward refusal. A loop region that fails to schedule is instead
reported as *inconclusive*, since a loop-carried dependence may legitimately
run backwards. The candidate order is seeded with source position, so a graph
already orderable that way is emitted in that order unchanged.

Run directly for a self-checking demo on corpus fixtures:
    python3 feasibility.py
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from itertools import combinations
from typing import TextIO

import networkx as nx

import reconstitute
from slicer import DEF_ORDER_KINDS, ORDER_KINDS

# Edge kinds that constrain the order of a block: real flow dependences, plus
# the output-ordering edges that are not dependences but are still ordering.
ORDER_CONSTRAINING: tuple[str, ...] = ("DDG",) + ORDER_KINDS + DEF_ORDER_KINDS

LOOP_KEYWORDS = ("while", "for", "do")
SEARCH_BUDGET = 20_000
_MAX_NESTING = 64  # depth guard for the region walk; real CDG nesting is tiny


@dataclass(frozen=True)
class Violation:
    kind: str                      # control-parent | cycle | deadlock | def-order
    detail: str                    # rendered, user-facing
    nodes: tuple[str, ...] = ()
    region: str | None = None


@dataclass
class Type2Result:
    feasible: bool
    order: dict[str, list[str]] = field(default_factory=dict)
    violations: list[Violation] = field(default_factory=list)
    inconclusive: list[str] = field(default_factory=list)  # loop regions


def check(
    g: nx.MultiDiGraph,
    contributors: dict[str, nx.MultiDiGraph] | None = None,
    maps: dict[str, dict[str, str]] | None = None,
) -> Type2Result:
    """Decide whether a program exists whose PDG is `g` (in practice, G_M).

    `contributors` maps a version name to that version's own graph and enables
    C4, which needs each side's source positions; without it C1–C3 are still
    checked. `maps` carries the base→variant correspondences, which C4 needs
    to ask what A and B each did with a guarded definition — `origin_ids`
    alone cannot answer that for a CONTROL_STRUCTURE.
    """
    regions = reconstitute.regions(g)
    tree = _RegionTree(g, regions)
    index = _RegionIndex(g, regions, tree)

    violations = _control_parent_violations(g, regions)
    order: dict[str, list[str]] = {}
    inconclusive: list[str] = []

    for parent, members in regions.items():
        sequence, region_violations, unknown = _order_region(
            g, parent, members, tree, index)
        order[parent] = sequence
        violations += region_violations
        if unknown:
            inconclusive.append(parent)

    # C4 stands down where the graph carries real def-order edges: positions
    # are a merged-frame heuristic, and on a one-sided merge they read a
    # disagreement the real edges say is not there.
    if contributors and not any(
        d.get("kind") in DEF_ORDER_KINDS for _u, _v, d in g.edges(data=True)
    ):
        violations += _def_order_violations(g, contributors, maps or {})

    return Type2Result(
        feasible=not violations,
        order=order,
        violations=violations,
        inconclusive=inconclusive,
    )


# ── C1: one control parent per statement ─────────────────────────────────────
def _control_parent_violations(
    g: nx.MultiDiGraph, regions: dict[str, list[str]]
) -> list[Violation]:
    owners: dict[str, list[str]] = {}
    for parent, members in regions.items():
        for m in members:
            owners.setdefault(m, []).append(parent)

    out: list[Violation] = []
    for m, parents in sorted(owners.items()):
        if len(parents) < 2:
            continue
        entries = [p for p in parents if g.nodes[p].get("label") == "METHOD"]
        conditions = sorted(p for p in parents if p not in entries)
        if entries and len(conditions) == 1:
            # The early-return shape gives `tail` two control parents, both
            # correct: dependent on `c` being false, and an entry edge as a
            # top-level block statement.
            detail = (
                f"{_code(g, m)!r} runs only when {_code(g, conditions[0])!r} is "
                f"false, and is also a top-level statement of "
                f"{_code(g, entries[0])!r} — expressing that needs an `else`, "
                "and our CDG edges carry no branch polarity"
            )
        else:
            blocks = ", ".join(repr(_code(g, p)) for p in sorted(parents))
            detail = (f"{_code(g, m)!r} is controlled by {len(parents)} blocks "
                      f"({blocks}) — it would have to be emitted inside each")
        out.append(Violation(
            kind="control-parent", detail=detail, nodes=(m, *sorted(parents)),
        ))
    return out


# ── the region tree: lifting a vertex to the statement that represents it ────
class _RegionTree:
    """Maps any vertex to the region member standing for it, per region. A
    dependence edge may join vertices nested in two different siblings, so
    each endpoint is lifted to its containing sibling before it constrains."""

    def __init__(self, g: nx.MultiDiGraph, regions: dict[str, list[str]]) -> None:
        self._g = g
        self._parent_of = {m: p for p, members in regions.items() for m in members}
        # A condition is never emitted on its own — it stands for its control
        # structure, which is what actually occupies a slot in the outer block.
        self._owner_of_condition: dict[str, str] = {}
        for members in regions.values():
            for m in members:
                if g.nodes[m].get("label") == "CONTROL_STRUCTURE":
                    condition = reconstitute.condition_of(g, m)
                    if condition is not None:
                        self._owner_of_condition[condition] = m
        self._cache: dict[str, dict[str, str]] = {}

    def memberships(self, n: str) -> dict[str, str]:
        """Region parent → the member of that region that contains `n`."""
        hit = self._cache.get(n)
        if hit is not None:
            return hit
        out: dict[str, str] = {}
        cur = n
        for _ in range(_MAX_NESTING):
            cur = self._owner_of_condition.get(cur, cur)
            parent = self._parent_of.get(cur)
            if parent is None:
                break
            out[parent] = cur
            cur = parent
        if not out:
            host = self._span_host(n)
            if host is not None:
                out = dict(self.memberships(host))
        self._cache[n] = out
        return out

    def parent_of(self, n: str) -> str | None:
        return self._parent_of.get(n)

    def owner_of(self, region_parent: str) -> str | None:
        """The CONTROL_STRUCTURE whose body this region is (None for a method)."""
        return self._owner_of_condition.get(region_parent)

    def _span_host(self, n: str) -> str | None:
        """The statement whose source span encloses a sub-expression — the
        tightest such span.

        A span comparison is meaningful only within one coordinate frame, so a
        host may claim a sub-expression only when both wear the same frame (the
        same first-of-(A, B, Base) attribute winner). Sharing a contributor is
        not enough: in `G_M` a statement contributed by two versions would
        otherwise claim another frame's sub-expression. Per-version graphs have
        no provenance and share one `None` frame.
        """
        d = self._g.nodes[n]
        frame = _frame_of(d)
        best: str | None = None
        best_key: tuple | None = None
        for m in self._parent_of:
            md = self._g.nodes[m]
            if _frame_of(md) != frame:
                continue
            if md.get("method") != d.get("method") or not reconstitute.subsumes(md, d):
                continue
            key = (len(md.get("code") or ""), m)
            if best_key is None or key < best_key:
                best, best_key = m, key
        return best


# ── the region index: every per-region fact, gathered in one pass ────────────
class _RegionIndex:
    """Per-region constraint inputs, bucketed by one walk of the graph.

    An edge can only constrain the regions its endpoints lift into, which
    `_RegionTree.memberships` already names, so the walk happens once and each
    region reads its own bucket rather than rescanning the whole graph per
    constraint family.
    """

    def __init__(
        self, g: nx.MultiDiGraph, regions: dict[str, list[str]], tree: _RegionTree
    ) -> None:
        self.pairs: dict[str, list[tuple[str, str, dict]]] = {p: [] for p in regions}
        self.defs_by_var: dict[str, dict[str | None, set[str]]] = {p: {} for p in regions}
        self.escaping: dict[str, dict[str | None, set[str]]] = {p: {} for p in regions}
        self.ddg_touch: dict[str, dict[str | None, set[str]]] = {p: {} for p in regions}
        member_of = {p: set(ms) for p, ms in regions.items()}

        # `defs` is authoritative where the exporter emits it; only graphs
        # predating the `defs` field fall back to inferring definitions from
        # outgoing DDG edges (unsound — see the note below — but it keeps old
        # JSON working).
        has_defs = any("defs" in d for _, d in g.nodes(data=True))

        for n, d in g.nodes(data=True):
            defs = d.get("defs") or ()
            if not (has_defs and defs):
                continue
            for p, m in tree.memberships(n).items():
                if p in self.defs_by_var:
                    for var in defs:
                        self.defs_by_var[p].setdefault(var, set()).add(m)

        for src, dst, data in g.edges(data=True):
            kind = data.get("kind")
            if kind not in ORDER_CONSTRAINING and kind != "DDG":
                continue
            ms_src = tree.memberships(src)
            ms_dst = tree.memberships(dst)
            var = data.get("variable")

            if kind in ORDER_CONSTRAINING:
                # C2/C3 input: the pair, lifted to each region holding both
                # endpoints as *distinct* members.
                for p, d_m in ms_src.items():
                    u_m = ms_dst.get(p)
                    if u_m is None or u_m == d_m or p not in self.pairs:
                        continue
                    if d_m in member_of[p] and u_m in member_of[p]:
                        self.pairs[p].append((d_m, u_m, data))

            if kind == "DDG":
                for p, inside in ms_src.items():
                    # C3 second half: a definition whose use lives in an
                    # *enclosing* block escapes this one. "Attributable to no
                    # region" is not evidence of escape (see
                    # `_escaping_precedence`'s note), hence `ms_dst and`.
                    if (p in self.escaping and inside in member_of[p]
                            and ms_dst and p not in ms_dst):
                        self.escaping[p].setdefault(var, set()).add(inside)
                for ms in (ms_src, ms_dst):
                    for p, m in ms.items():
                        if p in self.ddg_touch:
                            self.ddg_touch[p].setdefault(var, set()).add(m)
                if not has_defs:
                    for p, m in ms_src.items():
                        if p in self.defs_by_var:
                            self.defs_by_var[p].setdefault(var, set()).add(m)


# ── C2 / C3: ordering one region ─────────────────────────────────────────────
def _order_region(
    g: nx.MultiDiGraph, parent: str, members: list[str], tree: _RegionTree,
    index: _RegionIndex,
) -> tuple[list[str], list[Violation], bool]:
    """Linearise one region. Returns (sequence, violations, inconclusive)."""
    seed = list(members)
    if len(members) < 2:
        return seed, [], False

    defs_by_var = index.defs_by_var[parent]
    carriage = _flow_pairs(index, parent)
    # Kill analysis reasons about real dependences, so it takes them in their
    # true direction, carried or not.
    flow = set(carriage)
    blockers = _interposition(g, parent, members, tree, flow, defs_by_var)
    # Ordering flips the carried-only ones. `d →lc(L) u` says d's value reaches
    # u on the *next* iteration, which in the body text puts d after u —
    # emitting it first would convert the dependence into a loop-independent
    # one and change what the loop computes.
    precedence = {
        (u, d, var) if carried else (d, u, var)
        for (d, u, var), carried in carriage.items()
    }
    # C3 has a second half: a definition that *leaves* this block must
    # be the block's last writer of that variable. `flow` only relates members
    # to each other, so on its own it says nothing about a definition whose use
    # lives outside the block — see `_escaping_precedence`.
    ordering = (precedence
                | _escaping_precedence(index, parent, members, defs_by_var)
                | _declaration_precedence(g, index, parent, members, defs_by_var)
                | _exit_precedence(g, parent, members))

    # The source-position order is the candidate, not the answer: when it
    # satisfies the constraints we keep it, so a graph that was already
    # orderable is emitted exactly as before.
    if _satisfies(seed, ordering, blockers):
        return seed, [], False

    position = {m: i for i, m in enumerate(members)}
    found = _search(members, ordering, blockers, position)
    if found is not None:
        return found, [], False

    if _is_loop_region(g, parent, tree):
        # A backwards dependence in a loop body may simply be loop-carried, and
        # our export does not mark which are — so we decline to call it
        # infeasible and fall back to source order.
        return seed, [], True

    cycle = _precedence_cycle(ordering)
    if cycle:
        return seed, [Violation(
            kind="cycle",
            detail=("flow dependences run in a cycle through "
                    + " → ".join(repr(_code(g, n)) for n in cycle)
                    + " — no member of the block can come first"),
            nodes=tuple(cycle),
            region=parent,
        )], False

    return seed, [Violation(
        kind="deadlock",
        detail=_deadlock_detail(g, members, ordering, blockers, position),
        nodes=tuple(members),
        region=parent,
    )], False


def _flow_pairs(
    index: _RegionIndex, parent: str
) -> dict[tuple[str, str, str | None], bool]:
    """Region-level `(before, after, variable)` pairs, mapped to loop carriage.
    Flow dependences plus `OUT`, which is not a dependence but constrains
    emission exactly as a flow edge does."""
    # (before, after, variable) -> is *every* contributing edge loop-carried?
    seen: dict[tuple[str, str, str | None], bool] = {}
    for d, u, data in index.pairs[parent]:
        key = (d, u, data.get("variable"))
        carried = bool(data.get("carried"))
        # HPR note a dependence may be *both* carried and independent. For
        # ordering the independent one wins, since it must hold within one
        # iteration — so a pair counts as carried only if every edge behind it
        # is.
        seen[key] = carried if key not in seen else (seen[key] and carried)
    return seen


def _escaping_precedence(
    index: _RegionIndex,
    parent: str,
    members: list[str],
    defs_by_var: dict[str | None, set[str]],
) -> set[tuple[str, str, str | None]]:
    """C3, second half: a definition that leaves the block must be the block's
    *last* writer of that variable.

    `_flow_pairs` only relates members of one region, so it says nothing about
    a definition whose use lives outside the block. For every member `d` whose
    definition of `x` escapes, every other member defining `x` without escaping
    must come before `d`. Conditional writers are constrained like any other:
    placed after `d`, the runs where the branch fires would overwrite the value
    `G_M` says leaves the block.
    That a guarded write cannot be *relied on* to kill is the other half of C3
    and no licence here. Members that also escape on `x` are excluded — two
    escaping definitions of one variable are a def-order question (C4, decided
    by `DO` edges), not a kill-order one.

    "Outside this block" means *in an enclosing block*, not merely
    unresolvable: a vertex attributable to no region at all — a sub-expression
    `_span_host` declined to claim, a METHOD_RETURN — is not evidence that the
    definition escapes. Treating it as such made every method-level definition
    look escaping, which manufactured precedence constraints pointing
    *backwards* against real flow edges and reported a cycle in graphs that
    order perfectly well. Nothing can escape the outermost region anyway:
    there is nowhere further out. `_RegionIndex` applies that test as it
    buckets each edge.
    """
    member_set = set(members)
    out: set[tuple[str, str, str | None]] = set()
    for var, escapers in index.escaping[parent].items():
        if var is None:
            continue
        for d in escapers:
            for k in defs_by_var.get(var, ()):
                if k == d or k in escapers or k not in member_set:
                    continue
                out.add((k, d, var))
    return out


def _declaration_precedence(
    g: nx.MultiDiGraph,
    index: _RegionIndex,
    parent: str,
    members: list[str],
    defs_by_var: dict[str | None, set[str]],
) -> set[tuple[str, str, str | None]]:
    """A Java local must be declared before anything that touches it.

    This constraint has no counterpart in HPR: their language has no
    declarations, so a PDG never needed to express it. A scheduler allowed to
    *reorder* a block will otherwise push a declaration past its uses and
    produce a program that does not compile. The exporter marks the
    declaring statement (`declares`); everything in the region that reads or
    writes that variable is ordered after it.
    """
    member_set = set(members)
    touched = index.ddg_touch[parent]
    out: set[tuple[str, str, str | None]] = set()
    for m in members:
        for var in g.nodes[m].get("declares") or ():
            touching = set(defs_by_var.get(var, ())) | touched.get(var, set())
            for other in touching & member_set:
                if other != m:
                    out.add((m, other, var))
    return out


def _frame_of(d: dict) -> str | None:
    """Which contributor's coordinates a `G_M` vertex wears: the first of
    A > B > Base present in its provenance — `merge.py`'s attribute priority,
    which decides whose positions were copied onto the vertex. `None` on plain
    per-version graphs, where every vertex trivially shares the frame."""
    contributed = d.get("contributed_by") or ()
    for version in ("a", "b", "base"):
        if version in contributed:
            return version
    return None


def _exit_precedence(
    g: nx.MultiDiGraph, parent: str, members: list[str]
) -> set[tuple[str, str, str | None]]:
    """A member that unconditionally leaves the block — a bare `return`,
    `break` or `continue` — must be the block's *last* statement: javac
    rejects anything after it as unreachable. Like `declares` this is a
    Java emission constraint with no PDG counterpart, so it belongs here and
    not in the graph.

    It matters only across mixed coordinate frames, because
    only a merged coordinate frame can violate it: in any single version the
    return is last by source order, and the seed order preserves that. In
    `G_M` a callee reached *backward-only* — through its formal-out, into a
    variant's Δ slice — gets its live chain framed in that variant's
    coordinates while its dead declarations, reachable by no slice, ride the
    preserved core in Base's frame; when the variant's file is shorter above
    the method, the live `return` sorts before the dead declaration and the
    emitted method stops compiling.

    Two exit members in one *branch* yield contradictory pairs and hence a
    reported cycle — correctly: no Java program has two bare returns in one
    block, so such a `G_M` is genuinely unrealisable.

    Applied **per branch**, not per region: a predicate's region holds the
    then-block and the early-exit tail under one CDG parent, distinguished only
    by edge polarity, and they are two separate emitted blocks. Grouping by
    polarity keeps a genuine second bare return within one branch contradictory,
    as it should be.
    """
    out: set[tuple[str, str, str | None]] = set()
    groups: dict[object, list[str]] = {}
    for m in members:
        groups.setdefault(reconstitute._branch_of(g, parent, m), []).append(m)
    for group in groups.values():
        for m in group:
            if not _is_jump(g.nodes[m]):
                continue
            for other in group:
                if other != m:
                    out.add((other, m, None))
    return out


def _is_jump(d: dict) -> bool:
    # RETURN, plus the bare break/continue that reconstitution also has to
    # recognise — one definition, in the module that emits them.
    return d.get("label") == "RETURN" or reconstitute.is_jump(d)


def _interposition(
    g: nx.MultiDiGraph,
    parent: str,
    members: list[str],
    tree: _RegionTree,
    flow: set[tuple[str, str, str | None]],
    defs_by_var: dict[str | None, set[str]],
) -> dict[tuple[str, str, str], frozenset[str]]:
    """C3 — per `(d, u, x)`, the members that must not fall between `d` and `u`.

    A member kills `d →(x)→ u` if it also defines `x` and does not itself flow
    `x` into `u` — **including** a CONTROL_STRUCTURE whose body writes `x`.
    C3 is one-directional: interposition never relies on a kill, it *forbids*
    one. A guarded write between `d` and `u` rewires `u`'s flow on exactly the
    runs where its branch fires, so the emitted program's PDG is not `G_M`.
    A guarded writer that legitimately sits
    between `d` and `u` is spared by `reaches`, not by its label: nothing in a
    realisable order can kill its value before `u` without killing `d`'s too,
    so it necessarily flows into `u` itself. A guarded write made dead by an
    early exit inside its own block is blocked over-strictly — refuse rather
    than guess. Two definitions that genuinely both reach `u` are a def-order
    question (C4), not an interposition one.
    """
    reaches: dict[tuple[str, str | None], set[str]] = {}
    for d, u, var in flow:
        reaches.setdefault((u, var), set()).add(d)

    out: dict[tuple[str, str, str], frozenset[str]] = {}
    for d, u, var in sorted(flow, key=lambda t: (t[0], t[1], t[2] or "")):
        if var is None:
            continue
        killers = {
            k for k in defs_by_var.get(var, ())
            if k not in (d, u) and k not in reaches.get((u, var), ())
        }
        if killers:
            out[(d, u, var)] = frozenset(killers)
    return out


def _satisfies(sequence, flow, blockers) -> bool:
    at = {m: i for i, m in enumerate(sequence)}
    if any(at[d] > at[u] for d, u, _ in flow):
        return False
    return not any(
        at[d] < at[k] < at[u]
        for (d, u, _var), killers in blockers.items()
        for k in killers
    )


def _predecessors(members, flow) -> dict[str, set[str]]:
    preds: dict[str, set[str]] = {m: set() for m in members}
    for d, u, _var in flow:
        preds[u].add(d)
    return preds


def _search(members, flow, blockers, position, budget: int = SEARCH_BUDGET):
    """Greedy topological schedule with bounded backtracking; None on failure.

    Source position is the branch *preference*, so where several orders work we
    still emit the one closest to what the contributors wrote. Recursion depth
    is one frame per statement in the region, which is fine at our scale — and
    the search only runs at all when the position order failed validation,
    which no corpus fixture does.
    """
    preds = _predecessors(members, flow)
    preference = sorted(members, key=position.__getitem__)
    total = len(members)
    steps = 0

    def step(emitted: list[str], done: set[str]) -> list[str] | None:
        nonlocal steps
        if len(emitted) == total:
            return list(emitted)
        steps += 1
        if steps > budget:
            return None
        open_pairs = [k for k in blockers if k[0] in done and k[1] not in done]
        for m in preference:
            if m in done or not preds[m] <= done:
                continue
            if any(m in blockers[k] for k in open_pairs):
                continue
            emitted.append(m)
            done.add(m)
            got = step(emitted, done)
            if got is not None:
                return got
            emitted.pop()
            done.discard(m)
        return None

    return step([], set())


def _precedence_cycle(flow) -> list[str]:
    """A cycle in the region's ordering constraints, canonically presented.

    `flow` is a set, so both the graph's edge-insertion order and hence
    `find_cycle`'s starting point vary with PYTHONHASHSEED. The cycle found is
    the same cycle either way, but reported starting at a different vertex —
    enough to make a golden report differ run to run. Sort the edges, then
    rotate the result to begin at its smallest member.
    """
    dag = nx.DiGraph()
    dag.add_edges_from(sorted((d, u) for d, u, _ in flow))
    try:
        cycle = [src for src, _dst in nx.find_cycle(dag)]
    except nx.NetworkXNoCycle:
        return []
    if not cycle:
        return cycle
    start = cycle.index(min(cycle))
    return cycle[start:] + cycle[:start]


def _is_loop_region(g: nx.MultiDiGraph, parent: str, tree: _RegionTree) -> bool:
    """True if this region, or any region enclosing it, is a loop body."""
    cs = tree.owner_of(parent)
    for _ in range(_MAX_NESTING):
        if cs is None:
            return False
        if (g.nodes[cs].get("code") or "").strip().startswith(LOOP_KEYWORDS):
            return True
        enclosing = tree.parent_of(cs)
        cs = tree.owner_of(enclosing) if enclosing is not None else None
    return False


def _deadlock_detail(g, members, flow, blockers, position) -> str:
    """Replay the schedule greedily and describe where every choice ran out."""
    preds = _predecessors(members, flow)
    emitted: list[str] = []
    done: set[str] = set()
    blocked: dict[str, tuple] = {}
    waiting: dict[str, set[str]] = {}
    while len(emitted) < len(members):
        open_pairs = [k for k in blockers if k[0] in done and k[1] not in done]
        blocked: dict[str, tuple] = {}
        waiting: dict[str, set[str]] = {}
        chosen = None
        for m in sorted(set(members) - done, key=position.__getitem__):
            if not preds[m] <= done:
                waiting[m] = preds[m] - done
                continue
            hit = [k for k in open_pairs if m in blockers[k]]
            if hit:
                blocked[m] = hit[0]
            else:
                chosen = m
                break
        if chosen is None:
            break
        emitted.append(chosen)
        done.add(chosen)

    if not blocked and not waiting:
        # greedy alone got everywhere the backtracking search could not: the
        # search hit its budget rather than a genuine deadlock.
        return ("no order found within the search budget — the block's ordering "
                "constraints are satisfiable only in ways this scheduler did not "
                "reach, so the merge is refused rather than guessed")

    parts = [
        "after " + ", ".join(repr(_code(g, m)) for m in emitted)
        if emitted else "from the very start"
    ]
    for m, (d, u, var) in sorted(blocked.items()):
        parts.append(
            f"{_code(g, m)!r} cannot go next — it would kill the definition of "
            f"{var!r} that {_code(g, d)!r} supplies to {_code(g, u)!r}"
        )
    for m, missing in sorted(waiting.items()):
        parts.append(
            f"{_code(g, m)!r} still waits on "
            + ", ".join(repr(_code(g, k)) for k in sorted(missing))
        )
    return "no order exists — " + "; ".join(parts)


# ── C4: def-order agreement across contributors ──────────────────────────────
def _def_order_violations(
    g: nx.MultiDiGraph,
    contributors: dict[str, nx.MultiDiGraph],
    maps: dict[str, dict[str, str]],
) -> list[Violation]:
    out: list[Violation] = []
    for use in sorted(g.nodes):
        by_var: dict[str, set[str]] = {}
        for src, _dst, data in g.in_edges(use, data=True):
            if data.get("kind") == "DDG" and data.get("variable") is not None:
                by_var.setdefault(data["variable"], set()).add(src)

        for var, defs in sorted(by_var.items()):
            if len(defs) < 2:
                continue
            for d1, d2 in combinations(sorted(defs), 2):
                asserted = _asserted_orders(g, contributors, maps, d1, d2, use, var)
                first_a, first_b = asserted.get("a"), asserted.get("b")
                if first_a is None or first_b is None or first_a == first_b:
                    continue
                out.append(Violation(
                    kind="def-order",
                    detail=(
                        f"{_code(g, d1)!r} and {_code(g, d2)!r} both define {var!r} "
                        f"and both reach {_code(g, use)!r}, so which of them comes "
                        f"last decides its value — but A puts {_code(g, first_a)!r} "
                        f"first and B puts {_code(g, first_b)!r} first; no single "
                        f"program does both"
                    ),
                    nodes=(use, d1, d2),
                ))
    return out


def _asserted_orders(
    g: nx.MultiDiGraph,
    contributors: dict[str, nx.MultiDiGraph],
    maps: dict[str, dict[str, str]],
    d1: str,
    d2: str,
    use: str,
    var: str,
) -> dict[str, str]:
    """Per contributor, which of `d1` / `d2` it puts first, read from that
    version's own source positions and counted only where both definitions
    really reach the use in that version."""
    out: dict[str, str] = {}
    for version, cg in contributors.items():
        mapping = maps.get(version, {})
        n1, n2, nu = (_origin(g, n, version, cg, mapping) for n in (d1, d2, use))
        if n1 is None or n2 is None or nu is None:
            continue
        if not (_flows(cg, n1, nu, var) and _flows(cg, n2, nu, var)):
            continue
        k1, k2 = _position(cg, n1), _position(cg, n2)
        if k1 != k2:
            out[version] = d1 if k1 < k2 else d2
    return out


def _origin(
    g: nx.MultiDiGraph,
    node: str,
    version: str,
    cg: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> str | None:
    """`node`'s counterpart in `version` — the vertex that version supplied if
    it contributed one, else whatever the correspondence says it is."""
    if not g.has_node(node):
        return None
    contributed = (g.nodes[node].get("origin_ids") or {}).get(version)
    if contributed is not None:
        return contributed
    # `node` is in the common (Base-id) space when it came from the preserved
    # core, so the base→variant map resolves it; a vertex native to another
    # variant has no counterpart here at all.
    corresponded = mapping.get(node)
    if corresponded is not None:
        return corresponded
    return node if cg.has_node(node) else None


def _flows(cg: nx.MultiDiGraph, src: str, dst: str, var: str) -> bool:
    if not (cg.has_node(src) and cg.has_node(dst)):
        return False
    return any(
        d.get("kind") == "DDG" and d.get("variable") == var
        for d in (cg.get_edge_data(src, dst) or {}).values()
    )


def _position(cg: nx.MultiDiGraph, n: str) -> tuple[int, int]:
    d = cg.nodes[n]
    return (
        d.get("lineNumber") if d.get("lineNumber") is not None else -1,
        d.get("columnNumber") if d.get("columnNumber") is not None else -1,
    )


def _code(g: nx.MultiDiGraph, n: str) -> str:
    if not g.has_node(n):
        return n
    d = g.nodes[n]
    return ((d.get("code") or d.get("name") or d.get("label") or n) or n).strip()


# ── inspection ───────────────────────────────────────────────────────────────
def show(
    result: Type2Result, g: nx.MultiDiGraph | None = None, file: TextIO | None = None
) -> None:
    """Print the feasibility verdict and, on failure, the offending vertices."""
    out = file or sys.stdout
    print("\n=== Type-II feasibility (does a program realise G_M? HRB Fig. 12) ===", file=out)
    blocks = len(result.order)
    print(f"  {blocks} block(s) ordered", file=out)
    for parent in result.inconclusive:
        label = _code(g, parent) if g is not None else parent
        print(f"  inconclusive: loop body at {label!r} — a backwards dependence "
              "there may be loop-carried; source order kept", file=out)
    for v in result.violations:
        print(f"  [{v.kind}] {v.detail}", file=out)
    if result.feasible:
        print("  VERDICT: feasible — every block has a valid statement order", file=out)
    else:
        print("  VERDICT: TYPE-II INFEASIBLE — no program corresponds to G_M", file=out)


# ── demonstration / smoke test ───────────────────────────────────────────────
def _toy(statements: dict[str, str], edges, method_line: int = 1) -> nx.MultiDiGraph:
    """A one-method graph: METHOD entry CDG-controls each statement, in order.

    `statements` maps node id → code (declaration order is source order);
    `edges` is a list of (src, dst, kind, variable).
    """
    g = nx.MultiDiGraph()
    g.add_node("m", label="METHOD", code="void m()", method="M.m",
               lineNumber=method_line, columnNumber=1)
    for i, (nid, code) in enumerate(statements.items(), start=method_line + 1):
        g.add_node(nid, label="CALL", code=code, method="M.m",
                   lineNumber=i, columnNumber=5)
        g.add_edge("m", nid, kind="CDG")
    for src, dst, kind, var in edges:
        g.add_edge(src, dst, kind=kind, variable=var)
    return g


def _demo() -> None:
    # ── C2: two statements that each depend on the other (A and B ordered the
    # same pair opposite ways, so G_M carries both edges).
    cyclic = _toy(
        {"s1": "y = x + 1", "s2": "x = y + 1"},
        [("s1", "s2", "DDG", "y"), ("s2", "s1", "DDG", "x")],
    )
    r = check(cyclic)
    show(r, cyclic)
    assert not r.feasible and r.violations[0].kind == "cycle", r
    print("  (assertion passed: C2 caught the dependence cycle)")

    # ── C3: n2 must sit between n1 and n3 (n1 → n2 → n3), yet it redefines the
    # very variable n1 supplies to n3 — HPR's kill-freedom, unsatisfiable here.
    killed = _toy(
        {"n1": "x = 1", "n2": "x = 2", "n3": "y = x", "n4": "z = x"},
        [("n1", "n2", "DDG", "t"), ("n1", "n3", "DDG", "x"),
         ("n2", "n3", "DDG", "s"), ("n2", "n4", "DDG", "x")],
    )
    r = check(killed)
    show(r, killed)
    assert not r.feasible and r.violations[0].kind == "deadlock", r
    print("  (assertion passed: C3 caught the killing definition)")

    # ── the same graph without the forcing edge is orderable, and the position
    # order already satisfies it — so nothing is reordered.
    fine = _toy(
        {"n1": "x = 1", "n3": "y = x", "n2": "x = 2", "n4": "z = x"},
        [("n1", "n3", "DDG", "x"), ("n2", "n4", "DDG", "x")],
    )
    r = check(fine)
    assert r.feasible, r
    assert r.order["m"] == ["n1", "n3", "n2", "n4"], r.order
    print("\n  (assertion passed: an orderable block keeps its source order)")

    # ── C1: one statement controlled by two blocks at once.
    two_parents = nx.MultiDiGraph()
    two_parents.add_node("m", label="METHOD", code="void m()", method="M.m",
                         lineNumber=1, columnNumber=1)
    two_parents.add_node("cs", label="CONTROL_STRUCTURE", code="if (c)", method="M.m",
                         lineNumber=2, columnNumber=1)
    two_parents.add_node("cond", label="CALL", code="c", method="M.m",
                         lineNumber=2, columnNumber=5)
    two_parents.add_node("s", label="CALL", code="x = 1", method="M.m",
                         lineNumber=3, columnNumber=9)
    for src in ("m", "cond"):
        two_parents.add_edge(src, "s", kind="CDG")
    two_parents.add_edge("m", "cs", kind="CDG")
    two_parents.add_edge("m", "cond", kind="CDG")
    r = check(two_parents)
    show(r, two_parents)
    assert not r.feasible and r.violations[0].kind == "control-parent", r
    print("  (assertion passed: C1 caught the doubly-controlled statement)")

    # ── C3 across a block boundary: two writes to x inside a loop
    # body, only the later one reaching the print after the loop. Nothing
    # relates them at region level — the flow edge lifts to the `while` — so
    # without the kill-order rule the schedule is free to swap them and change
    # which value escaped. Source position here deliberately has them the wrong
    # way round, so the fix has to *reorder*, not merely accept.
    escaping = nx.MultiDiGraph()
    escaping.add_node("m", label="METHOD", code="void m()", method="M.m",
                      lineNumber=1, columnNumber=1)
    escaping.add_node("cs", label="CONTROL_STRUCTURE", code="while (c < 3)",
                      method="M.m", lineNumber=2, columnNumber=1)
    escaping.add_node("cond", label="CALL", code="c < 3", method="M.m",
                      lineNumber=2, columnNumber=8)
    # `defs` is what the exporter now emits; w1 is *dead* (overwritten before
    # any use) so it has no outgoing DDG edge and appears nowhere else.
    escaping.add_node("w2", label="CALL", code="x = 9", method="M.m",
                      lineNumber=3, columnNumber=5, defs=("x",))  # earlier by position …
    escaping.add_node("w1", label="CALL", code="x = 5", method="M.m",
                      lineNumber=4, columnNumber=5, defs=("x",))  # … but must precede w2
    escaping.add_node("p", label="CALL", code="print(x)", method="M.m",
                      lineNumber=5, columnNumber=1)
    for dst in ("cs", "cond", "p"):
        escaping.add_edge("m", dst, kind="CDG")
    for dst in ("w1", "w2"):
        escaping.add_edge("cond", dst, kind="CDG")
    escaping.add_edge("cond", "cs", kind="DDG", variable="c")   # pairs cs↔cond
    escaping.add_edge("w2", "p", kind="DDG", variable="x")      # only w2 escapes

    r = check(escaping)
    body = reconstitute.condition_of(escaping, "cs")
    assert r.feasible, r.violations
    assert r.order[body] == ["w1", "w2"], r.order[body]
    print("\n  (assertion passed: C3 orders the escaping write last, "
          "against source position)")

    # ── C4: HPR Fig. 18. Two guarded definitions of x both reach `y = x`;
    # A wrote them in one order, B in the other. Nothing in G_M's edge set
    # differs from either contributor — only the order does, which is why
    # Type I cannot see this and Type II must.
    def _fig18(first: str, second: str) -> nx.MultiDiGraph:
        g = _toy({first: f"x = {first[-1]}", second: f"x = {second[-1]}",
                  "use": "y = x"}, [])
        g.add_edge(first, "use", kind="DDG", variable="x")
        g.add_edge(second, "use", kind="DDG", variable="x")
        return g

    a_graph = _fig18("d2", "d1")   # A: x = 2 first
    b_graph = _fig18("d1", "d2")   # B: x = 1 first
    g_m = _fig18("d1", "d2")
    for nid in ("d1", "d2", "use"):
        g_m.nodes[nid]["origin_ids"] = {"a": nid, "b": nid}
    r = check(g_m, contributors={"a": a_graph, "b": b_graph})
    show(r, g_m)
    assert not r.feasible and r.violations[0].kind == "def-order", r
    print("  (assertion passed: C4 caught the contradictory def-order)")

    # ── and it must stay quiet when the contributors agree.
    r = check(g_m, contributors={"a": b_graph, "b": b_graph})
    assert r.feasible, r
    print("\n  (assertion passed: C4 stays quiet when both sides agree)")


if __name__ == "__main__":
    _demo()
