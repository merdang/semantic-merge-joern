"""
Backward (and forward) program slicing over the PDG.

An edge `src -> dst` means *dst depends on src*, so a backward slice walks
incoming edges and a forward slice outgoing ones. Both are worklist fixpoints,
so Joern's dependence cycles terminate.

Run directly for a self-checking demo on corpus fixtures:
    python3 slicer.py
"""

from __future__ import annotations

from typing import Iterable

import networkx as nx

# The edges an intra-procedural slice traverses. The SDG layer is excluded:
# crossing method boundaries soundly needs the two-pass traversal below, not
# a flood fill, which would follow paths no execution can take.
DEP_KINDS: tuple[str, ...] = ("DDG", "CDG")

# Observable-output ordering: two statements writing one stream have no data
# dependence, yet their order is the program's output. Not a dependence kind —
# present in the graph, never traversed. Only `feasibility` reads it.
ORDER_KINDS: tuple[str, ...] = ("OUT",)

# Def-order dependence (HPR §4.1). Like OUT, ordering without traversal, but
# it does seed AP — which is how a reordering becomes an affected point.
DEF_ORDER_KINDS: tuple[str, ...] = ("DO",)

# The interprocedural SDG layer, consumed by the two-pass traversal below.
SDG_KINDS: tuple[str, ...] = ("CALL", "PARAM_IN", "PARAM_OUT")

# Two-pass interprocedural slicing (HRB '90). Summary edges need no kind of
# their own: with the actual vertices bundled onto the call site, the step
# over a call is already an ordinary DDG path through it.
B1_KINDS = DEP_KINDS + ("CALL", "PARAM_IN")  # pass 1: ascend to callers; skip PARAM_OUT
B2_KINDS = DEP_KINDS + ("PARAM_OUT",)        # pass 2: descend into callees; skip CALL/PARAM_IN


def backward_slice_sdg(g: nx.MultiDiGraph, seeds: Iterable[str] | str) -> set[str]:
    """HRB's context-sensitive backward slice over the SDG: `b = b2 ∘ b1`.
    Pass 1 ascends to callers, pass 2 descends into callees and never
    re-ascends, so one call site cannot drag in another caller's context."""
    return _slice(g, _slice(g, seeds, B1_KINDS, None, backward=True),
                  B2_KINDS, None, backward=True)


def forward_slice_sdg(g: nx.MultiDiGraph, seeds: Iterable[str] | str) -> set[str]:
    """The forward dual `f = f2 ∘ f1`, feeding strongly-affected points."""
    return _slice(g, _slice(g, seeds, B2_KINDS, None, backward=False),
                  B1_KINDS, None, backward=False)


def backward_slice(
    g: nx.MultiDiGraph,
    seeds: Iterable[str] | str,
    edge_kinds: tuple[str, ...] = DEP_KINDS,
    variables: set[str] | None = None,
) -> set[str]:
    """Vertices the `seeds` transitively depend on (seeds included).
    `variables` restricts DDG edges to those carrying one of the named
    variables; CDG edges are always followed."""
    return _slice(g, seeds, edge_kinds, variables, backward=True)


def forward_slice(
    g: nx.MultiDiGraph,
    seeds: Iterable[str] | str,
    edge_kinds: tuple[str, ...] = DEP_KINDS,
    variables: set[str] | None = None,
) -> set[str]:
    """Vertices that transitively depend on the `seeds` (seeds included)."""
    return _slice(g, seeds, edge_kinds, variables, backward=False)


def slice_subgraph(
    g: nx.MultiDiGraph,
    seeds: Iterable[str] | str,
    **kwargs,
) -> nx.MultiDiGraph:
    """The induced subgraph over a backward slice. Keyword args pass through
    to `backward_slice`."""
    return g.subgraph(backward_slice(g, seeds, **kwargs)).copy()


def all_backward_slices(
    g: nx.MultiDiGraph,
    edge_kinds: tuple[str, ...] = DEP_KINDS,
) -> dict[str, set[str]]:
    """Backward slice of every vertex, computed independently per vertex."""
    return {nid: backward_slice(g, nid, edge_kinds=edge_kinds) for nid in g.nodes}


# ── core traversal ───────────────────────────────────────────────────────────
def _slice(
    g: nx.MultiDiGraph,
    seeds: Iterable[str] | str,
    edge_kinds: tuple[str, ...],
    variables: set[str] | None,
    backward: bool,
) -> set[str]:
    kinds = frozenset(edge_kinds)
    # Incoming edges for a backward slice (toward predecessors), outgoing for a
    # forward slice (toward successors). `*_edges(v, data=True)` yields each
    # parallel edge separately, so a DDG edge's `variable` is checked per edge.
    step = g.in_edges if backward else g.out_edges

    worklist = [s for s in _as_list(seeds) if g.has_node(s)]
    visited: set[str] = set(worklist)
    while worklist:
        v = worklist.pop()
        for src, dst, data in step(v, data=True):
            kind = data.get("kind")
            if kind not in kinds:
                continue
            if (
                variables is not None
                and kind == "DDG"
                and data.get("variable") not in variables
            ):
                continue
            nxt = src if backward else dst
            if nxt not in visited:
                visited.add(nxt)
                worklist.append(nxt)
    return visited


def _as_list(seeds: Iterable[str] | str) -> list[str]:
    # A bare node-id string is iterable over characters; guard against slicing
    # from "b", "a", "s", "e", … instead of the id "base::…".
    if isinstance(seeds, str):
        return [seeds]
    return list(seeds)


# ── demonstration / smoke test ───────────────────────────────────────────────
def _fmt(g: nx.MultiDiGraph, nid: str) -> str:
    d = g.nodes[nid]
    line = d.get("lineNumber")
    pos = f"L{line}:{d.get('columnNumber')}" if line is not None else "(synth)"
    code = (d.get("code") or "").strip().replace("\n", " ") or (d.get("name") or "")
    if len(code) > 40:
        code = code[:39] + "…"
    return f"{pos:>9}  {(d.get('label') or ''):<20}  {code!r}"


def _print_slice(g: nx.MultiDiGraph, seeds: Iterable[str], title: str) -> None:
    sl = backward_slice(g, seeds)
    print(f"\n=== {title}: {len(sl)} vertices ===")
    for nid in sorted(
        sl,
        key=lambda n: (
            g.nodes[n].get("lineNumber") if g.nodes[n].get("lineNumber") is not None else -1,
            g.nodes[n].get("columnNumber") if g.nodes[n].get("columnNumber") is not None else -1,
        ),
    ):
        print("  " + _fmt(g, nid))


def _demo() -> None:
    from pdg import load_pdg

    g = load_pdg("base")
    method = "Main.main:void(java.lang.String[])"

    # Seed at the method exit. Since the exporter keeps only genuine
    # return-value flow into METHOD_RETURN (RETURN → RET), a void method's
    # exit depends on nothing but the entry: the slice is {METHOD, RET}.
    ret = [
        n for n, d in g.nodes(data=True)
        if d.get("method") == method and d.get("label") == "METHOD_RETURN"
    ]
    _print_slice(g, ret, f"backward slice of METHOD_RETURN  [{method}]")

    # Seed at the printf call: the unused `args` parameter and METHOD_RETURN
    # must drop out — the visible evidence that slicing prunes.
    printf = [
        n for n, d in g.nodes(data=True)
        if d.get("method") == method and d.get("name") == "printf"
    ]
    if printf:
        _print_slice(g, printf, "backward slice of printf(...)  (args + RET should be absent)")

    # ── two-pass slice on a real SDG: context sensitivity ────────────────────
    # inter_callee_edit's B calls twice() from two sites; slicing at the
    # second call's print must descend into the callee without dragging in
    # the first call site's context — the situation b = b2 ∘ b1 exists for.
    from pdg import HERE, load_pdg_file

    fx = HERE.parent / "examples" / "corpus" / "inter_callee_edit" / "pdg_json" / "b.json"
    if not fx.exists():
        print("\n(inter_callee_edit not exported — skipping the two-pass demo)")
        return
    sdg = load_pdg_file(fx)

    def find(**want):
        return [n for n, d in sdg.nodes(data=True)
                if all(d.get(k) == v for k, v in want.items())]

    println_b = find(name="println", lineNumber=6)   # System.out.println(b)
    two_pass = backward_slice_sdg(sdg, println_b)
    flood = backward_slice(sdg, println_b, edge_kinds=DEP_KINDS + SDG_KINDS)
    codes = {sdg.nodes[n].get("code") for n in two_pass}

    (other_call,) = find(name="twice", lineNumber=3)  # the OTHER call site
    print(f"\n=== two-pass SDG slice of println(b)  [inter_callee_edit / B] ===")
    print(f"  b = b2 ∘ b1 : {len(two_pass)} vertices — descends into twice() "
          f"({'return x * 2;' in codes})")
    print(f"  one-pass flood over all kinds: {len(flood)} vertices — "
          f"drags in the other call site ({other_call in flood})")
    assert "return x * 2;" in codes, "two-pass must reach the callee's return"
    assert other_call not in two_pass, "two-pass must keep the other caller's context out"
    assert other_call in flood, "the naive flood shows why two passes are needed"
    assert two_pass < flood
    print("  (assertions passed: context-sensitive descent, no context smearing)")


if __name__ == "__main__":
    _demo()
