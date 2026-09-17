"""
Demand-driven HRB — seed and scope discovery, and the scoped verdict.

Runs the same pipeline as the whole-program path, over a `Scope` grown from
the diff:

    seed     = the edited methods, plus those a variant deleted vertices from;
    discover = close AP and Δ over the *uncut* graphs; the scope is the set of
               methods those closures entered;
    verdict  = construction, Type I and Type II over the scoped subgraphs,
               certificates consulted first (`run`);
    emit     = scoped methods reconstituted, every other method copied through
               verbatim (`emit`).

`affected` / `merge` / `interference` / `feasibility` are reused unchanged and
fed the scoped projections, so any verdict difference comes from the scope
rather than from a second implementation. `Expansion` carries the seed, the
scope and what the closures pulled in, for cost instrumentation.

Run directly for a self-checking demo on corpus fixtures:
    python3 scoped.py
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

import networkx as nx

import affected
import feasibility
import interference
import invariant
import merge
import reconstitute
from scope import Scope, boundary_vertices, methods_of, subgraph


@dataclass
class Expansion:
    """The discovered scope, what seeded it, and the closures that found it.

    `sets` carries the f-chain per variant — (SAP, AP, Δ) — so the verdict
    stage reuses what discovery already computed instead of re-deriving it.
    Δ is `None` on the early-exit path, which reaches its verdict without
    ever needing it.
    `added` is the methods the closures pulled in beyond the seed: the
    diff's reach across call boundaries."""
    scope: Scope
    seed: frozenset[str]
    sets: dict[str, tuple[set[str], set[str], set[str] | None]] = field(
        default_factory=dict)

    @property
    def added(self) -> frozenset[str]:
        return frozenset(self.scope.methods) - self.seed


@dataclass
class ScopedRun:
    """One scoped pipeline run — same result objects the whole-program run
    yields, plus the scope they were computed under and which `path` decided
    the verdict: "early-exit" (Theorem 1 licensed the intra pipeline),
    "type0" (Theorem 2 licensed skipping Type I's computation), or "full"."""
    expansion: Expansion
    merged: merge.MergeResult
    t1: interference.TypeIResult
    t2: feasibility.Type2Result
    verdict: str
    path: str = "full"


def early_exit_certificate(
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    ap_a: set[str],
    ap_b: set[str],
) -> bool:
    """The early-exit certificate: `AP_A ∪ AP_B` contains no boundary vertex.

    When it holds, the interprocedural verdict equals the intra-procedural
    one, so the SDG passes can be skipped. Interprocedural edges are incident
    only to boundaries, so a closure containing none never had an SDG edge to
    traverse. `evaluate.py` and `fuzz.py` assert the verdict equality wherever
    the certificate holds.
    """
    return not boundary_vertices(a, ap_a) and not boundary_vertices(b, ap_b)


def intra_verdict(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
) -> str:
    """The plain intra-procedural pipeline's verdict (`sdg=False` throughout)
    — the early-exit theorem's other arm. APs are recomputed with the intra
    closures rather than shared with the caller's SDG run, so a comparison
    against the interprocedural verdict assumes nothing the theorem is meant
    to establish."""
    ap_a = affected.affected_points(base, a, map_a)
    ap_b = affected.affected_points(base, b, map_b)
    merged = merge.merge_from_ap(base, a, b, ap_a, ap_b, map_a, map_b, sdg=False)
    t1 = interference.type_i_interference(merged, base, a, b, map_a, map_b,
                                          sdg=False)
    t2 = feasibility.check(merged.graph,
                           contributors={"base": base, "a": a, "b": b},
                           maps={"a": map_a, "b": map_b})
    return invariant.verdict_of(t1, t2)


def restrict_map(
    mapping: dict[str, str], sub_base: nx.MultiDiGraph, sub_var: nx.MultiDiGraph
) -> dict[str, str]:
    """The correspondence, restricted to vertices both scoped graphs kept.

    With whole-method scopes the two containment tests agree (a mapped pair
    shares its method full name; renamed methods are never mapped),
    but both are checked so the restriction stays correct if scoping ever gets
    finer than a method.
    """
    return {b: v for b, v in mapping.items()
            if sub_base.has_node(b) and sub_var.has_node(v)}


def seed_scope(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
) -> tuple[Scope, frozenset[str]]:
    """The edited methods: those holding a directly-affected point in either
    variant, plus those a variant deleted vertices from. Deletions need their
    own rule because they live only on the Base side, where DAP cannot see
    them."""
    dap_a = affected.directly_affected(base, a, map_a)
    dap_b = affected.directly_affected(base, b, map_b)
    deleted_a = {n for n in base.nodes if n not in map_a}
    deleted_b = {n for n in base.nodes if n not in map_b}
    seed = (methods_of(a, dap_a) | methods_of(b, dap_b)
            | methods_of(base, deleted_a) | methods_of(base, deleted_b))
    return Scope.over(seed), seed


def discover(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
    sets: dict[str, tuple[set[str], set[str], set[str]]] | None = None,
) -> Expansion:
    """Scope discovery in one pass: the scope is the methods the AP and Δ
    closures enter.

    Closing over the *uncut* graphs needs no rounds, because a worklist
    closure never visits what it does not reach — cutting the graph first
    only severs the interprocedural edges and forces the closure to be
    rerun. `sets` lets a caller that already ran the f-chain hand it over
    rather than pay twice.
    """
    _sc, seed = seed_scope(base, a, b, map_a, map_b)
    methods = set(seed)
    out: dict[str, tuple[set[str], set[str], set[str]]] = {}
    for version, g, mapping in (("a", a, map_a), ("b", b, map_b)):
        if sets and version in sets:
            sap, ap, dl = sets[version]
        else:
            _dap, sap, ap = affected.affected_sets(base, g, mapping)
            dl = affected.delta_from_ap(g, sap, ap)
        out[version] = (sap, ap, dl)
        # the demand *is* what the closures reached: a vertex in another
        # method can only have been reached across a boundary vertex.
        methods |= set(methods_of(g, ap | dl))
    return Expansion(scope=Scope.over(methods), seed=seed, sets=out)


def run(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
) -> ScopedRun:
    """The scoped verdict, with the certificate fast paths.

    The early-exit certificate is consulted first, on the full graphs; when it
    holds, the intra-procedural pipeline answers outright over the seed scope
    and Δ is never computed. Otherwise `discover` fixes the scope, and the
    Type-0 certificate is read off the Δ slices already built for `G_M`;
    empty both ways, Type I is recorded clean without its closure passes.
    `G_M` is built unconditionally on every path, and Type II always runs —
    neither certificate says anything about feasibility.
    """
    dap_a, sap_a, ap_a = affected.affected_sets(base, a, map_a)
    dap_b, sap_b, ap_b = affected.affected_sets(base, b, map_b)

    if early_exit_certificate(a, b, ap_a, ap_b):
        # The intra pipeline runs on the seed scope, not the whole program:
        # under the certificate the APs are boundary-free and intra edges
        # never leave their method, so every method outside the seed scope is
        # identical in Base, A and B and can contribute no seed.
        sc, seed = seed_scope(base, a, b, map_a, map_b)
        sub = {"base": subgraph(base, sc), "a": subgraph(a, sc),
               "b": subgraph(b, sc)}
        sub_map_a = restrict_map(map_a, sub["base"], sub["a"])
        sub_map_b = restrict_map(map_b, sub["base"], sub["b"])
        sub_ap_a = affected.affected_points(sub["base"], sub["a"], sub_map_a)
        sub_ap_b = affected.affected_points(sub["base"], sub["b"], sub_map_b)
        merged = merge.merge_from_ap(sub["base"], sub["a"], sub["b"],
                                     sub_ap_a, sub_ap_b, sub_map_a, sub_map_b,
                                     sdg=False)
        t1 = interference.type_i_interference(
            merged, sub["base"], sub["a"], sub["b"], sub_map_a, sub_map_b,
            sdg=False)
        t2 = feasibility.check(merged.graph, contributors=sub,
                               maps={"a": sub_map_a, "b": sub_map_b})
        expansion = Expansion(scope=sc, seed=seed,
                              sets={"a": (sap_a, ap_a, None),
                                    "b": (sap_b, ap_b, None)})
        return ScopedRun(expansion=expansion, merged=merged, t1=t1, t2=t2,
                         verdict=invariant.verdict_of(t1, t2),
                         path="early-exit")

    # The certificate's f-chain is exactly what discovery needs; hand it over
    # rather than recompute. Δ is the only piece it still has to close.
    full_sets = {
        "a": (sap_a, ap_a, affected.delta_from_ap(a, sap_a, ap_a)),
        "b": (sap_b, ap_b, affected.delta_from_ap(b, sap_b, ap_b)),
    }
    expansion = discover(base, a, b, map_a, map_b, sets=full_sets)
    sc = expansion.scope
    sub = {"base": subgraph(base, sc), "a": subgraph(a, sc), "b": subgraph(b, sc)}
    sub_map_a = restrict_map(map_a, sub["base"], sub["a"])
    sub_map_b = restrict_map(map_b, sub["base"], sub["b"])

    # discovery already computed the f-chain and Δ — reuse rather than
    # re-derive. Both lie wholly inside the scope by construction (that is
    # what the scope was read off), so they are valid seeds for the scoped
    # construction without restriction.
    _sap_a, ap_a, dl_a = expansion.sets["a"]
    _sap_b, ap_b, dl_b = expansion.sets["b"]
    merged = merge.merge_from_ap(
        sub["base"], sub["a"], sub["b"], ap_a, ap_b, sub_map_a, sub_map_b,
        sdg=True, delta_a=dl_a, delta_b=dl_b,
    )
    pre0 = interference.type_0_from_ap(
        sub["base"], sub["a"], sub["b"], ap_a, ap_b, sub_map_a, sub_map_b,
        sdg=True, slice_a=dl_a, slice_b=dl_b,
    )
    if not pre0.interferes:
        # Theorem 2: empty both ways ⇒ Type I cannot fire. Only the sound
        # direction is ever used (non-empty decides nothing and
        # falls through to the real test).
        t1 = interference.TypeIResult(interferes=False)
        path = "type0"
    else:
        t1 = interference.type_i_interference(
            merged, sub["base"], sub["a"], sub["b"], sub_map_a, sub_map_b,
            sdg=True,
        )
        path = "full"
    t2 = feasibility.check(merged.graph, contributors=sub,
                           maps={"a": sub_map_a, "b": sub_map_b})
    return ScopedRun(
        expansion=expansion, merged=merged, t1=t1, t2=t2,
        verdict=invariant.verdict_of(t1, t2), path=path,
    )


def emit(sr: ScopedRun, base: nx.MultiDiGraph, base_src: Path) -> str:
    """The scoped merge's *program*, not just its verdict.

    A scoped `G_M` holds only the methods in scope, so the rest is copied
    through verbatim from Base's source: a method outside the scope holds no
    affected point and no deletion, so all three versions agree on it.
    Copying the text rather than reconstituting it keeps the untouched part
    byte-identical to what the developer wrote.
    """
    gm = sr.merged.graph
    scope = sr.expansion.scope
    lines = base_src.read_text().splitlines()

    verbatim: dict[str, tuple[str, int, list[str]]] = {}
    for _n, d in base.nodes(data=True):
        method = d.get("method")
        if d.get("label") != "METHOD" or method in scope or method in verbatim:
            continue
        start, end = d.get("lineNumber"), d.get("lineNumberEnd")
        if start is None or end is None:
            continue                      # synthetic <init>: never emitted
        verbatim[method] = (reconstitute._class_name(d), start,
                            lines[start - 1:end])
    return reconstitute.reconstitute(gm, sr.t2.order, verbatim=verbatim)


# ── inspection ───────────────────────────────────────────────────────────────
def show(sr: ScopedRun, total_methods: int | None = None) -> None:
    sc = sr.expansion.scope
    extent = f"{len(sc.methods)}"
    if total_methods is not None:
        extent += f"/{total_methods}"
    added = len(sr.expansion.added)
    print(f"  scope: {extent} methods ({added} pulled in across call "
          f"boundaries); verdict: {sr.verdict} [{sr.path}]")
    for m in sorted(sc.methods):
        tag = "seed" if m in sr.expansion.seed else "grown"
        print(f"    [{tag}] {m}")


# ── demonstration / smoke test ───────────────────────────────────────────────
def _demo() -> None:
    import correspondence
    from pdg import HERE, load_pdg_file

    corpus = HERE.parent / "examples" / "corpus"

    def load(fixture: str):
        d = corpus / fixture
        g = {v: load_pdg_file(d / "pdg_json" / f"{v}.json") for v in ("base", "a", "b")}
        m = {v: correspondence.solve(g["base"], g[v], base_src=d / "base.java",
                                     variant_src=d / f"{v}.java") for v in ("a", "b")}
        return g, m

    def whole_verdict(g, m):
        merged = merge.merge_graphs(g["base"], g["a"], g["b"], m["a"], m["b"], sdg=True)
        t1 = interference.type_i_interference(
            merged, g["base"], g["a"], g["b"], m["a"], m["b"], sdg=True)
        t2 = feasibility.check(merged.graph, contributors=g,
                               maps={"a": m["a"], "b": m["b"]})
        return invariant.verdict_of(t1, t2)

    # (fixture, methods expected in the final scope, methods pulled in beyond the seed)
    cases = [
        # intra-procedural: the scope is main alone and never grows — the
        # interprocedural machinery priced at zero on a local edit.
        ("disjoint", {"main"}, 0),
        # A edits the leaf of main → outer → inner, and B adds a call in main.
        # Nothing pulled in: B's new call vertex is a DAP in main, and it also
        # *rewires* outer's entry (a new CALL in-edge — the step-14 hybrid
        # seed), so all three methods seed outright.
        ("inter_chain", {"main", "outer", "inner"}, 0),
        # edits in two *independent* callees: both enter by seed, and the
        # closures pull in their shared caller — each side's AP escapes its
        # callee through the formal-out.
        ("inter_independent", {"main", "inc", "dec"}, 1),
        # a rename is delete + add: both halves seed (deleted twice() from
        # Base, new triple() in A), and the retargeted caller seeds too.
        ("inter_rename_callee", {"main", "twice", "triple"}, None),
    ]
    for fixture, expect_methods, expect_added in cases:
        g, m = load(fixture)
        sr = run(g["base"], g["a"], g["b"], m["a"], m["b"])
        total = len({d["method"] for _, d in g["base"].nodes(data=True)})
        print(f"\n=== {fixture} ===")
        show(sr, total_methods=total)
        got = {mm.split(".")[1].split(":")[0] for mm in sr.expansion.scope.methods}
        assert got == expect_methods, (fixture, got)
        if expect_added is not None:
            assert len(sr.expansion.added) == expect_added, \
                (fixture, sorted(sr.expansion.added))
        # the point of it all: the scoped verdict equals the whole-program one
        # (the corpus-wide assertion is the differential oracle).
        assert sr.verdict == whole_verdict(g, m), fixture

    # ── the climb, isolated: inter_chain with B ≡ Base ───────────────────────
    # With B's edit out of the picture the seed is the leaf alone, and the
    # closures must climb the chain: AP escapes inner through its formal-out
    # into outer, and outer's into main — two methods pulled in beyond the
    # seed, discovered in the single pass rather than a round each.
    g, m = load("inter_chain")
    map_bb = {n: n for n in g["base"].nodes}
    sr = run(g["base"], g["a"], g["base"], m["a"], map_bb)
    print("\n=== inter_chain, B ≡ Base (one-sided) ===")
    show(sr, total_methods=len({d["method"] for _, d in g["base"].nodes(data=True)}))
    assert {mm.split(".")[1].split(":")[0] for mm in sr.expansion.seed} == {"inner"}
    assert len(sr.expansion.added) == 2, sorted(sr.expansion.added)
    assert sr.verdict == "clean", sr.verdict  # one side changed ⇒ merge is A

    # ── the certificates, on real shapes ─────────────────────────────────────
    # inter_confined: boundaries exist (main calls twice()) but A's edit flows
    # only into its own print — the early-exit certificate holds non-trivially
    # and its licence is honest: the intra verdict equals the SDG one.
    g, m = load("inter_confined")
    ap = {v: affected.affected_points_sdg(g["base"], g[v], m[v]) for v in ("a", "b")}
    assert boundary_vertices(g["a"]), "inter_confined must actually have boundaries"
    assert early_exit_certificate(g["a"], g["b"], ap["a"], ap["b"])
    assert (intra_verdict(g["base"], g["a"], g["b"], m["a"], m["b"])
            == whole_verdict(g, m) == "clean")
    # inter_chain: the APs cross the callee's formal-out — certificate refused,
    # which is exactly when the SDG passes are genuinely needed.
    g, m = load("inter_chain")
    ap = {v: affected.affected_points_sdg(g["base"], g[v], m[v]) for v in ("a", "b")}
    assert not early_exit_certificate(g["a"], g["b"], ap["a"], ap["b"])
    print("\n(assertions passed: seeds from the diff, demand-driven growth, "
          "the isolated one-sided climb, scoped verdict == whole-program "
          "verdict on all shapes, and the early-exit certificate holds with "
          "calls present exactly where its licence is honest)")


if __name__ == "__main__":
    _demo()
