"""
Scope — the unit of demand-driven analysis.

A `Scope` is the set of methods a scoped run analyses. A vertex is a
*boundary* iff an interprocedural edge is incident to it, so dependence
leaves a method only through boundaries. `Scope` itself is graph-free; the
per-graph projections take the graph as an argument.

Run directly for a self-checking demo on corpus fixtures:
    python3 scope.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import chain
from typing import Iterable

import networkx as nx

from slicer import SDG_KINDS

# Edge kinds carrying dependence across the interprocedural layer. Field and
# heap edges, once modelled, join this tuple and nothing else changes.
BOUNDARY_KINDS: tuple[str, ...] = SDG_KINDS


@dataclass(frozen=True)
class Scope:
    """A set of method full names, not closed under the call relation: naming
    a method does not pull in its callees. `grow` is API only — the pipeline
    builds its scope in one pass via `scoped.discover`."""

    methods: frozenset[str]

    @classmethod
    def over(cls, methods: Iterable[str]) -> "Scope":
        return cls(frozenset(methods))

    def __contains__(self, method: str) -> bool:
        return method in self.methods

    def grow(self, more: Iterable[str]) -> "Scope":
        return Scope(self.methods | frozenset(more))


def is_boundary(g: nx.MultiDiGraph, v: str) -> bool:
    """Is an interprocedural edge incident to `v`?"""
    edges = chain(g.in_edges(v, data=True), g.out_edges(v, data=True))
    return any(d.get("kind") in BOUNDARY_KINDS for _, _, d in edges)


def boundary_vertices(g: nx.MultiDiGraph, vertices: Iterable[str] | None = None) -> set[str]:
    """Filter `vertices` (default: all of `g`) down to the boundaries. Empty
    for an AP set is the early-exit certificate: dependence has no other way
    out of a method, so the set certifies its own confinement."""
    pool = g.nodes if vertices is None else vertices
    return {v for v in pool if is_boundary(g, v)}


def methods_of(g: nx.MultiDiGraph, vertices: Iterable[str]) -> frozenset[str]:
    """The methods containing `vertices`."""
    return frozenset(g.nodes[v]["method"] for v in vertices)


def vertices(g: nx.MultiDiGraph, scope: Scope) -> set[str]:
    """The vertices of `g` lying in the scope's methods."""
    return {v for v, d in g.nodes(data=True) if d.get("method") in scope}


def subgraph(g: nx.MultiDiGraph, scope: Scope) -> nx.MultiDiGraph:
    """The induced subgraph over the scope's vertices, keeping a recursion's
    own SDG self-edges. Copied, because downstream stages write onto their
    graphs and must not write through to the whole-program one."""
    return g.subgraph(vertices(g, scope)).copy()


def frontier(g: nx.MultiDiGraph, scope: Scope) -> dict[str, frozenset[str]]:
    """In-scope vertices with an interprocedural edge leaving the scope, each
    mapped to the methods one such edge away. Descriptive, not operational:
    the pipeline does not call it. An empty dict means the scoped subgraph of
    `g` is closed."""
    out: dict[str, set[str]] = {}
    for src, dst, d in g.edges(data=True):
        if d.get("kind") not in BOUNDARY_KINDS:
            continue
        src_m, dst_m = g.nodes[src]["method"], g.nodes[dst]["method"]
        if src_m in scope and dst_m not in scope:
            out.setdefault(src, set()).add(dst_m)
        if dst_m in scope and src_m not in scope:
            out.setdefault(dst, set()).add(src_m)
    return {v: frozenset(ms) for v, ms in out.items()}


# ── inspection ───────────────────────────────────────────────────────────────
def show(g: nx.MultiDiGraph, scope: Scope, title: str = "scope") -> None:
    """Print the scope's methods, their sizes, and the current frontier."""
    print(f"\n=== {title}: {len(scope.methods)} method(s) ===")
    for m in sorted(scope.methods):
        n = sum(1 for _, d in g.nodes(data=True) if d.get("method") == m)
        print(f"  {m}  ({n} vertices)")
    fr = frontier(g, scope)
    if not fr:
        print("  frontier: (closed)")
    for v in sorted(fr):
        d = g.nodes[v]
        code = (d.get("code") or d.get("name") or d.get("label") or v).strip()
        print(f"  frontier: {code!r} → {', '.join(sorted(fr[v]))}")


# ── demonstration / smoke test ───────────────────────────────────────────────
def _demo() -> None:
    import correspondence
    from affected import affected_points_sdg, directly_affected
    from pdg import HERE, load_pdg_file

    corpus = HERE.parent / "examples" / "corpus"

    # ── inter_chain: main → outer → inner, A edits the leaf ──────────────────
    d = corpus / "inter_chain"
    base = load_pdg_file(d / "pdg_json" / "base.json")
    a = load_pdg_file(d / "pdg_json" / "a.json")
    mapping = correspondence.solve(base, a, base_src=d / "base.java",
                                   variant_src=d / "a.java")

    dap = directly_affected(base, a, mapping)
    seed = Scope.over(methods_of(a, dap))
    print(f"seed methods (from A's directly-affected points): {sorted(seed.methods)}")
    assert seed.methods == {"Main.inner:int(int)"}, seed.methods

    # Every boundary of the seed method crosses to outer(): entry, formal-in,
    # formal-out.
    fr = frontier(a, seed)
    labels = sorted(a.nodes[v].get("label") for v in fr)
    assert labels == ["METHOD", "METHOD_PARAMETER_IN", "METHOD_RETURN"], labels
    assert all(ms == {"Main.outer:int(int)"} for ms in fr.values()), fr

    # frontier/grow compose to a fixpoint. The pipeline does not build a scope
    # this way; `discover` reaches the same methods in one pass.
    scope = seed
    rounds = []
    while True:
        fr = frontier(a, scope)
        if not fr:
            break
        scope = scope.grow(chain.from_iterable(fr.values()))
        rounds.append(sorted(m.split(".")[1].split(":")[0] for m in scope.methods))
    show(a, scope, title="inter_chain/A after growth to fixpoint")
    assert rounds == [["inner", "outer"], ["inner", "main", "outer"]], rounds
    assert not frontier(a, scope), "fixpoint must be closed"

    # A scope over every method reproduces the graph exactly; the grown scope
    # stops short of it by the uncalled `Main.<init>`.
    everything = subgraph(a, Scope.over(methods_of(a, a.nodes)))
    assert (everything.number_of_nodes(), everything.number_of_edges()) == \
           (a.number_of_nodes(), a.number_of_edges())
    left_out = methods_of(a, a.nodes) - scope.methods
    assert left_out == {"Main.<init>:void()"}, left_out

    # External calls are not boundaries: println has no interprocedural edge.
    println = [v for v, dd in a.nodes(data=True) if dd.get("name") == "println"]
    assert println and not any(is_boundary(a, v) for v in println)
    print("  (assertions passed: seed from the diff, three-vertex frontier, "
          "two growth rounds, closed fixpoint, external calls not boundaries)")

    # ── inter_recursive: a boundary that is not a frontier ───────────────────
    d = corpus / "inter_recursive"
    rec = load_pdg_file(d / "pdg_json" / "base.json")
    fact = "Main.fact:int(int)"
    rec_sites = [v for v, dd in rec.nodes(data=True)
                 if dd.get("label") == "CALL" and dd.get("name") == "fact"
                 and dd.get("method") == fact]
    assert rec_sites and all(is_boundary(rec, v) for v in rec_sites)
    fact_only = Scope.over([fact])
    fr = frontier(rec, fact_only)
    assert all(v not in fr for v in rec_sites), \
        "a recursive call site's edges never leave its method"
    # fact's entry is still a frontier vertex: main() calls it too.
    (entry,) = [v for v, dd in rec.nodes(data=True)
                if dd.get("label") == "METHOD" and dd.get("method") == fact]
    assert fr[entry] == {"Main.main:void(java.lang.String[])"}, fr
    inner_kinds = {dd.get("kind") for _, _, dd in
                   subgraph(rec, fact_only).edges(data=True)}
    assert set(SDG_KINDS) <= inner_kinds, inner_kinds
    print("  (assertions passed: recursion is a boundary but not a frontier, "
          "and its SDG self-edges survive the scoped projection)")

    # ── the early-exit certificate, previewed ────────────────────────────────
    d = corpus / "disjoint"
    dbase = load_pdg_file(d / "pdg_json" / "base.json")
    da = load_pdg_file(d / "pdg_json" / "a.json")
    dmap = correspondence.solve(dbase, da, base_src=d / "base.java",
                                variant_src=d / "a.java")
    assert not boundary_vertices(da, affected_points_sdg(dbase, da, dmap))
    assert boundary_vertices(a, affected_points_sdg(base, a, mapping))
    print("  (assertions passed: disjoint's APs are boundary-free; "
          "inter_chain's cross a boundary and demand expansion)")


if __name__ == "__main__":
    _demo()
