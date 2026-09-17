"""
Merged-graph construction.

    G_M  =  G_A / AP_A   ∪   G_B / AP_B   ∪   G_Base / Pre

The union is taken in the common (Base-id) space, so a statement several
versions contributed appears once and new code cannot collide. Every vertex
and edge records its provenance, and clashes the union had to resolve are
recorded rather than silently settled. `G_M` is built unconditionally, before
any interference test: it is the object those tests are defined on.

Run directly for a self-checking demo on corpus fixtures:
    python3 merge.py
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from typing import TextIO

import networkx as nx

from affected import affected_points, affected_points_sdg, delta, delta_from_ap
from correspondence import canonicalizer
from slicer import DEF_ORDER_KINDS, ORDER_KINDS, SDG_KINDS, backward_slice, backward_slice_sdg


@dataclass(frozen=True)
class AttributeConflict:
    """Two contributors supplied the same vertex with different statement text."""
    node: str                                 # common-space id
    codes: tuple[tuple[str, str], ...]        # (version, code) in contribution order


@dataclass(frozen=True)
class EdgeAddition:
    """The union gave `node` incoming dependence edges `version` did not
    have. A diagnostic, not a verdict."""
    node: str
    version: str
    edges: frozenset[tuple]


@dataclass
class MergeResult:
    graph: nx.MultiDiGraph                # G_M, in the common (Base-id) space
    ap_a: set[str] = field(default_factory=set)   # A-native node-ids
    ap_b: set[str] = field(default_factory=set)   # B-native node-ids
    preserved: set[str] = field(default_factory=set)  # Base node-ids (Pre)
    contributions: dict[str, set[str]] = field(default_factory=dict)  # version → common-space ids
    attribute_conflicts: list[AttributeConflict] = field(default_factory=list)
    edge_additions: list[EdgeAddition] = field(default_factory=list)


def merge_graphs(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
    sdg: bool = False,
) -> MergeResult:
    """Compute affected points for both variants, then construct G_M."""
    ap_fn = affected_points_sdg if sdg else affected_points
    ap_a = ap_fn(base, a, map_a)
    ap_b = ap_fn(base, b, map_b)
    return merge_from_ap(base, a, b, ap_a, ap_b, map_a, map_b, sdg=sdg)


def merge_from_ap(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    ap_a: set[str],
    ap_b: set[str],
    map_a: dict[str, str],
    map_b: dict[str, str],
    sdg: bool = False,
    delta_a: set[str] | None = None,
    delta_b: set[str] | None = None,
) -> MergeResult:
    """Construct G_M from pre-computed affected points, avoiding a re-slice.
    A caller already holding the Δ slices passes them as `delta_a`/`delta_b`."""
    pre = preserved_points(base, ap_a, ap_b, map_a, map_b)

    g_m = nx.MultiDiGraph()
    contributions: dict[str, set[str]] = {}
    identity = lambda nid: nid  # Base ids are the common space
    if sdg:
        slices = (
            ("a", a, delta_a if delta_a is not None else delta(base, a, map_a),
             canonicalizer(map_a)),
            ("b", b, delta_b if delta_b is not None else delta(base, b, map_b),
             canonicalizer(map_b)),
            ("base", base, backward_slice_sdg(base, pre), identity),
        )
    else:
        slices = (
            ("a", a, backward_slice(a, ap_a), canonicalizer(map_a)),
            ("b", b, backward_slice(b, ap_b), canonicalizer(map_b)),
            ("base", base, backward_slice(base, pre), identity),
        )
    # Order fixes attribute priority (A > B > Base): the first contributor of a
    # vertex supplies its attributes, later ones only extend the provenance.
    codes_seen: dict[str, list[tuple[str, str]]] = {}
    for version, g, sliced, to_common in slices:
        contributions[version] = {to_common(n) for n in sliced}
        _add_contribution(g_m, g, sliced, to_common, version, codes_seen)

    # Interprocedural layer: the slices traverse DDG ∪ CDG only, so re-attach
    # every SDG edge whose endpoints survived.
    for version, g, sliced, to_common in slices:
        _add_sdg_layer(g_m, g, sliced, to_common, version)

    # Two HPR rules on def-order, both checked here as a post-pass over the
    # final vertex set (a witness may arrive from a later contributor):
    # §4.1.2, the witness must be present, and clause (1), both endpoints must
    # still define the variable. A merged vertex can fail the second, since
    # correspondence identifies statements, not the variables they assign.
    def _defines(node: str, var: str | None) -> bool:
        return var is None or var in (g_m.nodes[node].get("defs") or ())

    stale = [
        (u, v, k) for u, v, k, d in g_m.edges(keys=True, data=True)
        if d.get("kind") in DEF_ORDER_KINDS
        and (
            (d.get("witness") is not None and not g_m.has_node(d["witness"]))
            or not _defines(u, d.get("variable"))
            or not _defines(v, d.get("variable"))
        )
    ]
    g_m.remove_edges_from(stale)

    # ── record what the union decided ───────────────────────────────────────
    attribute_conflicts = [
        AttributeConflict(node=c, codes=tuple(pairs))
        for c, pairs in sorted(codes_seen.items())
        if len({code for _, code in pairs}) > 1
    ]
    # Edge additions: for every contributed vertex, canonical in-edges the
    # union has that the contributor's own graph lacks. Computed after the SDG
    # layer so interprocedural edges participate.
    in_gm = {
        v: {(s, d.get("kind"), d.get("variable")) for s, _, d in g_m.in_edges(v, data=True)}
        for v in g_m.nodes
    }
    edge_additions: list[EdgeAddition] = []
    for version, g, sliced, to_common in slices:
        for n in sorted(sliced):
            c = to_common(n)
            native_in = {
                (to_common(s), d.get("kind"), d.get("variable"))
                for s, _, d in g.in_edges(n, data=True)
            }
            foreign = in_gm[c] - native_in
            if foreign:
                edge_additions.append(
                    EdgeAddition(node=c, version=version, edges=frozenset(foreign))
                )

    return MergeResult(
        graph=g_m, ap_a=ap_a, ap_b=ap_b, preserved=pre, contributions=contributions,
        attribute_conflicts=attribute_conflicts, edge_additions=edge_additions,
    )


def preserved_points(
    base: nx.MultiDiGraph,
    ap_a: set[str],
    ap_b: set[str],
    map_a: dict[str, str],
    map_b: dict[str, str],
) -> set[str]:
    """Pre = Base vertices unchanged in *both* variants: those with a
    correspondent in each, neither of which is an affected point. A vertex
    either variant deleted is not preserved."""
    return {
        v
        for v in base.nodes
        if v in map_a
        and v in map_b
        and map_a[v] not in ap_a
        and map_b[v] not in ap_b
    }


# ── graph union in the common space ─────────────────────────────────────────
def _add_contribution(
    g_m: nx.MultiDiGraph,
    g: nx.MultiDiGraph,
    sliced: set[str],
    to_common,
    version: str,
    codes_seen: dict[str, list[tuple[str, str]]],
) -> None:
    # Sorted, not raw set order: iterating the set directly would make G_M's
    # insertion order depend on PYTHONHASHSEED, and tie-breaks that read
    # adjacency order would vary run to run.
    for n in sorted(sliced):
        c = to_common(n)
        codes_seen.setdefault(c, []).append((version, g.nodes[n].get("code") or ""))
        if g_m.has_node(c):
            g_m.nodes[c]["contributed_by"].add(version)
            g_m.nodes[c]["origin_ids"][version] = n
        else:
            data = dict(g.nodes[n])
            data["contributed_by"] = {version}
            data["origin_ids"] = {version: n}
            g_m.add_node(c, **data)

    # Induced edges: both endpoints inside the slice. Parallel edges are
    # identified by (kind, variable) — the same dependence contributed twice
    # merges into one edge with joint provenance rather than a duplicate.
    for src, dst, data in g.edges(sorted(sliced), data=True):
        if dst not in sliced:
            continue
        _merge_edge(g_m, to_common(src), to_common(dst), data, version, to_common)


def _add_sdg_layer(
    g_m: nx.MultiDiGraph,
    g: nx.MultiDiGraph,
    sliced: set[str],
    to_common,
    version: str,
) -> None:
    """Attach the edges no slice traverses: the SDG layer, output ordering and
    def-order. Two admission rules. Endpoint presence suffices for the SDG
    layer and for `OUT`, which must hold however the statements got there.
    Def-order follows HPR's induced-subgraph rule (§4.1.2): endpoints *and*
    witness must all be in this version's slice, or one version's ordering
    lands on statements another version owns."""
    for src, dst, data in g.edges(data=True):
        kind = data.get("kind")
        if kind not in SDG_KINDS + ORDER_KINDS + DEF_ORDER_KINDS:
            continue
        if kind in DEF_ORDER_KINDS:
            if src not in sliced or dst not in sliced:
                continue
            witness = data.get("witness")
            if witness is not None and witness not in sliced:
                continue
        c_src, c_dst = to_common(src), to_common(dst)
        if g_m.has_node(c_src) and g_m.has_node(c_dst):
            _merge_edge(g_m, c_src, c_dst, data, version, to_common)


def _merge_edge(
    g_m: nx.MultiDiGraph, c_src: str, c_dst: str, data: dict, version: str,
    to_common=lambda nid: nid,
) -> None:
    kind, var = data.get("kind"), data.get("variable")
    # The witness is part of an edge's identity: two definitions may be ordered
    # by several witnesses, each carrying its own def-order edge.
    # the witness names a vertex, so it lives in the common space like the
    # endpoints do — otherwise the §4.1.2 presence test below never matches
    raw_witness = data.get("witness")
    witness = to_common(raw_witness) if raw_witness is not None else None
    existing = g_m.get_edge_data(c_src, c_dst) or {}
    for edge_data in existing.values():
        if (edge_data.get("kind") == kind and edge_data.get("variable") == var
                and edge_data.get("witness") == witness):
            edge_data["contributed_by"].add(version)
            return
    merged = dict(data)
    merged["contributed_by"] = {version}
    if witness is not None:
        merged["witness"] = witness
    g_m.add_edge(c_src, c_dst, **merged)



# ── inspection ───────────────────────────────────────────────────────────────
def show(result: MergeResult, file: TextIO | None = None) -> None:
    """Print G_M: totals, per-version contributions, and the vertex listing."""
    out = file or sys.stdout
    g = result.graph
    print("\n=== Merged graph G_M ===", file=out)
    print(f"  vertices: {g.number_of_nodes()}   edges: {g.number_of_edges()}", file=out)
    for version in ("a", "b", "base"):
        ids = result.contributions.get(version, set())
        label = {"a": "G_A/AP_A", "b": "G_B/AP_B", "base": "G_Base/Pre"}[version]
        print(f"  {label:<10} contributed {len(ids)} vertices", file=out)
    print(f"  preserved points (Pre): {len(result.preserved)}", file=out)
    if result.attribute_conflicts:
        print(f"  attribute conflicts recorded: {len(result.attribute_conflicts)}", file=out)
        for ac in result.attribute_conflicts:
            texts = " | ".join(f"{v}: {c!r}" for v, c in ac.codes)
            print(f"    {ac.node}  {texts}", file=out)
    if result.edge_additions:
        print(f"  edge additions recorded (diagnostic): {len(result.edge_additions)}", file=out)

    by_method: dict[str, list[tuple[str, dict]]] = {}
    for nid, d in g.nodes(data=True):
        by_method.setdefault(d.get("method", "?"), []).append((nid, d))

    for method in sorted(by_method):
        print(f"\nmethod: {method}", file=out)
        for _, d in sorted(by_method[method], key=lambda item: _pos_key(item[1])):
            tag = "+".join(v for v in ("a", "b", "base") if v in d["contributed_by"])
            print(f"  {_fmt(d)}  [{tag}]", file=out)


def _fmt(d: dict) -> str:
    line = d.get("lineNumber")
    pos = f"L{line}:{d.get('columnNumber')}" if line is not None else "(synth)"
    code = (d.get("code") or "").strip().replace("\n", " ") or (d.get("name") or "")
    if len(code) > 38:
        code = code[:37] + "…"
    return f"{pos:>9}  {(d.get('label') or ''):<18}  {code!r}"


def _pos_key(d: dict) -> tuple:
    return (
        d.get("lineNumber") if d.get("lineNumber") is not None else -1,
        d.get("columnNumber") if d.get("columnNumber") is not None else -1,
        d.get("label") or "",
    )


# ── demonstration / smoke test ───────────────────────────────────────────────
def _toy(version: str, x_init: str = "x = 1", y_init: str = "y = 2") -> nx.MultiDiGraph:
    """Two independent def→use chains: x feeds print(x), y feeds print(y)."""
    g = nx.MultiDiGraph()
    p = f"{version}::m"
    for i, code in enumerate((x_init, y_init, "print(x)", "print(y)"), start=1):
        g.add_node(f"{p}::{i}", code=code, label="CALL", method="m", lineNumber=i, columnNumber=1)
    g.add_edge(f"{p}::1", f"{p}::3", kind="DDG", variable="x")
    g.add_edge(f"{p}::2", f"{p}::4", kind="DDG", variable="y")
    return g


def _demo() -> None:
    import correspondence
    from interference import type_0_from_ap
    from pdg import HERE, load_pdg

    # ── real triple: B == Base, so integration must reproduce A exactly.
    src = HERE.parent / "examples"
    base, a, b = load_pdg("base"), load_pdg("a"), load_pdg("b")
    map_a = correspondence.solve(base, a, base_src=src / "base.java", variant_src=src / "a.java")
    map_b = correspondence.solve(base, b, base_src=src / "base.java", variant_src=src / "b.java")

    result = merge_graphs(base, a, b, map_a, map_b)
    gate = type_0_from_ap(base, a, b, result.ap_a, result.ap_b, map_a, map_b)
    print("--- real triple (examples/{base,a,b}.java) ---")
    print(f"Type-0 pre-check: {'inconclusive' if gate.interferes else 'empty — proves non-interference'}")
    show(result)

    to_common_a = canonicalizer(map_a)
    assert set(result.graph.nodes) == {to_common_a(n) for n in a.nodes}
    assert result.graph.number_of_edges() == a.number_of_edges()
    print("\n  (assertion passed: with B unchanged, G_M is exactly G_A — "
          f"{result.graph.number_of_nodes()} vertices, {result.graph.number_of_edges()} edges)")

    # ── toy triple with two independent edits: G_M must contain BOTH changes,
    # even though Pre is empty — the changed slices already cover everything.
    tbase = _toy("base")
    ta = _toy("a", x_init="x = 5")   # A edits the x-initialisation
    tb = _toy("b", y_init="y = 7")   # B edits the y-initialisation
    tmap_a = {f"base::m::{i}": f"a::m::{i}" for i in (1, 2, 3, 4)}
    tmap_b = {f"base::m::{i}": f"b::m::{i}" for i in (1, 2, 3, 4)}

    tresult = merge_graphs(tbase, ta, tb, tmap_a, tmap_b)
    tgate = type_0_from_ap(tbase, ta, tb, tresult.ap_a, tresult.ap_b, tmap_a, tmap_b)
    print("\n--- toy triple (A edits x-init, B edits y-init — independent) ---")
    print(f"Type-0 pre-check: {'inconclusive' if tgate.interferes else 'empty — proves non-interference'}")
    show(tresult)

    merged_codes = [
        d["code"] for _, d in sorted(tresult.graph.nodes(data=True), key=lambda it: it[1]["lineNumber"])
    ]
    print("\n  merged program preview:", " ; ".join(merged_codes))
    assert merged_codes == ["x = 5", "y = 7", "print(x)", "print(y)"], merged_codes
    assert tresult.preserved == set()
    print("  (assertion passed: G_M integrates A's edit AND B's edit; Pre is empty)")


if __name__ == "__main__":
    _demo()
