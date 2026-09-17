"""
Affected-points computation.

An affected point of a variant is a vertex whose backward slice differs from
its Base counterpart's. Computed by HPR's linear technique rather than by
slicing at every vertex: seed with the new, edited and rewired vertices, then
take the forward closure over DDG ∪ CDG.

Run directly for a self-checking demo on corpus fixtures:
    python3 affected.py
"""

from __future__ import annotations

import sys
from typing import TextIO

import networkx as nx

from slicer import (
    B1_KINDS,
    B2_KINDS,
    backward_slice,
    backward_slice_sdg,
    forward_slice,
    forward_slice_sdg,
)


def affected_points(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> set[str]:
    """Affected points of `variant` w.r.t. `base`, as variant node-ids."""
    return forward_slice(variant, set(_seeds(base, variant, mapping)))


# ── interprocedural affected points (HRB '95) ───────────────────────────────
def directly_affected(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> set[str]:
    """DAP — the directly affected points: the seed set itself (new, edited
    or rewired, where rewiring also counts SDG in-edges)."""
    return set(_seeds(base, variant, mapping))


def strongly_affected(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> set[str]:
    """SAP = f1(DAP): the points affected in *every* calling context."""
    return forward_slice(variant, directly_affected(base, variant, mapping),
                         edge_kinds=B2_KINDS)


def affected_points_sdg(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> set[str]:
    """All affected points, strongly ∪ weakly: `f2(f1(DAP))`. Vertices reached
    only by f2 are *weakly* affected — changed in some contexts, not all."""
    return forward_slice_sdg(variant, directly_affected(base, variant, mapping))


def affected_sets(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> tuple[set[str], set[str], set[str]]:
    """The f-chain computed once: (DAP, SAP = f1(DAP), AP = f2(SAP)).
    Sharing the chain is HRB's own prescription (BHR 1995 p. 33), not a
    local optimisation; everything interprocedural downstream builds on it."""
    dap = directly_affected(base, variant, mapping)
    sap = forward_slice(variant, dap, edge_kinds=B2_KINDS)   # f1: escape via formal-outs
    ap = forward_slice(variant, sap, edge_kinds=B1_KINDS)    # f2: descend into callees
    return dap, sap, ap


def delta_from_ap(
    variant: nx.MultiDiGraph,
    sap: set[str],
    ap: set[str],
) -> set[str]:
    """Δ from pre-computed SAP and AP, fused as `b2(b1(SAP) ∪ AP)`. The
    fusion is HRB's (BHR 1995 p. 33): strongly affected points take the full
    two-pass backward slice, weakly affected ones only the descending pass."""
    return backward_slice(
        variant,
        backward_slice(variant, sap, edge_kinds=B1_KINDS) | set(ap),
        edge_kinds=B2_KINDS,
    )


def delta(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> set[str]:
    """Δ(V, Base) — BHR 1995 p. 33, via the shared f-chain and the fused
    backward pass. Feeds the merged-graph construction."""
    _dap, sap, ap = affected_sets(base, variant, mapping)
    return delta_from_ap(variant, sap, ap)


def _seeds(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> dict[str, str]:
    """HPR's seed set D, with the reason each vertex qualifies."""
    base_of = {var_id: base_id for base_id, var_id in mapping.items()}
    seeds: dict[str, str] = {}
    for v, d in variant.nodes(data=True):
        b = base_of.get(v)
        if b is None:
            seeds[v] = "new"
        elif _code(d) != _code(base.nodes[b]):
            seeds[v] = "edited"
        elif _in_triples(variant, v, base_of) != _in_triples(base, b, None):
            seeds[v] = "rewired"
    return seeds


def _in_triples(
    g: nx.MultiDiGraph, node: str, to_base: dict[str, str] | None
) -> set[tuple]:
    """Incoming dependence edges of `node` as (src, kind, variable) triples,
    with sources folded through the correspondence so both sides compare in
    Base ids."""
    out = set()
    for src, _, data in g.in_edges(node, data=True):
        c_src = to_base.get(src, src) if to_base is not None else src
        out.add((c_src, data.get("kind"), data.get("variable")))
    return out


def _code(d: dict) -> str:
    code = d.get("code")
    if code is not None and code.strip():
        return code.strip()
    # Synthetic vertices (METHOD_RETURN's "RET", parameters) carry stable code
    # already, but fall back to name/label so a missing `code` still compares
    # as something rather than collapsing every such vertex to "".
    return d.get("name") or d.get("label") or ""


# ── inspection ───────────────────────────────────────────────────────────────
def show(
    variant: nx.MultiDiGraph,
    ap: set[str],
    mapping: dict[str, str] | None = None,
    base: nx.MultiDiGraph | None = None,
    title: str = "affected points",
    file: TextIO | None = None,
) -> None:
    """Print the affected points, grouped by method and sorted by position."""
    out = file or sys.stdout
    reasons = _seeds(base, variant, mapping) if base is not None and mapping is not None else {}

    print(f"\n=== {title}: {len(ap)} affected ===", file=out)

    by_method: dict[str, list[str]] = {}
    for v in ap:
        by_method.setdefault(variant.nodes[v].get("method", "?"), []).append(v)

    for method in sorted(by_method):
        print(f"\nmethod: {method}", file=out)
        for v in sorted(by_method[method], key=lambda n: _pos_key(variant.nodes[n])):
            tag = f"  [{reasons.get(v, 'downstream')}]" if reasons or mapping else ""
            print(f"  {_fmt(variant.nodes[v])}{tag}", file=out)


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
def _demo() -> None:
    import correspondence
    from pdg import HERE, load_pdg

    src = HERE.parent / "examples"
    base = load_pdg("base")
    for v in ("a", "b"):
        variant = load_pdg(v)
        mapping = correspondence.solve(
            base, variant,
            base_src=src / "base.java",
            variant_src=src / f"{v}.java",
        )
        ap = affected_points(base, variant, mapping)
        show(variant, ap, mapping=mapping, base=base,
             title=f"AP_{v.upper()}  (variant {v} vs base)")

    # ── interprocedural APs: the un-blinding measurement ─────────────────────
    from correspondence import canonicalizer
    from pdg import load_pdg_file

    corpus = HERE.parent / "examples" / "corpus"

    def common_aps(fixture: str, fn):
        d = corpus / fixture
        g = {v: load_pdg_file(d / "pdg_json" / f"{v}.json") for v in ("base", "a", "b")}
        out = []
        for v in ("a", "b"):
            m = correspondence.solve(g["base"], g[v],
                                     base_src=d / "base.java", variant_src=d / f"{v}.java")
            to_c = canonicalizer(m)
            out.append({to_c(n) for n in fn(g["base"], g[v], m)})
        return out

    print("\n=== interprocedural affected points (SAP/weak) ===")
    # intra_overlap: measured expectation for the *hybrid* intra AP — the
    # seed rule already sees SDG in-edge changes (an added call
    # rewires the callee's entry), but only the two-pass closures propagate
    # a change through a call whose fan-in did NOT change (inter_param_flow).
    for fixture, intra_overlap, sdg_overlap in (
        ("inter_callee_edit", True, True),    # B's new call rewires the callee → even seeds see it
        ("inter_param_flow", False, True),    # closures required: fan-in unchanged on both sides
        ("inter_independent", False, False),  # disjoint callees — must stay clean
    ):
        intra_a, intra_b = common_aps(fixture, affected_points)
        sdg_a, sdg_b = common_aps(fixture, affected_points_sdg)
        print(f"  {fixture}: intra AP∩AP = {len(intra_a & intra_b)},  "
              f"SDG AP∩AP = {len(sdg_a & sdg_b)}  "
              f"(|AP_A| {len(intra_a)}→{len(sdg_a)}, |AP_B| {len(intra_b)}→{len(sdg_b)})")
        assert bool(intra_a & intra_b) == intra_overlap, f"{fixture}: intra"
        assert bool(sdg_a & sdg_b) == sdg_overlap, f"{fixture}: sdg"
    print("  (assertions passed: SDG APs overlap exactly where the conflict"
          " flows through a call — inter_param_flow shows the closures are"
          " what completes the un-blinding)")


if __name__ == "__main__":
    _demo()
