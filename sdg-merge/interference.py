"""
Interference checks, in the papers' vocabulary (HRB 1995 §4.1.4).

Type I (`type_i_interference`) asks whether the union corrupted a variant's
changed behaviour; Type II (`feasibility.check`) whether `G_M` is feasible at
all. Type III is not implemented — a documented scope limitation, its shape
pinned in the corpus as `inter_type3`. `type_0_precheck` is ours, not the
papers': empty proves non-interference, non-empty decides nothing, and the
pipeline does not consult it.

Run directly for a self-checking demo on corpus fixtures:
    python3 interference.py
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from typing import TextIO

import networkx as nx

from affected import affected_points, affected_points_sdg, delta
from correspondence import canonicalizer
from slicer import backward_slice


@dataclass
class PrecheckResult:
    interferes: bool
    b_with_a: set[str] = field(default_factory=set)  # common-space witnesses
    a_with_b: set[str] = field(default_factory=set)
    ap_a: set[str] = field(default_factory=set)  # A-native node-ids
    ap_b: set[str] = field(default_factory=set)  # B-native node-ids


def type_0_precheck(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
    sdg: bool = False,
) -> PrecheckResult:
    """Compute affected points for both variants, then run the Type-0
    pre-check. Not a verdict: empty proves non-interference, non-empty is
    inconclusive. `sdg=True` runs the interprocedural form."""
    ap_fn = affected_points_sdg if sdg else affected_points
    ap_a = ap_fn(base, a, map_a)
    ap_b = ap_fn(base, b, map_b)
    return type_0_from_ap(base, a, b, ap_a, ap_b, map_a, map_b, sdg=sdg)


def type_0_from_ap(
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    ap_a: set[str],
    ap_b: set[str],
    map_a: dict[str, str],
    map_b: dict[str, str],
    sdg: bool = False,
    slice_a: set[str] | None = None,
    slice_b: set[str] | None = None,
) -> PrecheckResult:
    """Type-0 pre-check from pre-computed affected points, avoiding a
    re-slice. A caller already holding the Δ slices passes them as
    `slice_a`/`slice_b`."""
    to_base_a = canonicalizer(map_a)
    to_base_b = canonicalizer(map_b)

    if slice_a is None:
        slice_a = delta(base, a, map_a) if sdg else backward_slice(a, ap_a)
    if slice_b is None:
        slice_b = delta(base, b, map_b) if sdg else backward_slice(b, ap_b)

    # B interferes with A: something B changed lies in A's changed-behaviour cone.
    b_with_a = {to_base_a(n) for n in slice_a} & {to_base_b(n) for n in ap_b}
    # A interferes with B: the symmetric direction.
    a_with_b = {to_base_b(n) for n in slice_b} & {to_base_a(n) for n in ap_a}

    return PrecheckResult(
        interferes=bool(b_with_a or a_with_b),
        b_with_a=b_with_a,
        a_with_b=a_with_b,
        ap_a=ap_a,
        ap_b=ap_b,
    )


# ── Type-I interference (the papers' test) ───────────────────────────────────
@dataclass
class TypeIResult:
    interferes: bool
    a_damaged: set[str] = field(default_factory=set)   # common-space witnesses
    b_damaged: set[str] = field(default_factory=set)
    pre_damaged: set[str] = field(default_factory=set)


def type_i_interference(
    merged,  # merge.MergeResult (duck-typed to avoid a module cycle)
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
    sdg: bool = False,
) -> TypeIResult:
    """HPR's definitive post-construction interference test, in its AP form:

        AP(G_M, A)    ∩ AP(A, Base) = ∅     A's changed behaviour is in G_M
        AP(G_M, B)    ∩ AP(B, Base) = ∅     B's changed behaviour is in G_M
        AP(G_M, Base) ∩ Pre         = ∅     Base's preserved behaviour is kept

    Reuses `affected_points` with G_M as the variant and each contributor as
    the base, so all three conditions stay linear."""
    g_m = merged.graph
    to_a, to_b = canonicalizer(map_a), canonicalizer(map_b)

    # Contributor → G_M correspondences: a contributor vertex maps to its
    # common-space id whenever G_M actually contains that vertex.
    map_a_m = {n: to_a(n) for n in a.nodes if g_m.has_node(to_a(n))}
    map_b_m = {n: to_b(n) for n in b.nodes if g_m.has_node(to_b(n))}
    map_base_m = {n: n for n in base.nodes if g_m.has_node(n)}

    ap_fn = affected_points_sdg if sdg else affected_points
    a_damaged = ap_fn(a, g_m, map_a_m) & {to_a(n) for n in merged.ap_a}
    b_damaged = ap_fn(b, g_m, map_b_m) & {to_b(n) for n in merged.ap_b}
    pre_damaged = ap_fn(base, g_m, map_base_m) & merged.preserved

    return TypeIResult(
        interferes=bool(a_damaged or b_damaged or pre_damaged),
        a_damaged=a_damaged,
        b_damaged=b_damaged,
        pre_damaged=pre_damaged,
    )


def show_type_i(
    result: TypeIResult,
    base: nx.MultiDiGraph | None = None,
    a: nx.MultiDiGraph | None = None,
    b: nx.MultiDiGraph | None = None,
    g_m: nx.MultiDiGraph | None = None,
    file: TextIO | None = None,
) -> None:
    """Print the three preservation conditions and, on failure, the witnesses."""
    out = file or sys.stdout
    print("\n=== Type-I interference (post-construction, HPR §4.4 / HRB §4.1.4) ===", file=out)
    conditions = (
        ("A's changed behaviour preserved", "AP(G_M, A) ∩ AP(A, Base)", result.a_damaged),
        ("B's changed behaviour preserved", "AP(G_M, B) ∩ AP(B, Base)", result.b_damaged),
        ("Base's preserved behaviour kept", "AP(G_M, Base) ∩ Pre", result.pre_damaged),
    )
    for label, formula, witnesses in conditions:
        if not witnesses:
            print(f"  {label}:  yes  ({formula} = ∅)", file=out)
        else:
            print(f"  {label}:  NO   ({len(witnesses)} damaged point(s))", file=out)
            for nid in sorted(witnesses, key=lambda n: _sort_key(n, g_m, base, a, b)):
                print(f"      {_describe(nid, g_m, base, a, b)}", file=out)
    if result.interferes:
        print("  VERDICT: TYPE-I INTERFERENCE — G_M does not preserve the versions' behaviour", file=out)
    else:
        print("  VERDICT: G_M preserves all three behaviours — integration sound", file=out)


# ── inspection ───────────────────────────────────────────────────────────────
def show_precheck(
    result: PrecheckResult,
    base: nx.MultiDiGraph | None = None,
    a: nx.MultiDiGraph | None = None,
    b: nx.MultiDiGraph | None = None,
    file: TextIO | None = None,
) -> None:
    """Print the verdict and, when interfering, the conflicting vertices."""
    out = file or sys.stdout
    print("\n=== Type-0 pre-check (ours; empty proves non-interference, non-empty is inconclusive) ===", file=out)
    print(
        f"  AP_A = {len(result.ap_a)} affected points, "
        f"AP_B = {len(result.ap_b)} affected points",
        file=out,
    )
    _direction(out, "B interferes with A", "slice_A(AP_A) ∩ AP_B", result.b_with_a, base, a, b)
    _direction(out, "A interferes with B", "slice_B(AP_B) ∩ AP_A", result.a_with_b, base, a, b)

    if result.interferes:
        print("  pre-check: INCONCLUSIVE — Type-I decides", file=out)
    else:
        print("  pre-check: EMPTY — proves no Type-I interference", file=out)


def _direction(out, label, formula, witnesses, base, a, b) -> None:
    if not witnesses:
        print(f"  {label}:  no   ({formula} = ∅)", file=out)
        return
    print(f"  {label}:  YES  ({len(witnesses)} conflicting point(s))", file=out)
    for nid in sorted(witnesses, key=lambda n: _sort_key(n, base, a, b)):
        print(f"      {_describe(nid, base, a, b)}", file=out)


def _describe(nid: str, *graphs: nx.MultiDiGraph | None) -> str:
    d = _lookup(nid, *graphs)
    if d is None:
        return f"(unresolved) {nid}"
    line = d.get("lineNumber")
    pos = f"L{line}:{d.get('columnNumber')}" if line is not None else "(synth)"
    code = (d.get("code") or "").strip() or d.get("name") or d.get("label") or nid
    return f"{pos:>9}  {code!r}"


def _sort_key(nid: str, *graphs: nx.MultiDiGraph | None) -> tuple:
    d = _lookup(nid, *graphs) or {}
    return (
        d.get("lineNumber") if d.get("lineNumber") is not None else -1,
        d.get("columnNumber") if d.get("columnNumber") is not None else -1,
    )


def _lookup(nid: str, *graphs: nx.MultiDiGraph | None) -> dict | None:
    for g in graphs:
        if g is not None and g.has_node(nid):
            return g.nodes[nid]
    return None


# ── demonstration / smoke test ───────────────────────────────────────────────
def _toy(version: str, increment: str, init: str = "int b = 2") -> nx.MultiDiGraph:
    """A 3-vertex PDG `init; b = b + k; print(b)` in one method, DDG-chained."""
    g = nx.MultiDiGraph()
    p = f"{version}::m"
    g.add_node(f"{p}::1", code=init, label="CALL", method="m")
    g.add_node(f"{p}::2", code=increment, label="CALL", method="m")
    g.add_node(f"{p}::3", code="print(b)", label="CALL", method="m")
    g.add_edge(f"{p}::1", f"{p}::2", kind="DDG", variable="b")
    g.add_edge(f"{p}::2", f"{p}::3", kind="DDG", variable="b")
    return g


def _demo() -> None:
    import correspondence
    from pdg import HERE, load_pdg

    # ── real triple: A edits b and adds an if-block; B == Base ⇒ non-interfering.
    src = HERE.parent / "examples"
    base = load_pdg("base")
    a = load_pdg("a")
    b = load_pdg("b")
    map_a = correspondence.solve(base, a, base_src=src / "base.java", variant_src=src / "a.java")
    map_b = correspondence.solve(base, b, base_src=src / "base.java", variant_src=src / "b.java")
    print("--- real triple (examples/{base,a,b}.java) ---")
    t1 = type_0_precheck(base, a, b, map_a, map_b)
    show_precheck(t1, base, a, b)

    # Pre-check empty ⇒ construct G_M and confirm with the definitive Type-I test.
    from merge import merge_from_ap  # local import: merge's demo imports us back

    merged = merge_from_ap(base, a, b, t1.ap_a, t1.ap_b, map_a, map_b)
    t1 = type_i_interference(merged, base, a, b, map_a, map_b)
    show_type_i(t1, base, a, b, merged.graph)
    assert not t1.interferes, "real triple must pass Type-I"
    print("\n  (assertion passed: G_M preserves A's, B's and Base's behaviour)")

    # ── synthetic triple: A changes the increment, B changes the initialiser —
    # both touch b's value, so they must interfere. Exercises the positive
    # branch the real triple cannot (its AP_B is empty).
    tbase = _toy("base", "b = b + 1")
    ta = _toy("a", "b = b + 5")                 # A: b = b + 1 → b = b + 5
    tb = _toy("b", "b = b + 1", init="int b = 3")  # B: int b = 2 → int b = 3
    tmap_a = {f"base::m::{i}": f"a::m::{i}" for i in (1, 2, 3)}
    tmap_b = {f"base::m::{i}": f"b::m::{i}" for i in (1, 2, 3)}
    print("\n--- synthetic interfering triple (A edits increment, B edits init) ---")
    result = type_0_precheck(tbase, ta, tb, tmap_a, tmap_b)
    show_precheck(result, tbase, ta, tb)
    assert result.interferes, "synthetic triple must interfere"
    print("\n  (assertion passed: interference correctly detected)")

    # ── force the merge despite the Type-I verdict: the union resolves the
    # attribute conflict by priority (A > B), silently dropping B's init edit —
    # exactly the damage the post-construction Type-I test must catch.
    from merge import merge_from_ap

    forced = merge_from_ap(tbase, ta, tb, result.ap_a, result.ap_b, tmap_a, tmap_b)
    print("\n--- forcing the merge of the interfering triple (Type-I must catch it) ---")
    t1f = type_i_interference(forced, tbase, ta, tb, tmap_a, tmap_b)
    show_type_i(t1f, tbase, ta, tb, forced.graph)
    assert t1f.interferes, "forced merge must fail Type-I"
    print("\n  (assertion passed: Type-I detected the damaged behaviour)")


if __name__ == "__main__":
    _demo()
