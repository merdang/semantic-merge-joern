"""
Vertex correspondence between PDG versions.

For each Base vertex, which vertex in a variant it corresponds to. GumTree
matches the two sources, the character ranges become (line, column), and each
Base vertex is looked up in the variant by (method, label, position). Vertices
GumTree did not match may map by identity, and synthetic vertices without
positions map structurally. The mapping is injective by construction.

Without GumTree the solver falls back to position-only matching: correct for
unchanged methods, conservatively unmapped for edits.

Run directly for a self-checking demo on corpus fixtures:
    python3 correspondence.py
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import TextIO

import networkx as nx

from gumtree import (
    GumTreeError,
    GumTreeNotFound,
    diff_matches,
)
from positions import LineIndex
import reconstitute


def solve(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    base_src: Path | None = None,
    variant_src: Path | None = None,
) -> dict[str, str]:
    """`{base_node_id: variant_node_id}` for corresponding vertices, AST-driven
    when GumTree is available and position-only otherwise."""
    if base_src is not None and variant_src is not None:
        try:
            return _gumtree_solve(base, variant, base_src, variant_src)
        except (GumTreeNotFound, GumTreeError, FileNotFoundError) as e:
            print(f"[correspondence] GumTree path unavailable ({e}); using baseline.")
    return _structural_solve(base, variant)


# ── GumTree-driven path ──────────────────────────────────────────────────────
def _gumtree_solve(
    base_g: nx.MultiDiGraph,
    variant_g: nx.MultiDiGraph,
    base_src: Path,
    variant_src: Path,
) -> dict[str, str]:
    base_idx = LineIndex(base_src.read_text())
    var_idx = LineIndex(variant_src.read_text())

    # base (line, col) of matched AST node → variant (line, col)
    pos_map: dict[tuple[int, int], tuple[int, int]] = {}
    for (src_start, _), (dst_start, _) in diff_matches(base_src, variant_src):
        pos_map[base_idx.locate(src_start)] = var_idx.locate(dst_start)

    var_lookup = _by_position(variant_g)

    # Sub-expression → enclosing statement, computed inside each version's own
    # frame (the rule bans span comparison *across* frames, not within one).
    base_host, var_host = _hosts(base_g), _hosts(variant_g)
    var_children: dict[str, list[str]] = {}
    for child, host in var_host.items():
        var_children.setdefault(host, []).append(child)
    for kids in var_children.values():
        kids.sort()

    # Two phases: an *explicit* claim projects a position GumTree matched, an
    # *identity* claim only assumes the vertex never moved. Identity is wrong
    # where a vertex was deleted and another moved into its slot, so it must
    # find the same text and may not claim a vertex an explicit match owns.
    # A dropped claim leaves the base vertex unmapped, degrading to HRB's
    # delete + add rather than corrupting the common space.
    explicit: list[tuple[str, dict, list[str]]] = []
    identity: list[tuple[str, dict, list[str]]] = []
    for nid, d in base_g.nodes(data=True):
        line = d.get("lineNumber")
        col = d.get("columnNumber")
        if line is None or col is None:
            continue
        dst_lc = pos_map.get((line, col))
        key = (d.get("method"), d.get("label"), *(dst_lc or (line, col)),
               d.get("name") or "")
        candidates = var_lookup.get(key)
        if not candidates:
            continue
        (explicit if dst_lc is not None else identity).append((nid, d, candidates))

    mapping: dict[str, str] = {}
    claimed: set[str] = set()
    for phase, entries in (("explicit", explicit), ("identity", identity)):
        # Statements before their own sub-expressions, so a child's claim can
        # be checked against the claim its parent already made.
        for tier in (False, True):
            for nid, d, candidates in entries:
                if (nid in base_host) is not tier:
                    continue
                var_nid = _pick(candidates, d, variant_g, claimed)
                host_claim = mapping.get(base_host.get(nid, ""))
                hosted = host_claim is not None and (
                    var_nid is not None and var_host.get(var_nid) == host_claim
                )
                if host_claim is not None and not hosted:
                    # The claim contradicts the parent statement's: GumTree
                    # matched this sub-expression into a *different* statement
                    # Structure outranks it — re-home the claim inside
                    # the host the parent actually matched.
                    var_nid = _rehome(d, host_claim, var_children, variant_g, claimed)
                    hosted = var_nid is not None
                if var_nid is None:
                    continue
                # An identity claim is a guess and must find the same text —
                # unless the parent statement's own claim already places this
                # sub-expression, which is stronger evidence than text and is
                # what lets an *edited* operand stay corresponded instead of
                # degrading to delete + add. The identity geometry above is
                # untouched: the vertices it concerns are statements, which
                # have no host.
                if (phase == "identity" and not hosted
                        and not _same_text(d, variant_g.nodes[var_nid])):
                    continue
                mapping[nid] = var_nid
                claimed.add(var_nid)

    _map_synthetic(base_g, variant_g, mapping)
    return mapping



def _hosts(g: nx.MultiDiGraph) -> dict[str, str]:
    """Sub-expression vertex → the outermost statement whose span encloses it,
    computed within one version's own frame. Positions may never be compared
    across versions; `feasibility._span_host` does this job on `G_M`."""
    nodes = [(n, d) for n, d in g.nodes(data=True) if _position_key(d) is not None]
    tightest: dict[str, str] = {}
    for n, d in nodes:
        best: str | None = None
        best_key: tuple | None = None
        for m, md in nodes:
            if m == n or md.get("method") != d.get("method"):
                continue
            if not reconstitute.subsumes(md, d):
                continue
            key = (len(_code(md)), m)
            if best_key is None or key < best_key:
                best, best_key = m, key
        if best is not None:
            tightest[n] = best

    def outermost(n: str) -> str:
        seen = {n}
        while n in tightest and tightest[n] not in seen:
            n = tightest[n]
            seen.add(n)
        return n

    return {n: outermost(n) for n in tightest}


def _rehome(
    base_d: dict,
    host_claim: str,
    var_children: dict[str, list[str]],
    variant: nx.MultiDiGraph,
    claimed: set[str],
) -> str | None:
    """Re-place a host-inconsistent claim inside the host its parent matched.

    GumTree matches subtrees, so two identical sub-expressions in different
    statements are one subtree to it and a child can be claimed into the wrong
    statement. A sub-expression of a matched statement belongs to that
    statement's counterpart; `label`/`name` picks which child."""
    free = [n for n in var_children.get(host_claim, []) if n not in claimed]
    same_kind = [
        n for n in free
        if variant.nodes[n].get("label") == base_d.get("label")
        and (variant.nodes[n].get("name") or "") == (base_d.get("name") or "")
    ]
    if not same_kind:
        return None
    if len(same_kind) == 1:
        return same_kind[0]
    return _pick(same_kind, base_d, variant, claimed)


def _same_text(a: dict, b: dict) -> bool:
    """Statement text equality — the admissibility test for an identity claim.

    Comparing *text* across versions is sound (it is what the "edited" seed in
    `affected._seeds` does); comparing *positions* across versions is the thing
    nothing may do. An in-place rewrite radical enough that GumTree reports no
    match now degrades to delete + add rather than pairing two unrelated
    statements — the conservative direction.
    """
    return ((a.get("code") or "").strip()) == ((b.get("code") or "").strip())


# ── structural fallback ──────────────────────────────────────────────────────
def _structural_solve(
    base: nx.MultiDiGraph, variant: nx.MultiDiGraph
) -> dict[str, str]:
    var_lookup = _by_position(variant)
    mapping: dict[str, str] = {}
    claimed: set[str] = set()
    for nid, d in base.nodes(data=True):
        key = _position_key(d)
        var_nid = _pick(var_lookup.get(key, []), d, variant, claimed) if key else None
        if var_nid is not None:
            mapping[nid] = var_nid
            claimed.add(var_nid)
    _map_synthetic(base, variant, mapping)
    return mapping


# ── shared helpers ───────────────────────────────────────────────────────────
def _by_position(g: nx.MultiDiGraph) -> dict[tuple, list[str]]:
    """Position key → *every* vertex holding it, sorted for determinism.

    The key is not always unique: nested sub-expressions of one operator share
    line, column, label and `name`, and Joern gives these CALLs no
    `columnNumberEnd` to separate them. Collisions are kept and resolved by
    `_pick`.
    """
    out: dict[tuple, list[str]] = {}
    for nid, d in g.nodes(data=True):
        key = _position_key(d)
        if key is not None:
            out.setdefault(key, []).append(nid)
    for nids in out.values():
        nids.sort()
    return out


def _pick(
    candidates: list[str],
    base_d: dict,
    variant: nx.MultiDiGraph,
    claimed: set[str],
) -> str | None:
    """Which of several vertices sharing one position key this base vertex is.
    An exact `code` match wins; otherwise closest code length, since among
    expressions sharing a start column the outer one is longer. Ties break on
    id, so the result never depends on iteration order."""
    free = [n for n in candidates if n not in claimed]
    if not free:
        return None
    if len(free) == 1:
        return free[0]
    want = _code(base_d)
    exact = [n for n in free if _code(variant.nodes[n]) == want]
    if exact:
        return exact[0]
    return min(free, key=lambda n: (abs(len(_code(variant.nodes[n])) - len(want)), n))


def _code(d: dict) -> str:
    return (d.get("code") or "").strip()


def _position_key(d: dict) -> tuple | None:
    line = d.get("lineNumber")
    col = d.get("columnNumber")
    if line is None or col is None:
        return None
    # `name` disambiguates sibling CALL vertices sharing a (line, col), and
    # falls back to "" so vertices without one still hash.
    return (d.get("method"), d.get("label"), line, col, d.get("name") or "")


def _map_synthetic(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
) -> None:
    """Map nodes lacking source positions by (method, label, name).

    METHOD, METHOD_RETURN and parameters are emitted with stable identities
    that survive body edits, so a pure structural match is correct as long as
    the method signature is unchanged.
    """
    synthetic: dict[tuple, str] = {}
    for nid, d in variant.nodes(data=True):
        if d.get("lineNumber") is not None and d.get("columnNumber") is not None:
            continue
        key = (d.get("method"), d.get("label"), d.get("name"))
        synthetic.setdefault(key, nid)

    for nid, d in base.nodes(data=True):
        if nid in mapping:
            continue
        if d.get("lineNumber") is not None and d.get("columnNumber") is not None:
            continue
        key = (d.get("method"), d.get("label"), d.get("name"))
        match = synthetic.get(key)
        if match is not None:
            mapping[nid] = match


# ── common-space canonicalization ────────────────────────────────────────────
def canonicalizer(base_to_variant: dict[str, str]):
    """`f(variant_id) -> common-space id` for cross-version set algebra.

    The common space uses Base node-ids, so the same statement in A and B
    collapses onto one id while new code keeps its version-prefixed id and can
    never collide across versions.

    Relies on the correspondence being injective — which `solve` *enforces*:
    explicit GumTree claims resolve before identity guesses, and a
    second claim on an already-claimed variant vertex is dropped as
    delete + add. Enforcement matters here: `setdefault` deduplicates
    lookup keys within one graph, which never stopped two base vertices from
    claiming one variant vertex — and inverting the non-injective map here
    silently dropped an entry.
    """
    variant_to_base = {var_id: base_id for base_id, var_id in base_to_variant.items()}
    return lambda nid: variant_to_base.get(nid, nid)


# ── inspection ───────────────────────────────────────────────────────────────
def show(
    base: nx.MultiDiGraph,
    variant: nx.MultiDiGraph,
    mapping: dict[str, str],
    title: str = "base → variant",
    file: TextIO | None = None,
) -> None:
    """Print a side-by-side view of the correspondence, grouped by method.
    A `*moved*` marker means the vertex changed position between versions."""
    out = file or sys.stdout
    total = base.number_of_nodes()
    mapped = sum(1 for nid in base.nodes if nid in mapping)
    print(
        f"\n=== {title}: {mapped}/{total} mapped, {total - mapped} unmapped ===",
        file=out,
    )

    by_method: dict[str, list[tuple[str, dict]]] = {}
    for nid, d in base.nodes(data=True):
        by_method.setdefault(d.get("method", "?"), []).append((nid, d))

    for method in sorted(by_method):
        print(f"\nmethod: {method}", file=out)
        for nid, d in sorted(by_method[method], key=_show_sort_key):
            mapped_id = mapping.get(nid)
            left = _format_vertex(d)
            if mapped_id is None:
                right = "── unmapped ──"
                marker = ""
            else:
                vd = variant.nodes[mapped_id]
                right = _format_vertex(vd)
                marker = "  *moved*" if _shifted(d, vd) else ""
            print(f"  {left}   →   {right}{marker}", file=out)


def _format_vertex(d: dict) -> str:
    line = d.get("lineNumber")
    col = d.get("columnNumber")
    pos = f"L{line}:{col}" if line is not None else "(synth)"
    label = (d.get("label") or "")[:20].ljust(20)
    code = (d.get("code") or "").strip().replace("\n", " ") or (d.get("name") or "")
    if len(code) > 30:
        code = code[:29] + "…"
    return f"{pos:>9}  {label}  {code!r}"


def _show_sort_key(item: tuple[str, dict]) -> tuple:
    _, d = item
    return (
        d.get("lineNumber") if d.get("lineNumber") is not None else -1,
        d.get("columnNumber") if d.get("columnNumber") is not None else -1,
        d.get("label") or "",
    )


def _shifted(base_d: dict, var_d: dict) -> bool:
    bl, bc = base_d.get("lineNumber"), base_d.get("columnNumber")
    vl, vc = var_d.get("lineNumber"), var_d.get("columnNumber")
    if bl is None or vl is None:
        return False
    return (bl, bc) != (vl, vc)


# ── demonstration / smoke test ───────────────────────────────────────────────
def _demo() -> None:
    """Step-17 verification: correspondence across multi-method files.

    No method-specific machinery is needed beyond what the keys already
    encode: the positional lookup key and the synthetic key both carry the
    method fullName, so vertices can only match within their own method, and
    GumTree diffs whole files however many methods they hold. A renamed
    method changes its fullName, so its vertices deliberately fail to match —
    HRB's model treats a rename as delete + add; likewise a call vertex that
    now targets the renamed callee carries a new `name` and counts as new.
    """
    from pdg import load_pdg_file

    corpus = Path(__file__).resolve().parent.parent / "examples" / "corpus"

    def load(fixture: str):
        d = corpus / fixture
        graphs = {v: load_pdg_file(d / "pdg_json" / f"{v}.json") for v in ("base", "a", "b")}
        maps = {
            v: solve(graphs["base"], graphs[v],
                     base_src=d / "base.java", variant_src=d / f"{v}.java")
            for v in ("a", "b")
        }
        return graphs, maps

    # inter_callee_edit: a body edit in twice(), new statements in main() —
    # every Base vertex must correspond in both variants, method-locally.
    graphs, maps = load("inter_callee_edit")
    base = graphs["base"]
    for v in ("a", "b"):
        per_method: dict[str, list[int]] = {}
        for nid, d in base.nodes(data=True):
            got, tot = per_method.setdefault(d["method"], [0, 0])
            per_method[d["method"]] = [got + (nid in maps[v]), tot + 1]
        summary = "  ".join(f"{m.split(':')[0]}: {g}/{t}" for m, (g, t) in sorted(per_method.items()))
        print(f"inter_callee_edit base→{v}:  {summary}")
        assert len(maps[v]) == base.number_of_nodes(), f"base→{v} must map every vertex"

    # inter_rename_callee: A renames twice() → triple(). The renamed method's
    # vertices must not correspond; the caller's vertices all must — except
    # the call vertex itself, which now targets a different callee.
    graphs, maps = load("inter_rename_callee")
    base = graphs["base"]
    twice = {n for n, d in base.nodes(data=True) if ".twice:" in d["method"]}
    main_ = {n for n, d in base.nodes(data=True) if ".main:" in d["method"]}
    mapped = set(maps["a"])
    unmapped_main = {n for n in main_ - mapped}
    assert not (twice & mapped), "renamed method's vertices must not correspond"
    assert all(base.nodes[n].get("name") == "twice" for n in unmapped_main), \
        "in the caller, only the retargeted call vertex may be unmapped"
    print(f"inter_rename_callee base→a:  main {len(main_ & mapped)}/{len(main_)} "
          f"(unmapped: the retargeted call), twice {len(twice & mapped)}/{len(twice)} "
          f"(rename = delete + add)")
    print("\n(assertions passed: method-local matching, rename semantics)")


if __name__ == "__main__":
    _demo()
