"""
Conflict report — the user-facing outcome of the merge.

Type-I's damaged sets are the authoritative witnesses; this module resolves
each into something readable: method → file position → the statement in Base,
A and B → why it is damaged → a dependence chain from the opposing edit that
reaches it. The "why" joins `MergeResult.attribute_conflicts` with
`MergeResult.edge_additions`; a witness with neither is downstream damage.

CLI:
    python3 report.py                  # root triple (examples/{base,a,b}.java)
    python3 report.py <fixture>        # one corpus fixture by name
    python3 report.py --selftest       # compare against committed golden reports
    python3 report.py --bless <f> …    # (re)generate golden expected_report.txt
Exit status: 0 = clean merge, 1 = a refused merge (either check) or a failing
selftest.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from pathlib import Path

import networkx as nx

import affected
import correspondence
import feasibility
import interference
import merge
from correspondence import canonicalizer
from pdg import HERE, load_pdg_file

CORPUS = HERE.parent / "examples" / "corpus"
GOLDEN_FIXTURES = ("hidden_dataflow", "same_stmt_diff_edit", "inter_rename_callee",
                   "unorderable_defs")


# ── witness resolution ───────────────────────────────────────────────────────
@dataclass
class Witness:
    node: str                      # common-space id
    method: str
    line: int | None
    col: int | None
    code: str                      # the union's stored text
    versions: dict[str, str | None]  # version → statement text (None = absent)
    damaged: list[str]             # subset of ["A", "B", "preserved core"]
    causes: list[str] = field(default_factory=list)
    chain: list[tuple[str, str | None]] = field(default_factory=list)  # (code, var→next)


def witnesses(
    merged: merge.MergeResult,
    t1: interference.TypeIResult,
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
) -> list[Witness]:
    """Resolve Type-I's damaged sets into per-statement, per-version detail."""
    g_m = merged.graph
    to_a, to_b = canonicalizer(map_a), canonicalizer(map_b)
    ap_a_common = {to_a(n) for n in merged.ap_a}
    ap_b_common = {to_b(n) for n in merged.ap_b}

    sides = {}
    for w in t1.a_damaged:
        sides.setdefault(w, []).append("A")
    for w in t1.b_damaged:
        sides.setdefault(w, []).append("B")
    for w in t1.pre_damaged:
        sides.setdefault(w, []).append("preserved core")

    attr_by_node = {ac.node: ac for ac in merged.attribute_conflicts}
    adds_by_node: dict[str, list[merge.EdgeAddition]] = {}
    for ea in merged.edge_additions:
        adds_by_node.setdefault(ea.node, []).append(ea)

    out: list[Witness] = []
    for w in sorted(sides):
        d = g_m.nodes[w] if g_m.has_node(w) else {}
        wit = Witness(
            node=w,
            method=d.get("method", "?"),
            line=d.get("lineNumber"),
            col=d.get("columnNumber"),
            code=(d.get("code") or d.get("label") or w).strip(),
            versions=_versions_of(w, base, a, b, map_a, map_b),
            damaged=sides[w],
        )

        ac = attr_by_node.get(w)
        if ac is not None:
            texts = ", ".join(f"{v.upper()} has {c!r}" for v, c in ac.codes)
            wit.causes.append(f"contributors disagree on this statement: {texts}")
        for ea in adds_by_node.get(w, ()):
            for src, kind, var in sorted(ea.edges, key=str):
                src_code = (g_m.nodes[src].get("code") or src).strip() if g_m.has_node(src) else src
                dep = f"on {var!r} " if var else ""
                wit.causes.append(
                    f"the union adds a {kind} dependence {dep}from {src_code!r} "
                    f"that {ea.version.upper()} did not have"
                )
        if not wit.causes:
            wit.causes.append("downstream of the conflicting edits (dependence-affected)")

        # the opposing side's edits are the culprits the chain should reach from
        culprits: set[str] = set()
        if "A" in sides[w]:
            culprits |= ap_b_common
        if "B" in sides[w]:
            culprits |= ap_a_common
        if "preserved core" in sides[w]:
            culprits |= ap_a_common | ap_b_common
        wit.chain = _chain(g_m, culprits - {w}, w)
        out.append(wit)

    out.sort(key=lambda x: (x.method, x.line if x.line is not None else -1,
                            x.col if x.col is not None else -1, x.node))
    return out


def _versions_of(
    w: str,
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
) -> dict[str, str | None]:
    """The statement's text in each version; None where the vertex is absent."""
    def text(g: nx.MultiDiGraph, nid: str | None) -> str | None:
        if nid is None or not g.has_node(nid):
            return None
        d = g.nodes[nid]
        return (d.get("code") or d.get("label") or "").strip()

    a_id = map_a.get(w, w if a.has_node(w) else None)
    b_id = map_b.get(w, w if b.has_node(w) else None)
    return {
        "base": text(base, w if base.has_node(w) else None),
        "a": text(a, a_id),
        "b": text(b, b_id),
    }


def _chain(
    g_m: nx.MultiDiGraph, culprits: set[str], target: str
) -> list[tuple[str, str | None]]:
    """Shortest dependence path in G_M from any culprit to the witness.

    Rendered as (code, variable-to-next); empty when no culprit reaches the
    witness (e.g. the damage is an attribute clash at the witness itself)."""
    best: list[str] | None = None
    for c in sorted(culprits):
        if not g_m.has_node(c):
            continue
        try:
            path = nx.shortest_path(g_m, source=c, target=target)
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            continue
        if len(path) < 2:
            continue
        if best is None or len(path) < len(best):
            best = path
    if best is None:
        return []
    out: list[tuple[str, str | None]] = []
    for i, n in enumerate(best):
        code = (g_m.nodes[n].get("code") or g_m.nodes[n].get("label") or n).strip()
        var = None
        if i + 1 < len(best):
            edges = g_m.get_edge_data(n, best[i + 1]) or {}
            for e in edges.values():  # prefer a variable-labelled (DDG) edge
                if e.get("variable"):
                    var = e["variable"]
                    break
        out.append((code, var))
    return out


# ── rendering ────────────────────────────────────────────────────────────────
def render(
    merged: merge.MergeResult,
    t1: interference.TypeIResult,
    base: nx.MultiDiGraph,
    a: nx.MultiDiGraph,
    b: nx.MultiDiGraph,
    map_a: dict[str, str],
    map_b: dict[str, str],
    t2: feasibility.Type2Result | None = None,
) -> str:
    lines: list[str] = ["=== Semantic merge report ==="]
    if not t1.interferes:
        if t2 is not None and not t2.feasible:
            return "\n".join(lines + _type_ii_section(merged.graph, t2))
        g = merged.graph
        lines.append("VERDICT: clean — no Type-I interference; the merged program is emitted.")
        lines.append(
            f"  G_M: {g.number_of_nodes()} vertices, {g.number_of_edges()} edges · "
            f"A contributed {len(merged.contributions.get('a', ()))}, "
            f"B {len(merged.contributions.get('b', ()))}, "
            f"preserved core {len(merged.contributions.get('base', ()))}"
        )
        if t2 is not None:
            lines.append(
                f"  Type II: feasible — {len(t2.order)} block(s) ordered, "
                "emission follows the verified schedule"
            )
        return "\n".join(lines)

    wits = witnesses(merged, t1, base, a, b, map_a, map_b)
    lines.append(
        f"VERDICT: TYPE-I INTERFERENCE — merge refused ({len(wits)} conflicting point(s))"
    )
    lines.append(
        f"  damaged: A's changes at {len(t1.a_damaged)} point(s) · "
        f"B's changes at {len(t1.b_damaged)} point(s) · "
        f"preserved core at {len(t1.pre_damaged)} point(s)"
    )

    current_method = None
    for w in wits:
        if w.method != current_method:
            current_method = w.method
            lines.append(f"\nmethod {current_method}")
        pos = f"L{w.line}:{w.col}" if w.line is not None else "(synth)"
        lines.append(f"  ✗ {pos:>7}  {w.code!r}   [damages: {', '.join(w.damaged)}]")
        base_t, a_t, b_t = w.versions["base"], w.versions["a"], w.versions["b"]
        if len({base_t, a_t, b_t}) > 1:  # only show versions when they differ
            fmt = lambda t: "(absent)" if t is None else repr(t)
            lines.append(f"      base {fmt(base_t)} · A {fmt(a_t)} · B {fmt(b_t)}")
        for cause in w.causes:
            lines.append(f"      cause: {cause}")
        if len(w.chain) > 1:
            rendered = ""
            for i, (code, var) in enumerate(w.chain):
                rendered += repr(code)
                if i + 1 < len(w.chain):
                    rendered += f" →({var})→ " if var else " → "
            lines.append(f"      path:  {rendered}")

    if t2 is not None and not t2.feasible:
        # both tests fired: the union is unfaithful *and* unorderable. Report
        # each on its own terms rather than letting the first hide the second.
        lines.append("")
        lines += _type_ii_section(merged.graph, t2)

    lines.append("\nFix the conflicting statements on one side and re-merge.")
    return "\n".join(lines)


def _type_ii_section(g_m: nx.MultiDiGraph, t2: feasibility.Type2Result) -> list[str]:
    """The Type-II refusal: no program corresponds to the merged graph."""
    lines = [
        f"VERDICT: TYPE-II INFEASIBILITY — merge refused "
        f"({len(t2.violations)} unsatisfiable ordering constraint(s))",
        "  G_M is a faithful union, but no program has it as its PDG.",
    ]
    for v in t2.violations:
        lines.append(f"\n  ✗ [{v.kind}] {v.detail}")
        for nid in v.nodes:
            d = g_m.nodes[nid] if g_m.has_node(nid) else {}
            line = d.get("lineNumber")
            pos = f"L{line}:{d.get('columnNumber')}" if line is not None else "(synth)"
            code = (d.get("code") or d.get("label") or nid).strip()
            lines.append(f"      {pos:>7}  {code!r}")
    for parent in t2.inconclusive:
        d = g_m.nodes[parent] if g_m.has_node(parent) else {}
        code = (d.get("code") or parent).strip()
        lines.append(f"\n  ? loop body at {code!r}: a backwards dependence there may be "
                     "loop-carried; ordering left to source position")
    lines.append("\nRe-order the statements on one side and re-merge.")
    return lines


# ── pipeline runner (shared by CLI and selftest) ─────────────────────────────
def run(fdir: Path) -> tuple[str, bool]:
    """Run the full pipeline on a triple directory; (report text, refused).

    `refused` is true when either check fired — the tool's contract is that a
    merged program is emitted exactly when it is both faithful and realisable.
    """
    graphs = {v: load_pdg_file(fdir / "pdg_json" / f"{v}.json") for v in ("base", "a", "b")}
    map_a = correspondence.solve(graphs["base"], graphs["a"],
                                 base_src=fdir / "base.java", variant_src=fdir / "a.java")
    map_b = correspondence.solve(graphs["base"], graphs["b"],
                                 base_src=fdir / "base.java", variant_src=fdir / "b.java")
    ap_a = affected.affected_points_sdg(graphs["base"], graphs["a"], map_a)
    ap_b = affected.affected_points_sdg(graphs["base"], graphs["b"], map_b)
    merged = merge.merge_from_ap(graphs["base"], graphs["a"], graphs["b"],
                                 ap_a, ap_b, map_a, map_b, sdg=True)
    t1 = interference.type_i_interference(merged, graphs["base"], graphs["a"], graphs["b"],
                                          map_a, map_b, sdg=True)
    t2 = feasibility.check(merged.graph, contributors=graphs,
                           maps={"a": map_a, "b": map_b})
    text = render(merged, t1, graphs["base"], graphs["a"], graphs["b"], map_a, map_b, t2)
    return text, t1.interferes or not t2.feasible


# ── golden selftest ──────────────────────────────────────────────────────────
def _selftest() -> int:
    failed = 0
    for name in GOLDEN_FIXTURES:
        fdir = CORPUS / name
        golden = fdir / "expected_report.txt"
        if not golden.exists():
            print(f"[MISS] {name}: no golden — run `python3 report.py --bless {name}`")
            failed += 1
            continue
        text, _ = run(fdir)
        if text == golden.read_text():
            print(f"[OK]   {name}: report matches golden")
        else:
            print(f"[FAIL] {name}: report differs from golden")
            failed += 1
    # a clean fixture must render the clean verdict and report no witnesses
    text, interferes = run(CORPUS / "convergent_edit")
    if not interferes and "VERDICT: clean" in text:
        print("[OK]   convergent_edit: clean verdict rendered")
    else:
        print("[FAIL] convergent_edit: expected a clean report")
        failed += 1
    print(f"\n=== selftest: {'PASS' if not failed else f'{failed} FAILURE(S)'} ===")
    return 1 if failed else 0


def main() -> None:
    args = sys.argv[1:]
    if args and args[0] == "--selftest":
        sys.exit(_selftest())
    if args and args[0] == "--bless":
        for name in args[1:] or GOLDEN_FIXTURES:
            text, _ = run(CORPUS / name)
            (CORPUS / name / "expected_report.txt").write_text(text)
            print(f"blessed {name}/expected_report.txt")
        return
    fdir = CORPUS / args[0] if args else HERE.parent / "examples"
    if not (fdir / "pdg_json" / "base.json").exists():
        print(f"no exporter output under {fdir} — run: cd joern-sdg-exporter && sbt run")
        sys.exit(2)
    text, interferes = run(fdir)
    print(text)
    sys.exit(1 if interferes else 0)


if __name__ == "__main__":
    main()
