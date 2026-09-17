"""
Source reconstitution from the merged graph.

Turns a PDG in our schema (usually G_M, but any version works) back into Java.
Control structure comes from the CDG: a METHOD entry's CDG children are the
method's top-level statements, and a CONTROL_STRUCTURE is its header plus the
block its condition controls. Statement order is not decided here —
`feasibility.check` linearises each region and emission consumes that schedule.

A single class per file is assumed; synthetic methods without source positions
are skipped.

Run directly for a self-checking demo on corpus fixtures:
    python3 reconstitute.py
"""

from __future__ import annotations

import networkx as nx

INDENT = "    "


def reconstitute(
    g: nx.MultiDiGraph,
    order: dict[str, list[str]] | None = None,
    verbatim: dict[str, tuple[str, int, list[str]]] | None = None,
) -> str:
    """Emit Java source for every positioned method in `g`, class-wrapped.

    `order` maps a region parent to the sequence its block must be emitted in
    (see `regions`). Supply the ordering `feasibility.check` produced; omit it
    to fall back on source position.

    `verbatim` splices in methods not in `g`, as pre-rendered source
    (`fullName -> (class, sort key, lines)`): that is how the scoped merge
    emits a whole program, copying through methods all three versions agree
    on. Ordering methods mixes coordinate frames, which is admissible only
    because method order within a class carries no semantics in Java.
    """
    methods = [(nid, g.nodes[nid]) for nid in _method_entries(g)]

    # (class, sort key, payload) — payload is a node id to emit, or lines to splice
    items: list[tuple[str, int, str, object]] = [
        (_class_name(d), d["lineNumber"], "graph", nid) for nid, d in methods
    ]
    for cls, key, lines_ in (verbatim or {}).values():
        items.append((cls, key, "text", lines_))

    by_class: dict[str, list[tuple[int, str, object]]] = {}
    for cls, key, kind, payload in items:
        by_class.setdefault(cls, []).append((key, kind, payload))

    lines: list[str] = []
    for cls, entries in by_class.items():
        lines.append(f"public class {cls} {{")
        for _key, kind, payload in sorted(entries, key=lambda e: e[0]):
            if kind == "graph":
                _emit(g, payload, 1, lines, order)
            else:
                lines += payload
        lines.append("}")
    return "\n".join(lines) + "\n"


def _method_entries(g: nx.MultiDiGraph) -> list[str]:
    """Every METHOD vertex that carries a source position (synthetic `<init>`
    methods have none and are not emitted)."""
    return [
        nid
        for nid, d in g.nodes(data=True)
        if d.get("label") == "METHOD" and d.get("lineNumber") is not None
    ]


def regions(g: nx.MultiDiGraph) -> dict[str, list[str]]:
    """Region parent → its statement children, in source-position order. A
    region is one emitted block. Feasibility orders each region and emission
    consumes that order, so one function serves both."""
    out: dict[str, list[str]] = {}
    pending = list(_method_entries(g))
    while pending:
        parent = pending.pop()
        if parent in out:
            continue
        kids = _statement_children(g, parent)
        out[parent] = kids
        for k in list(kids) + alternative_of(g, parent):
            if g.nodes[k].get("label") == "CONTROL_STRUCTURE":
                pending.append(guard_of(g, k))
    return out


def _class_name(method_data: dict) -> str:
    # "Main.main:void(java.lang.String[])" → "Main"
    qualified = (method_data.get("method") or "?").split(":", 1)[0]
    return qualified.rsplit(".", 1)[0] if "." in qualified else qualified


# ── emission ─────────────────────────────────────────────────────────────────
def _emit(
    g: nx.MultiDiGraph,
    v: str,
    depth: int,
    lines: list[str],
    order: dict[str, list[str]] | None = None,
) -> None:
    d = g.nodes[v]
    pad = INDENT * depth
    code = (d.get("code") or "").strip()
    label = d.get("label")

    if label == "METHOD":
        lines.append(f"{pad}{code} {{")
        for child in _block_of(g, v, order):
            _emit(g, child, depth + 1, lines, order)
        lines.append(f"{pad}}}")
    elif label == "CONTROL_STRUCTURE" and is_jump(d):
        # `break` / `continue` carry no block, so they emit as plain
        # statements rather than the generic `code { … }` shape.
        lines.append(f"{pad}{code if code.endswith(';') else code + ';'}")
    elif label == "CONTROL_STRUCTURE":
        guard = guard_of(g, v)
        lines.append(f"{pad}{code} {{")
        for child in _block_of(g, guard, order):
            if _branch_of(g, guard, child) is not False:
                _emit(g, child, depth + 1, lines, order)
        lines.append(f"{pad}}}")
        # False-branch children emit at the same depth as their `if`, and in
        # the *schedule's* order rather than the CDG's edge order.
        alternatives = alternative_of(g, guard)
        ranked = {c: i for i, c in enumerate(_block_of(g, guard, order))}
        for child in sorted(alternatives, key=lambda c: ranked.get(c, len(ranked))):
            _emit(g, child, depth, lines, order)
    else:  # CALL / RETURN statements
        # Joern includes the trailing semicolon in RETURN codes but not CALL
        # ones; appending blindly would emit `return x;;`.
        stmt = code if code.endswith(";") else code + ";"
        lines.append(f"{pad}{stmt}")


def _block_of(
    g: nx.MultiDiGraph, parent: str, order: dict[str, list[str]] | None
) -> list[str]:
    """The sequence to emit for `parent`'s block — the checked schedule when
    Type II supplied one, else source-position order."""
    if order is not None and parent in order:
        return order[parent]
    return _statement_children(g, parent)


def is_jump(d: dict) -> bool:
    """Is this vertex a bare `break` / `continue`? Both are CONTROL_STRUCTURE
    vertices with no condition and no body, so they need distinguishing
    wherever a control structure is assumed to own a block."""
    if d.get("label") != "CONTROL_STRUCTURE":
        return False
    return (d.get("code") or "").strip().rstrip(";") in ("break", "continue")


def guard_of(g: nx.MultiDiGraph, cs: str) -> str:
    """What controls a control structure's body: its condition where it has
    one, and otherwise the vertex itself. javasrc2cpg gives an `else` its own
    CONTROL_STRUCTURE (code "else") with no condition, holding the alternative
    block."""
    return condition_of(g, cs) or cs


def _branch_of(g: nx.MultiDiGraph, parent: str, child: str) -> bool | None:
    """Polarity of the control dependence from `parent` to `child`."""
    for data in (g.get_edge_data(parent, child) or {}).values():
        if data.get("kind") == "CDG":
            return data.get("branch")
    return None


def alternative_of(g: nx.MultiDiGraph, guard: str) -> list[str]:
    """False-branch children of a predicate — in practice the `else` vertex.
    Read straight off the CDG, since an `else` hangs off the `if` rather than
    off a BLOCK and so is not a block child."""
    seen: set[str] = set()
    out: list[str] = []
    for _, dst, data in g.out_edges(guard, data=True):
        if data.get("kind") != "CDG" or data.get("branch") is not False or dst in seen:
            continue
        d = g.nodes[dst]
        # bypass the `statement` filter only for a control structure: the
        # `else` vertex, which is part of its `if` rather than a block statement
        if d.get("label") == "CONTROL_STRUCTURE" or d.get("statement", True):
            seen.add(dst)
            out.append(dst)
    return out


def _statement_children(g: nx.MultiDiGraph, parent: str) -> list[str]:
    """CDG children of `parent` that are real statements, in source order."""
    kids: list[str] = []
    seen: set[str] = set()
    for _, dst, data in g.out_edges(parent, data=True):
        if data.get("kind") != "CDG" or dst in seen:
            continue
        # A loop predicate is control-dependent on itself, so the CDG carries
        # a self-loop; emitting it as a child would print the condition as a
        # statement inside its own body.
        if dst == parent:
            continue
        seen.add(dst)
        if g.nodes[dst].get("label") in ("METHOD_PARAMETER_IN", "METHOD_RETURN"):
            continue  # implicit in the method header / closing brace
        kids.append(dst)

    # A condition CDG-points at sub-expressions inside its nested statements
    # too, so operands are filtered out using the exporter's `statement` flag.
    # The span fallback (a vertex nested in a sibling's span is an operand)
    # serves older exports only: it is unsafe in `G_M`, where vertices from
    # different versions can share a coordinate.
    if any("statement" in g.nodes[k] for k in kids):
        kids = [k for k in kids if g.nodes[k].get("statement")]
    else:
        kids = [
            k for k in kids
            if not any(
                subsumes(g.nodes[j], g.nodes[k]) and _shares_contributor(g.nodes[j], g.nodes[k])
                for j in kids if j != k
            )
        ]
    kids.sort(
        key=lambda n: (
            g.nodes[n].get("lineNumber") if g.nodes[n].get("lineNumber") is not None else -1,
            g.nodes[n].get("columnNumber") if g.nodes[n].get("columnNumber") is not None else -1,
        )
    )
    return kids


def _shares_contributor(a: dict, b: dict) -> bool:
    """True unless both vertices carry provenance and share no contributor.

    Plain per-version graphs have no `contributed_by`, so this is vacuously
    true there and the span test behaves exactly as it always did."""
    ca, cb = a.get("contributed_by"), b.get("contributed_by")
    if not ca or not cb:
        return True
    return bool(set(ca) & set(cb))


def subsumes(outer: dict, inner: dict) -> bool:
    """True if `inner`'s single-line source span sits inside `outer`'s."""
    line, col_o = outer.get("lineNumber"), outer.get("columnNumber")
    col_i = inner.get("columnNumber")
    if line is None or col_o is None or col_i is None:
        return False
    if inner.get("lineNumber") != line:
        return False
    end_o = col_o + len(outer.get("code") or "")
    end_i = col_i + len(inner.get("code") or "")
    if (col_o, end_o) == (col_i, end_i):
        return False  # identical spans never subsume each other
    return col_o <= col_i and end_i <= end_o


def condition_of(g: nx.MultiDiGraph, cs: str) -> str | None:
    """The condition CALL of a CONTROL_STRUCTURE.

    Structural, not positional: the condition is a DDG predecessor that itself
    controls a block and whose text occurs inside the header's. That keeps the
    pairing frame-independent, which matters in G_M, where a header and its
    condition may carry positions from different contributors. Falls back to a
    positional test for a condition with no DDG in-edge.

    Public because `feasibility` walks the same region tree emission does.
    """
    d = g.nodes[cs]
    header = d.get("code") or ""
    structural = {
        src
        for src, _dst, e in g.in_edges(cs, data=True)
        if e.get("kind") == "DDG"
        and src != cs
        and g.nodes[src].get("method") == d.get("method")
        and (g.nodes[src].get("code") or "").strip()
        and (g.nodes[src].get("code") or "").strip() in header
        and any(x.get("kind") == "CDG" for _, _, x in g.out_edges(src, data=True))
    }
    if len(structural) == 1:
        return structural.pop()


    line, col = d.get("lineNumber"), d.get("columnNumber")
    if line is None or col is None:
        return None
    end = col + len(d.get("code") or "")
    for n, nd in g.nodes(data=True):
        if n == cs or nd.get("method") != d.get("method"):
            continue
        if nd.get("lineNumber") != line or nd.get("columnNumber") is None:
            continue
        n_end = nd["columnNumber"] + len(nd.get("code") or "")
        if col <= nd["columnNumber"] and n_end <= end and any(
            e.get("kind") == "CDG" for _, _, e in g.out_edges(n, data=True)
        ):
            return n
    return None


# ── demonstration / smoke test ───────────────────────────────────────────────
def _normalized(source: str) -> str:
    return "".join(source.split())


def _javac_check(source: str) -> str:
    """Compile `source` in a temp dir; return a status line."""
    import subprocess
    import tempfile
    from pathlib import Path

    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "Main.java"
        f.write_text(source)
        try:
            r = subprocess.run(
                ["javac", "-d", td, str(f)], capture_output=True, text=True
            )
        except FileNotFoundError:
            return "javac not found — compile check skipped"
        assert r.returncode == 0, f"javac rejected the output:\n{r.stderr}"
        return "javac: compiles cleanly"


def _demo() -> None:
    import correspondence
    from merge import merge_graphs
    from pdg import HERE, load_pdg

    src = HERE.parent / "examples"
    base, a, b = load_pdg("base"), load_pdg("a"), load_pdg("b")
    map_a = correspondence.solve(base, a, base_src=src / "base.java", variant_src=src / "a.java")
    map_b = correspondence.solve(base, b, base_src=src / "base.java", variant_src=src / "b.java")
    merged = merge_graphs(base, a, b, map_a, map_b)

    source = reconstitute(merged.graph)
    print("=== Reconstituted merged program (real triple) ===\n")
    print(source)
    assert _normalized(source) == _normalized((src / "a.java").read_text()), \
        "G_M source must equal a.java up to whitespace (B == Base)"
    print("  (assertion passed: equals a.java up to whitespace)")
    print(f"  ({_javac_check(source)})")

    # Round-trip sanity on an unmerged PDG too: Base in, base.java out.
    base_source = reconstitute(base)
    assert _normalized(base_source) == _normalized((src / "base.java").read_text()), \
        "base PDG must round-trip to base.java"
    print("\n  (assertion passed: base PDG round-trips to base.java)")


if __name__ == "__main__":
    _demo()
