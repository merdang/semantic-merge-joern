"""
Per-method PDG renderer. Pure-Python layered layout — no Graphviz.

Importable from main.py (`from visualize import draw`) or runnable standalone:
    python3 visualize.py                 # all versions
    python3 visualize.py a               # one version
    python3 visualize.py base "Main.main:void(java.lang.String[])"
"""

from __future__ import annotations

import sys
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
import networkx as nx

from pdg import HERE, load_all, method_subgraph

OUT_DIR = HERE / "out"

NODE_COLOR = {
    "METHOD":              "#1E2761",
    "METHOD_RETURN":       "#F0E6C0",
    "METHOD_PARAMETER_IN": "#D8D0F0",
    "CONTROL_STRUCTURE":   "#F7D6D0",
    "RETURN":              "#F0E6C0",
    "CALL":                "#E8EFFB",
}

EDGE_COLOR = {"DDG": "#1D9E75", "CDG": "#D85A30"}
EDGE_STYLE = {"DDG": "solid",   "CDG": "dashed"}


def _layered_pos(g: nx.MultiDiGraph) -> dict:
    """Top-down layered layout. Within each layer, sort by (line, column,
    code) so statements appear in source order left-to-right."""
    simple = nx.DiGraph()
    simple.add_nodes_from(g.nodes())
    simple.add_edges_from((u, v) for u, v in g.edges())

    dag = simple
    if not nx.is_directed_acyclic_graph(simple):
        dag = simple.copy()
        while not nx.is_directed_acyclic_graph(dag):
            cyc = nx.find_cycle(dag)
            dag.remove_edge(*cyc[-1][:2])

    layer: dict = {}
    for n in nx.topological_sort(dag):
        preds = list(dag.predecessors(n))
        layer[n] = 0 if not preds else max(layer[p] for p in preds) + 1

    rows = defaultdict(list)
    for n, lv in layer.items():
        rows[lv].append(n)

    def sort_key(n):
        d = g.nodes[n]
        return (
            d.get("lineNumber") or 9999,
            d.get("columnNumber") or 0,
            d.get("code") or "",
        )

    pos = {}
    xg, yg = 3.0, 1.6
    for lv, nodes in rows.items():
        nodes = sorted(nodes, key=sort_key)
        width = (len(nodes) - 1) * xg
        for i, n in enumerate(nodes):
            pos[n] = (i * xg - width / 2, -lv * yg)
    return pos


def _node_text(d: dict) -> str:
    code = (d.get("code") or "").strip().replace("\n", " ")
    if len(code) > 24:
        code = code[:23] + "…"
    lbl = d.get("label", "")
    ln = d.get("lineNumber")
    line_tag = f"L{ln}" if ln is not None else ""
    short = {
        "METHOD_PARAMETER_IN": "PARAM",
        "CONTROL_STRUCTURE":   "CTRL",
    }.get(lbl, lbl)
    return f"{short}\n{code}\n{line_tag}".rstrip()


def draw(
    g: nx.MultiDiGraph,
    method: str | None = None,
    hide_orphan_method: bool = True,
    out_dir: Path = OUT_DIR,
) -> Path | None:
    """Render one method's PDG to PNG. Returns the output path or None."""
    out_dir.mkdir(parents=True, exist_ok=True)
    if method is None:
        methods = {d["method"] for _, d in g.nodes(data=True)}
        if not methods:
            print(f"no methods in version '{g.graph.get('version','?')}'")
            return None
        method = max(
            methods,
            key=lambda mn: sum(1 for _, d in g.nodes(data=True) if d["method"] == mn),
        )

    sg = method_subgraph(g, method)
    if sg.number_of_nodes() == 0:
        print(f"No nodes for method '{method}'.")
        return None

    if hide_orphan_method:
        orphans = [
            n for n, d in sg.nodes(data=True)
            if d.get("label") == "METHOD" and sg.degree(n) == 0
        ]
        sg = sg.copy()
        sg.remove_nodes_from(orphans)

    pos = _layered_pos(sg)

    ys = [p[1] for p in pos.values()] or [0]
    height = max(7, 1.6 * (max(ys) - min(ys)) + 4)
    plt.figure(figsize=(15, height))

    for lbl in {d.get("label") for _, d in sg.nodes(data=True)}:
        ns = [n for n, d in sg.nodes(data=True) if d.get("label") == lbl]
        nx.draw_networkx_nodes(
            sg, pos, nodelist=ns,
            node_color=NODE_COLOR.get(lbl, "#FFFFFF"),
            edgecolors="#1E2761", node_size=2400, linewidths=0.9,
        )

    light_nodes = [n for n, d in sg.nodes(data=True) if d.get("label") != "METHOD"]
    dark_nodes  = [n for n, d in sg.nodes(data=True) if d.get("label") == "METHOD"]
    if light_nodes:
        nx.draw_networkx_labels(
            sg, pos,
            labels={n: _node_text(sg.nodes[n]) for n in light_nodes},
            font_size=7, font_family="monospace", font_color="#1A1A2E",
        )
    if dark_nodes:
        nx.draw_networkx_labels(
            sg, pos,
            labels={n: _node_text(sg.nodes[n]) for n in dark_nodes},
            font_size=7, font_family="monospace", font_color="white",
        )

    for i, kind in enumerate(("DDG", "CDG")):
        ek = [(u, v) for u, v, d in sg.edges(data=True) if d["kind"] == kind]
        if not ek:
            continue
        nx.draw_networkx_edges(
            sg, pos, edgelist=ek,
            edge_color=EDGE_COLOR[kind],
            width=1.5, arrows=True, arrowsize=13,
            connectionstyle=f"arc3,rad={0.08 * (i + 1)}",
            node_size=2400,
            style=EDGE_STYLE[kind],
        )

    ddg_by_pair: dict = {}
    for u, v, d in sg.edges(data=True):
        if d["kind"] == "DDG" and d.get("variable"):
            ddg_by_pair.setdefault((u, v), []).append(d["variable"])
    edge_labels = {p: ",".join(sorted(set(vs))) for p, vs in ddg_by_pair.items()}
    if edge_labels:
        nx.draw_networkx_edge_labels(
            sg, pos, edge_labels=edge_labels,
            font_size=7, font_color="#0F6B4E",
            bbox=dict(facecolor="white", edgecolor="none", pad=1),
        )

    handles = [
        plt.Line2D([0], [0], color=EDGE_COLOR["DDG"], lw=2, label="DDG (data)"),
        plt.Line2D([0], [0], color=EDGE_COLOR["CDG"], lw=2,
                   linestyle="dashed", label="CDG (control)"),
    ]
    plt.legend(handles=handles, loc="upper right", fontsize=9)
    plt.title(f"PDG — '{g.graph.get('version','?')}' — {method}", fontsize=10)
    plt.axis("off")
    plt.tight_layout()

    safe_method = method.replace(":", "_").replace("/", "_").replace(" ", "_")
    out = out_dir / f"pdg_{g.graph.get('version','x')}_{safe_method}.png"
    plt.savefig(out, dpi=150, bbox_inches="tight")
    plt.close()
    print(f"saved -> {out}")
    return out


def draw_all(graphs: dict[str, nx.MultiDiGraph], method: str | None = None) -> None:
    for g in graphs.values():
        draw(g, method=method)


def main() -> None:
    args = sys.argv[1:]
    graphs = load_all()
    if not graphs:
        print("No JSON files found. Run the exporter first.")
        return

    versions = [args[0]] if args else list(graphs)
    method = args[1] if len(args) >= 2 else None

    for v in versions:
        if v not in graphs:
            print(f"version '{v}' not loaded")
            continue
        draw(graphs[v], method=method)
        print()


if __name__ == "__main__":
    main()
