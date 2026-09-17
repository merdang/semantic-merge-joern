"""
Load PDG JSON emitted by the Scala exporter into NetworkX graphs.

Per-version only: nothing here knows about correspondence.
"""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx

HERE = Path(__file__).resolve().parent
JSON_DIR = HERE.parent / "examples" / "pdg_json"


def load_pdg(version: str) -> nx.MultiDiGraph:
    """Load one of the root triple's versions from examples/pdg_json/."""
    return load_pdg_file(JSON_DIR / f"{version}.json")


def load_pdg_file(path: Path | str) -> nx.MultiDiGraph:
    """Load an exported PDG JSON from anywhere (root triple or corpus fixture)."""
    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(f"No JSON at {path} — did the exporter run?")

    data = json.loads(path.read_text())
    g = nx.MultiDiGraph(version=data.get("version", path.stem))

    for m in data["methods"]:
        method_name = m["fullName"]
        for n in m["nodes"]:
            g.add_node(
                n["id"],
                method=method_name,
                label=n.get("label"),
                code=n.get("code", ""),
                name=n.get("name"),
                lineNumber=n.get("lineNumber"),
                columnNumber=n.get("columnNumber"),
                lineNumberEnd=n.get("lineNumberEnd"),
                columnNumberEnd=n.get("columnNumberEnd"),
                # variables the statement writes; the only place a dead
                # definition appears, having no outgoing DDG edge
                defs=tuple(n.get("defs") or ()),
                # variables the statement declares (a Java emission constraint)
                declares=tuple(n.get("declares") or ()),
                # statement rather than sub-expression; absent in older
                # exports, where reconstitution infers it from source spans
                **({"statement": n["statement"]} if "statement" in n else {}),
            )
        for e in m["edges"]:
            attrs = {"kind": e["kind"]}
            if "variable" in e:
                attrs["variable"] = e["variable"]
            # the vertex witnessing a def-order edge (HPR's `v1 ->do(v3) v2`)
            if "witness" in e:
                attrs["witness"] = e["witness"]
            # loop-carried: the definition is written after the use it serves
            if e.get("carried"):
                attrs["carried"] = True
            # branch polarity: the value the predicate must take to reach here
            if "branch" in e:
                attrs["branch"] = e["branch"]
            g.add_edge(e["src"], e["dst"], **attrs)

    # SDG layer (optional): CALL / PARAM_IN / PARAM_OUT edges across methods
    for e in data.get("interproceduralEdges", []):
        attrs = {"kind": e["kind"]}
        if "variable" in e:
            attrs["variable"] = e["variable"]
        g.add_edge(e["src"], e["dst"], **attrs)

    return g


def load_all() -> dict[str, nx.MultiDiGraph]:
    out: dict[str, nx.MultiDiGraph] = {}
    for v in ("base", "a", "b"):
        try:
            out[v] = load_pdg(v)
        except FileNotFoundError as e:
            print(e)
    return out


def summarize(g: nx.MultiDiGraph) -> None:
    version = g.graph.get("version", "?")
    methods = sorted({d["method"] for _, d in g.nodes(data=True)})
    kinds: dict[str, int] = {}
    for _, _, d in g.edges(data=True):
        kinds[d["kind"]] = kinds.get(d["kind"], 0) + 1

    print(f"=== version '{version}' ===")
    print(f"  nodes: {g.number_of_nodes()}   edges: {g.number_of_edges()}")
    print(f"  edge kinds: {kinds or '(none)'}")
    print(f"  methods ({len(methods)}):")
    for mn in methods:
        cnt = sum(1 for _, d in g.nodes(data=True) if d["method"] == mn)
        print(f"    - {mn}  ({cnt} nodes)")

    if "DDG" not in kinds:
        print("  !! WARNING: no DDG edges. Dataflow overlay may be missing.")
    if "CDG" not in kinds:
        # CDG can legitimately be empty for branch-free code.
        print("  (info) no CDG edges — expected for flat code without if/while.")


def method_subgraph(g: nx.MultiDiGraph, method_full_name: str) -> nx.MultiDiGraph:
    keep = [nid for nid, d in g.nodes(data=True) if d["method"] == method_full_name]
    return g.subgraph(keep).copy()
