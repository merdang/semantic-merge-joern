"""
HRB / HPR semantic-merge driver.

Loads Base / A / B, computes vertex correspondence, builds the merged graph
G_M, and runs Type I then Type II on it. Source is emitted only when both
pass, and must compile and run. The merge is demand-driven by default;
`--whole-program` runs the whole-program reference the scoped path is tested
against.

Usage:
    python3 main.py                          # demand-driven merge (default)
    python3 main.py --whole-program          # the whole-program reference
    python3 main.py --visualize              # + per-version PDG PNGs
    python3 main.py --show-correspondence    # + each mapping and its APs
"""

from __future__ import annotations

import argparse
import sys

import affected
import correspondence
import feasibility
import interference
import invariant
import merge
import report
import scoped
from pdg import HERE, load_all, summarize

SRC_DIR = HERE.parent / "examples"


def run_algorithm(
    graphs: dict, show_mapping: bool = False, whole_program: bool = False
) -> None:
    for g in graphs.values():
        summarize(g)
        print()

    base = graphs.get("base")
    if base is None:
        print("base PDG missing — cannot compute correspondence.")
        return

    print("=== Correspondence (base → variant) ===")
    maps: dict[str, dict[str, str]] = {}
    for v in ("a", "b"):
        variant = graphs.get(v)
        if variant is None:
            continue
        maps[v] = correspondence.solve(
            base, variant,
            base_src=SRC_DIR / "base.java",
            variant_src=SRC_DIR / f"{v}.java",
        )
        print(f"  base → {v}: {len(maps[v])} vertex mappings")

    if "a" in maps and "b" in maps:
        # G_M is what the tests are defined on, so it is built first and
        # unconditionally (HRB Fig. 12): a firing test skips emission only.
        emit = None
        if whole_program:
            print("\n=== Whole-program pipeline (the reference) ===")
            aps = {v: affected.affected_points_sdg(base, graphs[v], maps[v])
                   for v in ("a", "b")}
            merged = merge.merge_from_ap(
                base, graphs["a"], graphs["b"],
                aps["a"], aps["b"], maps["a"], maps["b"], sdg=True,
            )
            t1 = interference.type_i_interference(
                merged, base, graphs["a"], graphs["b"], maps["a"], maps["b"],
                sdg=True,
            )
            t2 = feasibility.check(merged.graph, contributors=graphs,
                                   maps={"a": maps["a"], "b": maps["b"]})
        else:
            print("\n=== Demand-driven pipeline ===")
            sr = scoped.run(base, graphs["a"], graphs["b"], maps["a"], maps["b"])
            total = len({d["method"] for _, d in base.nodes(data=True)})
            scoped.show(sr, total_methods=total)
            merged, t1, t2 = sr.merged, sr.t1, sr.t2
            aps = {v: sr.expansion.sets[v][1] for v in ("a", "b")
                   if v in sr.expansion.sets}
            emit = lambda: scoped.emit(sr, base, SRC_DIR / "base.java")

        for v in ("a", "b"):
            if v in aps:
                print(f"  AP_{v.upper()} = {len(aps[v])} affected points")
                if show_mapping:
                    correspondence.show(base, graphs[v], maps[v],
                                        title=f"base → {v}")
                    affected.show(graphs[v], aps[v], mapping=maps[v],
                                  title=f"AP_{v.upper()}")

        merge.show(merged)
        interference.show_type_i(t1, base, graphs["a"], graphs["b"], merged.graph)
        feasibility.show(t2, merged.graph)

        # the user-facing outcome: per-statement conflict report
        print("\n" + report.render(
            merged, t1, base, graphs["a"], graphs["b"], maps["a"], maps["b"], t2
        ))

        # Emission goes through the clean-path invariant, so the driver holds
        # itself to the contract the harness enforces.
        result = invariant.clean_path(merged, t1, t2, emit=emit)
        if result.verdict == "type1":
            print("\nIntegration aborted: Type-I interference — no merged program.")
        elif result.verdict == "type2":
            print("\nIntegration aborted: Type-II infeasibility — no program realises G_M.")
        elif not result.ok:
            print(f"\n!! CLEAN-PATH INVARIANT VIOLATED: {result.violation}")
            sys.exit(1)
        else:
            merged_path = SRC_DIR / "merged.java"
            merged_path.write_text(result.source)
            print(f"\n=== Reconstituted merged program (saved to {merged_path}) ===\n")
            print(result.source, end="")
            print(f"  (invariant holds: compiles and runs, printing {result.stdout!r})")


def run_visualization(graphs: dict) -> None:
    from visualize import draw_all
    print("=== Visualization ===")
    draw_all(graphs)


def main() -> None:
    parser = argparse.ArgumentParser(description="HRB semantic-merge driver")
    parser.add_argument(
        "--visualize", "-v", action="store_true",
        help="Render per-version PDG PNGs after the algorithm phase",
    )
    parser.add_argument(
        "--show-correspondence", "-s", action="store_true",
        help="Dump each base→variant mapping and its affected points",
    )
    parser.add_argument(
        "--whole-program", "-w", action="store_true",
        help="Run the whole-program reference pipeline instead of the "
             "demand-driven one (they are proved and tested to agree)",
    )
    args = parser.parse_args()

    graphs = load_all()
    if not graphs:
        print("No JSON files found. Run the exporter first.")
        sys.exit(1)

    run_algorithm(graphs, show_mapping=args.show_correspondence,
                  whole_program=args.whole_program)
    if args.visualize:
        print()
        run_visualization(graphs)


if __name__ == "__main__":
    main()
