"""
Cost instrumentation.

Measures what the demand-driven run confines, on generated triples large
enough for "fraction of the program touched" to mean something. Scope
fractions and time ratios are reported as per-tier distributions rather than
as one speedup number; CPG construction and correspondence are timed as their
own stages and charged to neither side; and every measured triple asserts
scoped verdict == whole-program verdict.

Usage:
    python3 measure.py                              # 25 triples per tier
    python3 measure.py 50 --tiers S,M,L,XL          # more, and larger
    python3 measure.py --csv cost.csv               # write per-triple rows
"""

from __future__ import annotations

import argparse
import csv
import random
import statistics
import sys
import time
from dataclasses import dataclass

import affected
import correspondence
import feasibility
import interference
import invariant
import merge
import scoped
from fuzz import FUZZ_ROOT, build_batch, export
from pdg import load_pdg_file

# The size tiers. S is the standing-gate tier (fuzz.py's defaults, with at
# least one helper so scope has something to confine); M and L are where the
# demand-driven premise — edits small relative to the program — becomes
# measurable. Edits stay at 1–3 regardless of size, deliberately: that *is*
# the premise.
TIERS: dict[str, dict] = {
    "S": dict(n_stmts=7, min_helpers=1, max_helpers=3, helper_stmts=(1, 3)),
    "M": dict(n_stmts=10, min_helpers=3, max_helpers=5, helper_stmts=(2, 4)),
    "L": dict(n_stmts=14, min_helpers=6, max_helpers=8, helper_stmts=(3, 6)),
    # XL extends the size trend past the point where the median ratio crosses
    # 1 (between M and L), so the crossing is bracketed rather than asserted
    # from its endpoint. Same edit budget as every other tier — that is the
    # premise being measured.
    "XL": dict(n_stmts=20, min_helpers=22, max_helpers=26, helper_stmts=(4, 8)),
}


@dataclass
class Row:
    tier: str
    name: str
    verdict: str
    path: str                # early-exit | type0 | full — which certificate fired
    methods_total: int
    methods_scope: int
    vertices_total: int
    vertices_scope: int
    rounds: int          # historical name: methods added beyond the seed,
                         # not growth rounds. Kept — it is a cost.csv column.
    t_corr: float
    t_whole: float
    t_scoped: float


def _measure_triple(tier: str, triple) -> Row:
    graphs = {v: load_pdg_file(triple.path / "pdg_json" / f"{v}.json")
              for v in ("base", "a", "b")}

    t0 = time.perf_counter()
    map_a = correspondence.solve(graphs["base"], graphs["a"],
                                 base_src=triple.path / "base.java",
                                 variant_src=triple.path / "a.java")
    map_b = correspondence.solve(graphs["base"], graphs["b"],
                                 base_src=triple.path / "base.java",
                                 variant_src=triple.path / "b.java")
    t_corr = time.perf_counter() - t0

    t0 = time.perf_counter()
    ap_a = affected.affected_points_sdg(graphs["base"], graphs["a"], map_a)
    ap_b = affected.affected_points_sdg(graphs["base"], graphs["b"], map_b)
    merged = merge.merge_from_ap(graphs["base"], graphs["a"], graphs["b"],
                                 ap_a, ap_b, map_a, map_b, sdg=True)
    t1 = interference.type_i_interference(
        merged, graphs["base"], graphs["a"], graphs["b"], map_a, map_b,
        sdg=True)
    t2 = feasibility.check(merged.graph, contributors=graphs,
                           maps={"a": map_a, "b": map_b})
    whole_verdict = invariant.verdict_of(t1, t2)
    t_whole = time.perf_counter() - t0

    t0 = time.perf_counter()
    sr = scoped.run(graphs["base"], graphs["a"], graphs["b"], map_a, map_b)
    t_scoped = time.perf_counter() - t0

    if sr.verdict != whole_verdict:
        print(f"!! DIFFERENTIAL VIOLATION on {triple.name}: scoped "
              f"{sr.verdict} != whole {whole_verdict} — timing a wrong "
              f"answer is worthless; aborting")
        sys.exit(1)

    methods = {d.get("method") for g in graphs.values()
               for _, d in g.nodes(data=True)}
    vertices_total = sum(g.number_of_nodes() for g in graphs.values())
    vertices_scope = sum(
        sum(1 for _, d in g.nodes(data=True)
            if d.get("method") in sr.expansion.scope)
        for g in graphs.values())
    return Row(
        tier=tier, name=triple.name, verdict=whole_verdict, path=sr.path,
        methods_total=len(methods),
        methods_scope=len(sr.expansion.scope.methods),
        vertices_total=vertices_total, vertices_scope=vertices_scope,
        rounds=len(sr.expansion.added),
        t_corr=t_corr, t_whole=t_whole, t_scoped=t_scoped,
    )


def _quartiles(xs: list[float]) -> tuple[float, float, float]:
    q = statistics.quantiles(xs, n=4) if len(xs) > 1 else [xs[0]] * 3
    return q[0], q[1], q[2]


def _summarise(tier: str, rows: list[Row], t_export: float) -> None:
    n = len(rows)
    mf = [r.methods_scope / r.methods_total for r in rows]
    vf = [r.vertices_scope / r.vertices_total for r in rows]
    ratio = [r.t_scoped / r.t_whole for r in rows]
    verdicts: dict[str, int] = {}
    for r in rows:
        verdicts[r.verdict] = verdicts.get(r.verdict, 0) + 1
    growth = sum(1 for r in rows if r.rounds > 0)

    def q3(xs):
        a, b, c = _quartiles(xs)
        return f"{a:.2f}/{b:.2f}/{c:.2f}"

    print(f"\n─── tier {tier}: {n} triples "
          f"({', '.join(f'{k}={v}' for k, v in sorted(verdicts.items()))}) ───")
    print(f"  program size          : {statistics.median(r.methods_total for r in rows):.0f} methods, "
          f"{statistics.median(r.vertices_total for r in rows):.0f} vertices per triple (medians)")
    print(f"  methods in scope      : q1/med/q3 {q3(mf)} of total "
          f"({growth}/{n} triples reached beyond the edited methods)")
    print(f"  vertices in scope     : q1/med/q3 {q3(vf)} of total")
    print(f"  analysis time, whole  : median {statistics.median(r.t_whole for r in rows)*1000:.0f} ms")
    print(f"  analysis time, scoped : median {statistics.median(r.t_scoped for r in rows)*1000:.0f} ms")
    print(f"  scoped/whole ratio    : q1/med/q3 {q3(ratio)}")
    # which theorem decided each triple, and what each path cost relative to
    # the whole-program run — the certificates' contribution made visible
    by_path: dict[str, list[float]] = {}
    for r in rows:
        by_path.setdefault(r.path, []).append(r.t_scoped / r.t_whole)
    parts = []
    for p in ("early-exit", "type0", "full"):
        if p in by_path:
            xs = by_path[p]
            parts.append(f"{p}: {len(xs)} (median ratio {statistics.median(xs):.2f})")
    print(f"  verdict paths         : {'; '.join(parts)}")
    print(f"  correspondence (shared): median {statistics.median(r.t_corr for r in rows)*1000:.0f} ms")
    print(f"  CPG export (whole-program by construction, incl. sbt startup): "
          f"{t_export:.0f} s batch, {t_export/n:.1f} s/triple")


def main() -> None:
    ap = argparse.ArgumentParser(description="Cost instrumentation")
    ap.add_argument("count", nargs="?", type=int, default=25,
                    help="triples per tier")
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--tiers", default="S,M,L")
    ap.add_argument("--csv", default=None, help="write per-triple rows")
    args = ap.parse_args()

    seed = args.seed if args.seed is not None else random.randrange(1 << 30)
    rng = random.Random(seed)
    tiers = [t.strip() for t in args.tiers.split(",") if t.strip()]
    print(f"=== Step-43 measurement: {args.count} triples/tier, "
          f"tiers {','.join(tiers)}, seed {seed} ===")

    all_rows: list[Row] = []
    for tier in tiers:
        triples = build_batch(rng, args.count, gen_kwargs=TIERS[tier])
        print(f"\n[{tier}] generated {len(triples)} triples; exporting …")
        t0 = time.perf_counter()
        if not export(FUZZ_ROOT):
            print("!! exporter failed")
            sys.exit(1)
        t_export = time.perf_counter() - t0
        rows = [_measure_triple(tier, t) for t in triples]
        all_rows += rows
        _summarise(tier, rows, t_export)

    if args.csv:
        with open(args.csv, "w", newline="") as fh:
            w = csv.writer(fh)
            w.writerow([f.name for f in Row.__dataclass_fields__.values()])
            for r in all_rows:
                w.writerow([getattr(r, f) for f in Row.__dataclass_fields__])
        print(f"\nper-triple rows written to {args.csv}")

    print(f"\n=== every measured triple held scoped == whole "
          f"(seed {seed} reproduces) ===")


if __name__ == "__main__":
    main()
