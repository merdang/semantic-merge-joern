"""
Evaluation harness — the corpus gate.

Drives every corpus fixture end-to-end against hand-traced ground truth:
exporter JSON → correspondence → affected points → G_M → Type I → Type II →
reconstituted Java → javac → java → stdout comparison. Both interference
tests run on every fixture, so each can be pinned independently.

A fixture is a directory under examples/corpus/ holding `base/a/b.java`, the
exporter's `pdg_json/` output, and `expected.json`:

    verdict     "clean", "type1" or "type2"
    feasible    optional: pin the Type-II outcome on its own
    git         what textual merge does, verified with `git merge-file`
    ap_a/ap_b   optional: hand-traced affected-point counts
    stdout      required for clean fixtures: output of the merged program
    round_trip_fails
                optional: versions the scheduler cannot yet reproduce
    category    optional: override the derived quadrant label
    expect_fail optional: the fixture is expected to FAIL and is reported
                [XFAIL]; if it starts passing it is [XPASS] and fails the run
    requires    "sdg" marks fixtures whose conflict flows through calls

Usage:
    python3 evaluate.py              # run every fixture
    python3 evaluate.py disjoint     # run selected fixtures by name
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

import affected
import correspondence
import feasibility
import interference
import invariant
import merge
import scoped
from pdg import HERE, load_pdg_file

CORPUS = HERE.parent / "examples" / "corpus"


def run_fixture(fdir: Path, git: str) -> list[str]:
    """Run one fixture end-to-end; return failure messages (empty = pass)."""
    expected = json.loads((fdir / "expected.json").read_text())
    failures: list[str] = []

    want_git = expected.get("git")
    if want_git is not None and git != want_git:
        failures.append(f"git (textual) verdict: expected {want_git}, got {git}")

    graphs = {}
    for v in ("base", "a", "b"):
        jf = fdir / "pdg_json" / f"{v}.json"
        if not jf.exists():
            return [f"missing {jf.name} — run the exporter (cd joern-sdg-exporter && sbt run)"]
        graphs[v] = load_pdg_file(jf)

    # Round-trip: each version's own graph, scheduled and emitted, must give
    # that version back. Independent of the merge, and it covers fixtures whose
    # verdict means emission is never reached — `loop_carried` and
    # `nested_control` are Type-I, so their reconstitution had never once been
    # exercised before this check existed.
    known_bad = set(expected.get("round_trip_fails", ()))
    for v in ("base", "a", "b"):
        detail = invariant.round_trip(graphs[v], fdir / f"{v}.java")
        if detail and v not in known_bad:
            failures.append(f"ROUND-TRIP: {detail}")
        elif not detail and v in known_bad:
            failures.append(
                f"ROUND-TRIP: {v}.java was pinned as failing (round_trip_fails) "
                f"but now round-trips — remove the pin"
            )

    map_a = correspondence.solve(
        graphs["base"], graphs["a"],
        base_src=fdir / "base.java", variant_src=fdir / "a.java",
    )
    map_b = correspondence.solve(
        graphs["base"], graphs["b"],
        base_src=fdir / "base.java", variant_src=fdir / "b.java",
    )
    # The interprocedural (HRB) path — identical to the intra path on
    # fixtures without SDG edges.
    ap_a = affected.affected_points_sdg(graphs["base"], graphs["a"], map_a)
    ap_b = affected.affected_points_sdg(graphs["base"], graphs["b"], map_b)

    for name, got in (("ap_a", ap_a), ("ap_b", ap_b)):
        want = expected.get(name)
        if want is not None and len(got) != want:
            variant = graphs[name[-1]]
            members = ", ".join(sorted(
                (variant.nodes[n].get("code") or variant.nodes[n].get("label") or n)[:30]
                for n in got
            ))
            failures.append(f"{name}: expected {want} points, got {len(got)}: [{members}]")

    # G_M is built *first* and unconditionally — it is the object the
    # interference tests are defined on, not an output of the merge (HRB
    # Fig. 12 does the same). Only emission is skipped when a test fires.
    merged = merge.merge_from_ap(
        graphs["base"], graphs["a"], graphs["b"], ap_a, ap_b, map_a, map_b, sdg=True
    )
    t1 = interference.type_i_interference(
        merged, graphs["base"], graphs["a"], graphs["b"], map_a, map_b, sdg=True
    )
    # Type II is not conditional on Type I: HRB Fig. 12 tests the constructed
    # graph with each check in turn, and the two answer different questions —
    # "is the union faithful?" and "does any program realise it?".
    t2 = feasibility.check(merged.graph, contributors=graphs,
                           maps={"a": map_a, "b": map_b})

    want_feasible = expected.get("feasible")
    if want_feasible is not None and t2.feasible != want_feasible:
        kinds = ", ".join(sorted({v.kind for v in t2.violations})) or "none"
        failures.append(
            f"feasible: expected {want_feasible}, got {t2.feasible} "
            f"(Type-II violations: {kinds})"
        )

    got_verdict = invariant.verdict_of(t1, t2)

    # The differential oracle. The demand-driven run (scoped.py) must reach
    # the same verdict as the whole-program pipeline on every fixture, every
    # time, so it runs here as a standing gate rather than a one-off script.
    sr = scoped.run(graphs["base"], graphs["a"], graphs["b"], map_a, map_b)
    if sr.verdict != got_verdict:
        failures.append(
            f"SCOPED: demand-driven verdict {sr.verdict} != whole-program "
            f"{got_verdict} (scope: {len(sr.expansion.scope.methods)} methods, "
            f"{len(sr.expansion.added)} pulled in)"
        )

    # Whenever the early-exit certificate holds (no boundary
    # vertex in either AP set), the plain intra-procedural pipeline must
    # reach the same verdict — that is what licenses skipping the SDG passes.
    # The intra run recomputes its own APs (sdg=False throughout): their
    # equality to the SDG APs under the certificate is part of the theorem,
    # so nothing is shared that the theorem is supposed to establish.
    if scoped.early_exit_certificate(graphs["a"], graphs["b"], ap_a, ap_b):
        intra_verdict = scoped.intra_verdict(
            graphs["base"], graphs["a"], graphs["b"], map_a, map_b)
        if intra_verdict != got_verdict:
            failures.append(
                f"EARLY-EXIT: certificate holds (APs boundary-free) but intra "
                f"verdict {intra_verdict} != interprocedural {got_verdict}"
            )

    # The Type-0 certificate is sound in one direction only — empty both ways
    # *proves* non-interference — and that direction is asserted here. (It is
    # not a gate: non-empty stays inconclusive.)
    pre = interference.type_0_from_ap(
        graphs["base"], graphs["a"], graphs["b"], ap_a, ap_b, map_a, map_b,
        sdg=True,
    )
    if not pre.interferes and t1.interferes:
        failures.append(
            "TYPE-0: certificate empty both ways (Δ_A ∩ AP_B = Δ_B ∩ AP_A = ∅), "
            "yet Type-I reports interference — the soundness direction broke"
        )

    if got_verdict != expected["verdict"]:
        failures.append(f"verdict: expected {expected['verdict']}, got {got_verdict}")
        return failures  # downstream stages are meaningless on the wrong verdict

    # The clean-path invariant: on a clean verdict this emits, compiles and
    # runs, and reports a *contract* violation if any of that fails. On any
    # other verdict it is a no-op. Attribute-conflict recording is
    # folded in, since a clash under a clean verdict is the same kind of defect.
    result = invariant.clean_path(merged, t1, t2)
    if not result.ok:
        failures.append(f"INVARIANT: {result.violation}")
        return failures

    if got_verdict != "clean":
        # correctly rejected — no merged program exists; drop any stale one
        (fdir / "merged.java").unlink(missing_ok=True)
        return failures

    # persist the merge result next to base/a/b.java for inspection
    (fdir / "merged.java").write_text(result.source)
    if result.stdout != expected["stdout"]:
        failures.append(f"stdout: expected {expected['stdout']!r}, got {result.stdout!r}")

    # The scoped path must produce a *program*, not only a verdict: scoped
    # methods reconstituted from the scoped G_M, every other method copied
    # through verbatim (they are identical in all three versions — that is
    # what kept them out of scope). It must compile, run, and print exactly
    # what the whole-program merge prints.
    scoped_src = scoped.emit(sr, graphs["base"], fdir / "base.java")
    scoped_out, err = invariant.compile_and_run(scoped_src)
    if err is not None:
        failures.append(f"SCOPED EMISSION: does not build/run — {err}")
    elif scoped_out != result.stdout:
        failures.append(
            f"SCOPED EMISSION: prints {scoped_out!r}, whole-program merge "
            f"prints {result.stdout!r}")
    else:
        (fdir / "merged_scoped.java").write_text(scoped_src)
    return failures


def _git_verdict(fdir: Path) -> str:
    """Three-way *textual* merge verdict for the triple, via `git merge-file`.

    Runs on copies in a temp dir (-p keeps inputs untouched anyway); the exit
    code is the number of conflicts, so 0 means git would merge silently.
    """
    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for name in ("a.java", "base.java", "b.java"):
            p = Path(td) / name
            p.write_text((fdir / name).read_text())
            paths[name] = str(p)
        try:
            r = subprocess.run(
                ["git", "merge-file", "-p", paths["a.java"], paths["base.java"], paths["b.java"]],
                capture_output=True, text=True,
            )
        except FileNotFoundError:
            return "git-missing"
    return "clean" if r.returncode == 0 else "conflict"




def main() -> None:
    if not CORPUS.is_dir():
        print(f"no corpus at {CORPUS}")
        sys.exit(1)
    fixtures = sorted(d for d in CORPUS.iterdir() if (d / "expected.json").exists())
    if sys.argv[1:]:
        fixtures = [f for f in fixtures if f.name in sys.argv[1:]]
    if not fixtures:
        print("no matching fixtures")
        sys.exit(1)

    print(f"=== Evaluation harness: {len(fixtures)} fixture(s) ===")
    failed = skipped = xfailed = 0
    rows: list[tuple[str, str, str, bool | None, str | None]] = []
    for fdir in fixtures:
        expected = json.loads((fdir / "expected.json").read_text())
        git = _git_verdict(fdir)
        if expected.get("requires"):
            skipped += 1
            rows.append((fdir.name, git, expected["verdict"], None,
                         expected.get("category")))
            print(f"\n[SKIP] {fdir.name}  (needs {expected['requires']} — "
                  f"ground truth: textual {git} · semantic {expected['verdict']})")
            print(f"       {expected.get('description', '')}")
            continue
        failures = run_fixture(fdir, git)
        known = expected.get("expect_fail")
        if known and failures:
            status, counts, ok = "XFAIL", False, True
        elif known:
            # the defect is gone — drop the marker and let the fixture guard it
            status, counts, ok = "XPASS", True, False
            failures = [f"expected to fail ({known}) but passed — remove expect_fail"]
        else:
            status, counts, ok = ("PASS", False, True) if not failures else ("FAIL", True, False)
        failed += counts
        xfailed += status == "XFAIL"
        rows.append((fdir.name, git, expected["verdict"], ok,
                     expected.get("category")))
        print(f"\n[{status}] {fdir.name}  (textual: {git} · semantic: {expected['verdict']})")
        print(f"       {expected.get('description', '')}")
        for msg in failures:
            print(f"       {'~~' if status == 'XFAIL' else '!!'} {msg}")

    print("\n=== textual (git) vs semantic verdicts ===")
    print(f"{'fixture':<22} {'git':<10} {'semantic':<10} category")
    for name, git, sem, ok, override in rows:
        # The quadrant is derived, but it is only a heuristic reading of
        # (git, semantic): a fixture may state its own, and `convergent_insert`
        # has to — git merges identical insertions correctly there, so "silent
        # bad textual merge" would be exactly backwards.
        if override is not None:
            cat = override
        elif git == "clean" and sem != "clean":
            cat = "silent bad textual merge — semantics catches it"
        elif git == "conflict" and sem == "clean":
            cat = "false textual conflict — semantics merges it"
        else:
            cat = "agreement"
        if ok is None:
            mark = "   (SKIPPED — awaiting SDG)"
        elif not ok:
            mark = "   (FAILED)"
        elif override and override.startswith("known defect"):
            mark = "   (XFAIL)"
        else:
            mark = ""
        print(f"{name:<22} {git:<10} {sem:<10} {cat}{mark}")

    ran = len(fixtures) - skipped
    line = f"=== {ran - failed - xfailed}/{ran - xfailed} fixtures passed"
    if xfailed:
        line += f"; {xfailed} known defect(s) pinned as XFAIL"
    if skipped:
        line += f"; {skipped} skipped (awaiting the interprocedural SDG)"
    print(f"\n{line} ===")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
