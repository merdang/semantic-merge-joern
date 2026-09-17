"""
The clean-path invariant.

The tool's contract, stated once and checked everywhere:

    a triple the pipeline calls **clean** yields a merged program that
    exists, compiles, and runs.

Not HPR's theorem — behaviour preservation is undecidable — but its checkable
shadow. A violation here means the tool's contract is broken, rather than a
fixture's expectation being wrong, and callers report it as such.

Run directly for a self-checking demo on corpus fixtures:
    python3 invariant.py
"""

from __future__ import annotations

import subprocess
import tempfile
from dataclasses import dataclass
from typing import Callable
from pathlib import Path

import feasibility
import interference
import merge
import reconstitute

RUN_TIMEOUT = 20  # seconds; generated triples must terminate


@dataclass(frozen=True)
class CleanPath:
    """The outcome of emitting a clean merge. `violation` is None when the
    contract held; `stdout` is the merged program's output when it ran."""
    verdict: str                    # clean | type1 | type2
    source: str | None = None
    stdout: str | None = None
    violation: str | None = None

    @property
    def ok(self) -> bool:
        return self.violation is None


def verdict_of(
    t1: interference.TypeIResult, t2: feasibility.Type2Result
) -> str:
    """The pipeline's verdict, in HRB Fig. 12's order — Type I, then Type II.
    One definition, so "clean" cannot mean different things in different
    callers."""
    if t1.interferes:
        return "type1"
    return "clean" if t2.feasible else "type2"


def clean_path(
    merged: merge.MergeResult,
    t1: interference.TypeIResult,
    t2: feasibility.Type2Result,
    run: bool = True,
    emit: "Callable[[], str] | None" = None,
) -> CleanPath:
    """Emit a clean merge and assert the contract holds; a no-op otherwise.
    `run=False` stops after `javac`. `emit` overrides how the source is
    produced — the scoped pipeline supplies `scoped.emit` — while the contract
    checks around it stay identical."""
    verdict = verdict_of(t1, t2)
    if verdict != "clean":
        return CleanPath(verdict=verdict)

    # An attribute clash on a shared vertex provably forces Type-I interference
    # (merge.py), so recording one under a clean verdict means construction and
    # verdict disagree — a contract violation, not a bad expectation.
    if merged.attribute_conflicts:
        return CleanPath(
            verdict=verdict,
            violation=(
                f"clean verdict with {len(merged.attribute_conflicts)} attribute "
                f"conflict(s) recorded: {merged.attribute_conflicts[:2]}"
            ),
        )

    try:
        source = (emit() if emit is not None
                  else reconstitute.reconstitute(merged.graph, order=t2.order))
    except Exception as exc:  # emission must not fail on a feasible graph
        return CleanPath(
            verdict=verdict,
            violation=f"clean verdict but emission raised {type(exc).__name__}: {exc}",
        )

    stdout, err = compile_and_run(source, run=run)
    if err is not None:
        return CleanPath(verdict=verdict, source=source, violation=err)
    return CleanPath(verdict=verdict, source=source, stdout=stdout)


def round_trip(g: "nx.MultiDiGraph", source: Path) -> str | None:
    """A program's own PDG, scheduled and emitted, must reproduce the program.

    Needs no merge: a single version's graph goes through the scheduler and
    the emitter, and the result must be that version's source again (modulo
    whitespace). Unlike `reconstitute.py`'s own round-trip check, this one
    exercises `feasibility`'s schedule rather than source position.

    Returns None when the program round-trips, else a description.
    """
    t2 = feasibility.check(g)
    emitted = reconstitute.reconstitute(g, order=t2.order)
    want = source.read_text()
    if _squash(emitted) == _squash(want):
        return None
    import difflib
    diff = "".join(difflib.unified_diff(
        want.splitlines(True), emitted.splitlines(True),
        source.name, "round-tripped", n=1))
    return f"{source.name} does not round-trip through its own PDG:\n{diff}"


def _squash(source: str) -> str:
    return "".join(source.split())


def compile_and_run(source: str, run: bool = True) -> tuple[str, str | None]:
    """javac (+ java) the merged program in a temp dir; (stdout, violation)."""
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "Main.java"
        f.write_text(source)
        try:
            c = subprocess.run(["javac", "-d", td, str(f)], capture_output=True, text=True)
        except FileNotFoundError:
            return "", "javac not found on PATH"
        if c.returncode != 0:
            return "", (
                "clean verdict but the merged program does not compile "
                f"— the clean-path invariant is broken:\n{c.stderr}"
            )
        if not run:
            return "", None
        try:
            r = subprocess.run(
                ["java", "-cp", td, "Main"], capture_output=True, text=True,
                timeout=RUN_TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            return "", (
                f"clean verdict but the merged program did not terminate within "
                f"{RUN_TIMEOUT}s — the clean-path invariant is broken"
            )
        if r.returncode != 0:
            return "", (
                "clean verdict but the merged program crashed "
                f"— the clean-path invariant is broken:\n{r.stderr}"
            )
        return r.stdout, None


# ── demonstration / smoke test ───────────────────────────────────────────────
def _demo() -> None:
    """Assert the invariant on the running dev triple, and that a broken
    program is actually caught (the check must not be vacuous)."""
    import affected
    import correspondence
    from pdg import HERE, load_pdg

    src = HERE.parent / "examples"
    base, a, b = load_pdg("base"), load_pdg("a"), load_pdg("b")
    map_a = correspondence.solve(base, a, base_src=src / "base.java", variant_src=src / "a.java")
    map_b = correspondence.solve(base, b, base_src=src / "base.java", variant_src=src / "b.java")
    ap_a = affected.affected_points_sdg(base, a, map_a)
    ap_b = affected.affected_points_sdg(base, b, map_b)
    merged = merge.merge_from_ap(base, a, b, ap_a, ap_b, map_a, map_b, sdg=True)
    t1 = interference.type_i_interference(merged, base, a, b, map_a, map_b, sdg=True)
    t2 = feasibility.check(merged.graph, contributors={"base": base, "a": a, "b": b},
                           maps={"a": map_a, "b": map_b})

    result = clean_path(merged, t1, t2)
    print(f"--- dev triple: verdict {result.verdict} ---")
    assert result.verdict == "clean", result
    assert result.ok, result.violation
    print(f"  invariant holds: compiles, runs, prints {result.stdout!r}")

    # The check must be able to fail: hand it source that does not compile.
    _, err = compile_and_run("public class Main { not java }")
    assert err is not None and "does not compile" in err, err
    print("  (assertion passed: a non-compiling program is reported as a violation)")

    # …and source that runs forever.
    _, err = compile_and_run(
        "public class Main { public static void main(String[] a) { while (true) {} } }"
    )
    assert err is not None and "terminate" in err, err
    print("  (assertion passed: a non-terminating program is reported as a violation)")

    # ── round-trip: the dev triple's own versions must survive the scheduler.
    for version, path in (("base", src / "base.java"), ("a", src / "a.java")):
        detail = round_trip(load_pdg(version), path)
        assert detail is None, detail
    print("  (assertion passed: base and a round-trip through their own PDGs)")


if __name__ == "__main__":
    _demo()
