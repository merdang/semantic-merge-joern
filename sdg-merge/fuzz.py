"""
Randomised triples — the teeth behind the clean-path invariant.

Generates three-way merge triples nobody wrote and asserts the pipeline's
properties over them. The generated Java is deliberately small: variables are
declared and initialised up front, and helpers are acyclic and loop-free, so
no edit can move a use above its declaration or make a program diverge. Every
version is compiled and run first — a triple that fails to build is discarded
as a bad draw rather than counted against the tool.

The six oracles, all internal:

1. **Clean-path invariant.** A clean verdict emits a program that compiles
   and runs.
2. **One-sided exactness.** When `B ≡ Base`, the merge must be clean and
   print exactly what `A` prints. Symmetrically for `A ≡ Base`.
3. **Convergent exactness.** When `A ≡ B`, likewise — unless the shared
   change inserted a statement: correspondence never runs A↔B, so two
   independent insertions cannot be identified and Type I fires as specified.
4. **Scoped differential.** The demand-driven verdict must equal the
   whole-program one on every triple.
5. **Early-exit certificate.** Where `AP_A ∪ AP_B` is boundary-free, the
   intra-procedural pipeline must reach the interprocedural verdict.
6. **Type-0 certificate.** Where `Δ_A ∩ AP_B = Δ_B ∩ AP_A = ∅`, Type I must
   not fire.

A seed is printed on every run and accepted on the command line, so any
violation is reproducible; `--keep` leaves the offending triples under
`examples/fuzz/`.

Usage:
    python3 fuzz.py                 # 40 triples, random seed
    python3 fuzz.py 200 --seed 7    # reproducible batch
    python3 fuzz.py 40 --keep       # keep the generated triples on disk
Exit status: 0 only when **every** oracle holds. Every oracle held on full
batches when it was introduced, so a failure is a regression. The way to read
one is to *minimise the triple*, not to guess at it.
"""

from __future__ import annotations

import argparse
import copy
import random
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

import affected
import correspondence
import feasibility
import interference
import invariant
import merge
import scoped
from pdg import HERE, load_pdg_file

FUZZ_ROOT = HERE.parent / "examples" / "fuzz"
EXPORTER = HERE.parent / "joern-sdg-exporter"


# ── the generated language ───────────────────────────────────────────────────
@dataclass
class Expr:
    kind: str                 # lit | var_lit | var_var | call
    lit: int = 0
    a: str = ""
    b: str = ""
    callee: int = 0           # helper index, kind == "call" only

    def render(self) -> str:
        if self.kind == "lit":
            return str(self.lit)
        if self.kind == "var_lit":
            return f"{self.a} + {self.lit}"
        if self.kind == "call":
            return f"f{self.callee}({self.a})"
        return f"{self.a} + {self.b}"


@dataclass
class Assign:
    target: str
    expr: Expr

    def render(self, pad: str) -> list[str]:
        return [f"{pad}{self.target} = {self.expr.render()};"]


@dataclass
class If:
    var: str
    lit: int
    body: list[Assign]

    def render(self, pad: str) -> list[str]:
        out = [f"{pad}if ({self.var} > {self.lit}) {{"]
        for s in self.body:
            out += s.render(pad + "    ")
        return out + [f"{pad}}}"]


@dataclass
class While:
    counter: str
    bound: int
    body: list[Assign]

    def render(self, pad: str) -> list[str]:
        out = [f"{pad}while ({self.counter} < {self.bound}) {{"]
        for s in self.body:
            out += s.render(pad + "    ")
        # The increment is rendered, never stored — so no edit can remove or
        # retarget it, and every generated loop terminates by construction.
        out.append(f"{pad}    {self.counter} = {self.counter} + 1;")
        return out + [f"{pad}}}"]


@dataclass
class Helper:
    """`static int fK(int x)` — no loops, calls only lower-numbered helpers,
    so the call graph is acyclic and termination survives every edit."""
    idx: int
    inits: dict[str, int]                  # local declarations, up front
    body: list = field(default_factory=list)   # Assign | If only
    ret: Expr = field(default_factory=lambda: Expr("lit"))

    @property
    def variables(self) -> list[str]:
        return ["x", *self.inits]

    def render(self) -> list[str]:
        lines = [f"    static int f{self.idx}(int x) {{"]
        for v, val in self.inits.items():
            lines.append(f"        int {v} = {val};")
        for s in self.body:
            lines += s.render("        ")
        lines.append(f"        return {self.ret.render()};")
        return lines + ["    }"]


@dataclass
class Program:
    variables: list[str]
    counters: list[str]
    inits: dict[str, int]
    body: list = field(default_factory=list)
    helpers: list[Helper] = field(default_factory=list)

    def render(self) -> str:
        lines = ["public class Main {", "    public static void main(String[] args) {"]
        for v in self.variables:
            lines.append(f"        int {v} = {self.inits[v]};")
        for c in self.counters:
            lines.append(f"        int {c} = 0;")
        for s in self.body:
            lines += s.render("        ")
        for v in self.variables:
            lines.append(f"        System.out.println({v});")
        lines.append("    }")
        for h in self.helpers:
            lines.append("")
            lines += h.render()
        return "\n".join(lines + ["}"]) + "\n"


# ── generation ───────────────────────────────────────────────────────────────
def _expr(
    rng: random.Random, variables: list[str], callables: list[int] = ()
) -> Expr:
    if callables and rng.random() < 0.22:
        return Expr("call", callee=rng.choice(callables), a=rng.choice(variables))
    kind = rng.choice(("lit", "var_lit", "var_var", "var_lit"))
    if kind == "lit":
        return Expr("lit", lit=rng.randint(0, 9))
    if kind == "var_lit":
        return Expr("var_lit", lit=rng.randint(0, 9), a=rng.choice(variables))
    return Expr("var_var", a=rng.choice(variables), b=rng.choice(variables))


def _helper(
    rng: random.Random, idx: int, stmts: tuple[int, int] = (1, 3)
) -> Helper:
    """One `static int f{idx}(int x)`: two locals, `stmts` statements, a
    return. May call only strictly lower-numbered helpers — acyclic by
    construction."""
    h = Helper(idx=idx, inits={f"h{i}": rng.randint(0, 5) for i in range(2)})
    lower = list(range(1, idx))
    for _ in range(rng.randint(*stmts)):
        if rng.random() < 0.75:
            h.body.append(Assign(rng.choice(h.variables),
                                 _expr(rng, h.variables, lower)))
        else:
            h.body.append(If(
                rng.choice(h.variables), rng.randint(0, 4),
                [Assign(rng.choice(h.variables), _expr(rng, h.variables, lower))],
            ))
    h.ret = _expr(rng, h.variables, lower)
    if h.ret.kind == "lit":                # a constant return ignores the body;
        h.ret = Expr("var_lit", lit=rng.randint(0, 9),   # keep the flow alive
                     a=rng.choice(h.variables))
    return h


def generate(
    rng: random.Random, n_vars: int = 4, n_stmts: int = 7,
    max_helpers: int = 3, min_helpers: int = 0,
    helper_stmts: tuple[int, int] = (1, 3),
) -> Program:
    """The size knobs default to the standing-gate tier, so
    `fuzz.py`'s batches keep their runtime; `measure.py` passes larger tiers
    where "fraction of the program touched" becomes a real measurement."""
    variables = [f"v{i}" for i in range(n_vars)]
    inits = {v: rng.randint(0, 5) for v in variables}
    prog = Program(variables=variables, counters=[], inits=inits)
    # 0 helpers keeps a pure intra-procedural share in every batch; the rest
    # exercise calls, chains (helper→helper), and the certificates' SDG halves.
    prog.helpers = [_helper(rng, i + 1, helper_stmts)
                    for i in range(rng.randint(min_helpers, max_helpers))]
    callables = [h.idx for h in prog.helpers]

    for _ in range(n_stmts):
        roll = rng.random()
        if roll < 0.62:
            prog.body.append(Assign(rng.choice(variables),
                                    _expr(rng, variables, callables)))
        elif roll < 0.85:
            prog.body.append(If(
                rng.choice(variables), rng.randint(0, 4),
                [Assign(rng.choice(variables), _expr(rng, variables, callables))
                 for _ in range(rng.randint(1, 2))],
            ))
        else:
            counter = f"c{len(prog.counters)}"
            prog.counters.append(counter)
            prog.body.append(While(
                counter, rng.randint(1, 3),
                [Assign(rng.choice(variables), _expr(rng, variables, callables))
                 for _ in range(rng.randint(1, 2))],
            ))
    return prog


@dataclass
class _Site:
    """One mutable method: its statement list, variable scope, and which
    helpers a call inserted or retargeted here may name (strictly lower
    indices inside a helper, so no edit can create recursion)."""
    body: list
    variables: list[str]
    callables: list[int]
    min_body: int            # deletion floor (main keeps 3; a helper may empty)
    extra_literals: list     # If/While headers + a helper's return expression


def _sites(prog: Program) -> list[_Site]:
    out = [_Site(prog.body, prog.variables, [h.idx for h in prog.helpers],
                 min_body=2,
                 extra_literals=[s for s in prog.body if isinstance(s, (If, While))])]
    for h in prog.helpers:
        out.append(_Site(h.body, h.variables, list(range(1, h.idx)),
                         min_body=0,
                         extra_literals=[s for s in h.body if isinstance(s, If)]
                                        + [h.ret]))
    return out


def _body_assigns(site: _Site) -> list[Assign]:
    """Every Assign in the site, including inside its If/While blocks."""
    out: list[Assign] = []
    for s in site.body:
        if isinstance(s, Assign):
            out.append(s)
        else:
            out += s.body
    return out


def mutate(
    rng: random.Random, prog: Program, n_edits: int
) -> tuple[Program, set[str]]:
    """Apply `n_edits` random edits; return the program and the edit kinds used.
    Every edit is compilation-safe by construction. The kinds are returned
    because `insert` and `recall` change which oracles apply to a convergent
    triple (see `check`)."""
    out = copy.deepcopy(prog)
    used: set[str] = set()
    for _ in range(n_edits):
        site = rng.choice(_sites(out))
        kinds = ["reliteral", "retarget", "insert", "swap"]
        if len(site.body) > site.min_body:
            kinds.append("delete")
        choice = rng.choice(kinds)
        used.add(choice)

        if choice == "reliteral":
            targets = _body_assigns(site) + site.extra_literals
            if not targets:
                continue
            t = rng.choice(targets)
            if isinstance(t, Assign):
                t.expr.lit = rng.randint(0, 9)
            elif isinstance(t, If):
                t.lit = rng.randint(0, 4)
            elif isinstance(t, While):
                t.bound = rng.randint(1, 3)
            else:                       # a helper's return expression
                t.lit = rng.randint(0, 9)

        elif choice == "retarget":
            assigns = _body_assigns(site)
            if not assigns:
                continue
            t = rng.choice(assigns)
            roll = rng.random()
            if roll < 0.4:
                t.target = rng.choice(site.variables)
            elif t.expr.kind == "call":
                # move the call's argument, or point it at another helper of
                # the same arity. The latter is its own kind ("recall"): a
                # call's name is part of the correspondence key, so retargeting
                # is delete + add and creates a new vertex.
                if rng.random() < 0.5 or len(site.callables) < 2:
                    t.expr.a = rng.choice(site.variables)
                else:
                    t.expr.callee = rng.choice(
                        [c for c in site.callables if c != t.expr.callee])
                    used.add("recall")
            elif t.expr.kind != "lit":
                t.expr.a = rng.choice(site.variables)
                if t.expr.kind == "var_var":
                    t.expr.b = rng.choice(site.variables)

        elif choice == "insert":
            at = rng.randint(0, len(site.body))
            site.body.insert(at, Assign(
                rng.choice(site.variables),
                _expr(rng, site.variables, site.callables)))

        elif choice == "delete":
            site.body.pop(rng.randrange(len(site.body)))

        elif choice == "swap" and len(site.body) > 1:
            i = rng.randrange(len(site.body) - 1)
            site.body[i], site.body[i + 1] = site.body[i + 1], site.body[i]
    return out, used


# ── building a batch ─────────────────────────────────────────────────────────
@dataclass
class Triple:
    name: str
    path: Path
    shape: str                  # both | b_is_base | a_is_base | convergent
    outputs: dict[str, str]     # version → stdout
    edits: set[str] = field(default_factory=set)  # edit kinds applied


def build_batch(
    rng: random.Random, count: int, gen_kwargs: dict | None = None
) -> list[Triple]:
    """Generate, validate and write `count` triples; discard bad draws.
    `gen_kwargs` forwards size knobs to `generate` (measure.py's tiers)."""
    if FUZZ_ROOT.exists():
        shutil.rmtree(FUZZ_ROOT)
    FUZZ_ROOT.mkdir(parents=True)

    triples: list[Triple] = []
    attempts = 0
    while len(triples) < count and attempts < count * 6:
        attempts += 1
        base = generate(rng, **(gen_kwargs or {}))
        roll = rng.random()
        edits: set[str] = set()
        if roll < 0.60:
            shape = "both"
            a, ea = mutate(rng, base, rng.randint(1, 3))
            b, eb = mutate(rng, base, rng.randint(1, 3))
            edits = ea | eb
        elif roll < 0.75:
            shape = "b_is_base"
            a, edits = mutate(rng, base, rng.randint(1, 3))
            b = copy.deepcopy(base)
        elif roll < 0.90:
            shape = "a_is_base"
            b, edits = mutate(rng, base, rng.randint(1, 3))
            a = copy.deepcopy(base)
        else:
            shape = "convergent"
            a, edits = mutate(rng, base, rng.randint(1, 3))
            b = copy.deepcopy(a)

        sources = {"base": base.render(), "a": a.render(), "b": b.render()}
        outputs: dict[str, str] = {}
        for version, source in sources.items():
            stdout, err = invariant.compile_and_run(source)
            if err is not None:
                break              # bad draw — not a tool defect
            outputs[version] = stdout
        else:
            name = f"t{len(triples):04d}"
            path = FUZZ_ROOT / name
            path.mkdir()
            for version, source in sources.items():
                (path / f"{version}.java").write_text(source)
            triples.append(Triple(name=name, path=path, shape=shape,
                                  outputs=outputs, edits=edits))
    return triples


def export(paths_root: Path) -> bool:
    """Run the Scala exporter over one root (one sbt start for the whole batch)."""
    r = subprocess.run(
        ["sbt", f'run {paths_root}'], cwd=EXPORTER, capture_output=True, text=True
    )
    if r.returncode != 0:
        print(r.stdout[-4000:], file=sys.stderr)
        print(r.stderr[-2000:], file=sys.stderr)
    return r.returncode == 0


# ── the oracles ──────────────────────────────────────────────────────────────
def check(triple: Triple) -> tuple[str, list[tuple[str, str]], set[str]]:
    """Run the pipeline on one triple; (verdict, [(kind, message)], certs).

    `kind` is "invariant", "exactness", "scoped", or "early-exit" / "type-0",
    counted apart because they mean different things. `certs` names the
    certificates that *applied*, so the summary can report how often each
    assertion actually bit rather than counting vacuous passes.
    """
    graphs = {}
    for v in ("base", "a", "b"):
        jf = triple.path / "pdg_json" / f"{v}.json"
        if not jf.exists():
            return "?", [("invariant", f"exporter produced no {v}.json")], set()
        graphs[v] = load_pdg_file(jf)

    map_a = correspondence.solve(graphs["base"], graphs["a"],
                                 base_src=triple.path / "base.java",
                                 variant_src=triple.path / "a.java")
    map_b = correspondence.solve(graphs["base"], graphs["b"],
                                 base_src=triple.path / "base.java",
                                 variant_src=triple.path / "b.java")
    ap_a = affected.affected_points_sdg(graphs["base"], graphs["a"], map_a)
    ap_b = affected.affected_points_sdg(graphs["base"], graphs["b"], map_b)
    merged = merge.merge_from_ap(graphs["base"], graphs["a"], graphs["b"],
                                 ap_a, ap_b, map_a, map_b, sdg=True)
    t1 = interference.type_i_interference(merged, graphs["base"], graphs["a"],
                                          graphs["b"], map_a, map_b, sdg=True)
    t2 = feasibility.check(merged.graph, contributors=graphs,
                           maps={"a": map_a, "b": map_b})
    result = invariant.clean_path(merged, t1, t2)

    violations: list[tuple[str, str]] = []
    if not result.ok:
        violations.append(("invariant", result.violation))

    # oracle 4: the demand-driven verdict must equal the whole-program one on
    # generated triples too, not only on fixtures the author thought of.
    sr = scoped.run(graphs["base"], graphs["a"], graphs["b"], map_a, map_b)
    if sr.verdict != result.verdict:
        violations.append(("scoped",
            f"demand-driven verdict {sr.verdict} != whole-program {result.verdict} "
            f"(scope: {len(sr.expansion.scope.methods)} methods, "
            f"{len(sr.expansion.added)} pulled in)"))

    # oracles 5–6: certificate soundness. Each certificate
    # licenses skipping work, so each is held to its claim wherever it holds.
    certs: set[str] = set()
    if scoped.early_exit_certificate(graphs["a"], graphs["b"], ap_a, ap_b):
        certs.add("early-exit")
        iv = scoped.intra_verdict(graphs["base"], graphs["a"], graphs["b"],
                                  map_a, map_b)
        if iv != result.verdict:
            violations.append(("early-exit",
                f"certificate holds (APs boundary-free) but intra verdict {iv} "
                f"!= interprocedural {result.verdict}"))
    pre = interference.type_0_from_ap(
        graphs["base"], graphs["a"], graphs["b"], ap_a, ap_b, map_a, map_b,
        sdg=True)
    if not pre.interferes:
        certs.add("type-0")
        if t1.interferes:
            violations.append(("type-0",
                "certificate empty both ways yet Type-I fired — "
                "the soundness direction broke"))

    # oracle 2/3: a merge with nothing to integrate must reproduce the one side
    # that changed — exactly, value by value.
    expected_side = {"b_is_base": "a", "a_is_base": "b", "convergent": "a"}.get(triple.shape)
    if triple.shape == "convergent" and triple.edits & {"insert", "recall"}:
        # Exactness is not claimable here, and structurally so: correspondence
        # runs base→A and base→B only, never A↔B, so two independently created
        # vertices have no counterpart to be identified through. G_M keeps both
        # copies and Type I fires correctly. "recall" is the same situation:
        # the callee's name is part of the vertex key.
        expected_side = None
    if expected_side is not None:
        if result.verdict != "clean":
            violations.append(("exactness",
                f"{triple.shape}: verdict {result.verdict}, but a merge in which only "
                f"one side changed has nothing to interfere with and must be clean"))
        elif result.ok and result.stdout != triple.outputs[expected_side]:
            violations.append(("exactness",
                f"{triple.shape}: merged output {result.stdout!r} != "
                f"{expected_side}'s own output {triple.outputs[expected_side]!r}"))
    return result.verdict, violations, certs


def main() -> None:
    ap = argparse.ArgumentParser(description="Randomised clean-path invariant testing")
    ap.add_argument("count", nargs="?", type=int, default=40, help="triples to generate")
    ap.add_argument("--seed", type=int, default=None, help="reproduce a previous batch")
    ap.add_argument("--keep", action="store_true", help="leave triples on disk")
    args = ap.parse_args()

    seed = args.seed if args.seed is not None else random.randrange(1 << 30)
    rng = random.Random(seed)
    print(f"=== Randomised clean-path testing: {args.count} triples, seed {seed} ===")

    triples = build_batch(rng, args.count)
    print(f"  generated and validated {len(triples)} triples "
          f"(base/a/b each compile and terminate)")
    if not triples:
        sys.exit(1)

    print("  exporting via Joern (one sbt run for the batch) …")
    if not export(FUZZ_ROOT):
        print("!! exporter failed")
        sys.exit(1)

    tally: dict[str, int] = {}
    shapes: dict[str, int] = {}
    broke: dict[str, int] = {"invariant": 0, "exactness": 0, "scoped": 0,
                             "early-exit": 0, "type-0": 0}
    applied: dict[str, int] = {"early-exit": 0, "type-0": 0}
    for triple in triples:
        verdict, violations, certs = check(triple)
        tally[verdict] = tally.get(verdict, 0) + 1
        shapes[triple.shape] = shapes.get(triple.shape, 0) + 1
        for cert in certs:
            applied[cert] += 1
        for kind in {k for k, _ in violations}:
            broke[kind] = broke.get(kind, 0) + 1
        if violations:
            print(f"\n[{violations[0][0].upper()}] {triple.name} ({triple.shape})")
            for _kind, message in violations:
                print(f"    {message}")

    print("\n  verdicts: " + ", ".join(f"{k}={v}" for k, v in sorted(tally.items())))
    print("  shapes:   " + ", ".join(f"{k}={v}" for k, v in sorted(shapes.items())))
    total = len(triples)
    print(f"\n  clean-path invariant : {total - broke['invariant']}/{total} held")
    print(f"  behavioural exactness: {total - broke['exactness']}/{total} held")
    print(f"  scoped == whole      : {total - broke['scoped']}/{total} held")
    # Certificate oracles report against the triples they *applied* to — a
    # vacuous pass (certificate refused) is not evidence for the theorem.
    for cert, label in (("early-exit", "early-exit certificate"),
                        ("type-0", "type-0 certificate    ")):
        print(f"  {label}: held on {applied[cert] - broke[cert]}/{applied[cert]} "
              f"triples it applied to")

    if any(broke.values()):
        # A failure here is a regression. Do not reach for a cause: minimise
        # the triple and look.
        for kind, count in sorted(broke.items()):
            if count:
                print(f"\n=== {count}/{total} triple(s) broke the {kind} oracle "
                      f"(reproduce with --seed {seed}) ===")
        print(f"    triples kept at {FUZZ_ROOT} — minimise one before theorising")
        sys.exit(1)

    print(f"\n=== all {total} triples: clean-path invariant, exactness, "
          f"scoped-differential and both certificates held ===")
    if args.keep:
        print(f"    triples kept at {FUZZ_ROOT}")
    else:
        shutil.rmtree(FUZZ_ROOT, ignore_errors=True)


if __name__ == "__main__":
    main()
