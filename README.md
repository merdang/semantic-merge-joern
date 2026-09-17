# semantic-merge-joern

A three-way merge tool for Java that decides conflicts by **program semantics
rather than text**. It builds a System Dependence Graph for each of the three
versions, computes which program points changed behaviour, and reports
interference only where the two edits actually disturb each other — so
independent changes to adjacent lines merge cleanly, and changes that quietly
break each other across a call boundary are refused instead of merged.

The implementation follows the Horwitz–Prins–Reps and Binkley–Horwitz–Reps
integration algorithms, built on [Joern](https://joern.io)'s Code Property
Graph.

This is the artifact accompanying the master's thesis *Integrating System
Dependence Graphs into Joern's Code Property Graph for Interprocedural Semantic
Code Merging* (Merdan Gurbangylyjov, University of Passau, 2026).

---

## What it does

Given a triple `base.java`, `a.java`, `b.java`:

1. **Export** — a Scala pass builds a CPG per version with Joern's
   `javasrc2cpg`, applies the control-flow and control-dependence overlays plus
   the dataflow overlay, and emits a statement-level SDG as JSON.
2. **Correspond** — GumTree diffs the sources; the match is projected onto SDG
   vertices to decide which vertex in `A` *is* which vertex in `Base`.
3. **Affected points** — the vertices whose behaviour the edit changed, closed
   forward over data and control dependence.
4. **Merge** — the merged graph `G_M` is built unconditionally from the two
   changed-behaviour slices and the preserved core.
5. **Type I** — does the union corrupt either contributor's changed behaviour?
6. **Type II** — is `G_M` feasible: does *any* program have it as its PDG?
7. **Emit** — on a clean verdict, Java source is reconstituted from `G_M` in the
   order the feasibility check verified.

By default the analysis is **demand-driven**: it is seeded from the methods the
diff touched and reaches only as far as dependence actually carries it.
`--whole-program` runs the reference pipeline instead; the two are proved and
continuously tested to agree.

## Requirements

| | |
|---|---|
| **JDK** | 17 or newer — developed and tested on OpenJDK 20 |
| **sbt** | 1.10+ (the build pins 1.10.11) |
| **Scala** | 3.6.4 — fetched by sbt |
| **Joern** | 4.0.131 — fetched by sbt as a library; **no separate install needed** |
| **Python** | 3.10+ |
| **Python packages** | `networkx`; `matplotlib` only for the optional visualizer |
| **GumTree** | the `gumtree` CLI, for correspondence |

GumTree is located via the `GUMTREE_BIN` environment variable, falling back to
`gumtree` on `PATH`. Without it the pipeline degrades to a positional fallback,
which is weaker — install it for real results.

On macOS/Linux, `python` may be Python 2; use `python3` throughout.

## Build and run

### 1. Export the graphs

```bash
cd joern-sdg-exporter
sbt run
```

This writes `examples/pdg_json/*.json` for the development triple and for every
corpus fixture, printing a `[check]` line per version with its `REACHING_DEF`
and `CDG` counts. Both are nonzero for branching code.

The exporter resolves the examples tree relative to its own working directory.
To export a tree elsewhere, set `SDG_EXAMPLES_DIR`, or pass roots as arguments:

```bash
sbt "run /path/to/triples"
```

### 2. Run the merge

```bash
cd sdg-merge
python3 main.py                        # demand-driven merge (default)
python3 main.py --whole-program        # the whole-program reference
python3 main.py --show-correspondence  # dump each base→variant map and its APs
python3 main.py --visualize            # also render per-version PDG PNGs
```

Re-run the exporter after editing any `.java` input — the Python side reads the
exported JSON, never the source.

## Test suites

All four are self-contained; none compares against another tool.

```bash
cd sdg-merge

python3 evaluate.py            # corpus: 59 fixtures, textual vs semantic verdicts
python3 evaluate.py disjoint   # a single fixture by name

python3 fuzz.py                # 40 randomly generated triples
python3 fuzz.py 200 --seed 7   # a reproducible batch

python3 report.py --selftest   # conflict reports against committed goldens

python3 slicer.py              # each module has a runnable demo that asserts
```

What each asserts:

- **`evaluate.py`** — every fixture's verdict, affected-point counts and program
  output against a hand-derived `expected.json`; that a clean verdict yields a
  program which compiles and runs; that each version round-trips through its own
  graph; and that the demand-driven verdict equals the whole-program one.
- **`fuzz.py`** — six oracles over generated triples, including behavioural
  exactness (when `B ≡ Base`, the merge must behave *exactly* like `A`) and the
  soundness of both fast-path certificates.
- **`report.py --selftest`** — rendered conflict reports byte-match committed
  goldens.
- **module demos** — 16 modules run standalone and assert their own invariants.

Expected state: **52 of 59 fixtures pass, 7 pinned as known defects** (below).
A pinned fixture that starts passing is reported as `XPASS`, so no pin can
outlive its cause.

## Repository layout

```
sdg-merge/               the Python pipeline
  main.py                driver
  pdg.py                 JSON loader
  gumtree.py positions.py GumTree CLI wrapper, offset → (line, col)
  correspondence.py      cross-version vertex correspondence
  slicer.py              backward/forward slicing, intra- and interprocedural
  affected.py            affected points
  merge.py               merged graph G_M
  interference.py        Type-I check
  feasibility.py         Type-II check
  reconstitute.py        Java emission from G_M
  scope.py scoped.py     demand-driven scoping
  invariant.py fuzz.py evaluate.py report.py measure.py   oracles and harnesses
  visualize.py           per-method PDG renderer (no Graphviz needed)

joern-sdg-exporter/      the Scala exporter
  src/main/scala/CreateCpgs.scala

examples/
  base.java a.java b.java    the development triple
  corpus/<fixture>/          base/a/b.java + expected.json; clean fixtures also
                             carry merged.java, the committed merge result
```

The boundary between the two halves is the JSON contract: the exporter emits
self-contained per-version facts, and everything spanning versions —
correspondence, affected points, interference — lives in Python.

## Known limitations

Stated plainly, because the evaluation measures them rather than assuming them
away. All seven are pinned as fixtures in the corpus.

**Field dependence is not modelled** (`field_write`). Interference that flows
through a field is reported **clean**. This is an unsoundness, not a
conservative approximation, and it is the one case where this tool is not better
than a textual merge. Closing it needs reaching definitions over heap locations
plus alias analysis.

**Recursion is over-approximated** (`recursive_disjoint`). Two disjoint edits to
one recursive method are reported as interfering, because the two-pass closure
re-enters the method through its own recursive call site. The error is in the
safe direction — refusing a merge that was fine. Summary edges would fix it.

**Five constructs analyse correctly but do not emit**: `for`, `do`/`while`,
`switch`, `try`/`catch`, and labelled `break`. The merge verdict and the
affected points are right in every case; only source reconstitution fails, for
reasons tabulated per fixture in each `expected.json`. Ordinary `while`, `if`,
nested control flow, early `return`, and bare `break`/`continue` all emit
correctly.

**Type III interference is not implemented** — a scope decision rather than
an eighth pin. HRB's third check covers a
component added to a procedure in one variant meeting a new transitive call on
that procedure in the other. Its canonical shape is in the corpus as
`inter_type3`, where the Type-I check happens to reject the merge anyway — but
one instance is not a proof of subsumption.

Beyond these, precision is bounded by what the graph carries: array elements are
not distinguished from one another, and a multi-argument call site bundles its
actual parameters into a single vertex.

## How to cite

If you use this software, please cite the archived release:

> Gurbangylyjov, M. (2026). *semantic-merge-joern: semantic three-way merge for
> Java on Joern's Code Property Graph* (v1.0) [Software]. Zenodo.
> https://doi.org/10.5281/zenodo.22809122

```bibtex
@misc{gurbangylyjov2026semanticmerge,
  author       = {Gurbangylyjov, Merdan},
  title        = {{semantic-merge-joern}: Semantic Three-Way Merge for {Java}
                  on {Joern}'s Code Property Graph},
  year         = {2026},
  version      = {1.0},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.22809122},
  howpublished = {\url{https://doi.org/10.5281/zenodo.22809122}}
}
```

The thesis it accompanies is *Integrating System Dependence Graphs into Joern's
Code Property Graph for Interprocedural Semantic Code Merging* (University of
Passau, 2026).

## License

MIT — see [LICENSE](LICENSE).
