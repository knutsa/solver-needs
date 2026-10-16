# Identifying What the Solver Needs: essential assertions and their mechanisms

Code and data release for

> *Identifying What the Solver Needs: LLMs and the Missing Proof Hints in SMT Verification.*
> NeurIPS 2026 workshop submission.

The pipeline finds the **essential assertions** of verified Dafny and Verus
programs, the `assert` statements whose removal breaks verification, and
classifies each one by the solver mechanism it compensates for, found as the
first mechanical intervention that restores the proof with the assertion
removed:

| Label | Mechanism | Probe |
|---|---|---|
| `AX` | axiomatization gap: a needed identity between collections that the SMT encoding leaves unstated | one sequence law (listed in `laws.py` of each verifier) added to the verifier's background axioms, or the *equality seed* of a collection equality |
| `INST-forall`, `INST-witness` | instantiation gap: a quantified fact is available but never triggered | a *term seed*, a ghost variable holding a subterm of the assertion |
| `NLA` | nonlinear arithmetic (Verus with Z3 only) | re-verify with Z3's nonlinear theory enabled |
| `FUEL` | exhausted unfolding fuel (Verus only) | `reveal_with_fuel` for the recursive functions the assertion mentions |
| `Other` | no probe explains the assertion | |

Four verifier/solver configurations are covered: Dafny + Z3, Dafny + cvc5,
Verus + Z3 and Verus + cvc5, over four corpora: CF-D and DB for Dafny, CF-V
and VB for Verus. The repository ships the corpora, the
essential-assertion datasets written by the extractors, the extraction pipeline and the recorded probe
outcomes of a complete classification run for each configuration.

## Installation

Python 3.13 and [uv](https://docs.astral.sh/uv/):

```sh
uv sync                              # the package and its dev tools
uv run pytest -q                     # unit tests and consistency checks of the recorded data
```

The table scripts need nothing else. Running the probes needs the verifiers
and solvers of the paper, installed under `tools/` (gitignored) by

```sh
tools/setup_toolchain.sh [--fork] [--verus DIR] [--cvc5 DIR]
```

which downloads the Dafny 4.11.0 release and Z3 4.12.1 for macOS arm64 or
Linux x86_64, links existing Verus and cvc5 installs, and, with `--fork`,
clones and builds the Dafny fork. Binary locations are read from
`solver_needs/config.py`: `tools/` by default, or the environment variables
`SOLVER_NEEDS_DAFNY_DLL`, `SOLVER_NEEDS_Z3`, `SOLVER_NEEDS_VERUS` and
`SOLVER_NEEDS_CVC5`.

| Tool | Version in the paper | How it is obtained |
|---|---|---|
| Dafny | fork of [marchiesa/dafny](https://github.com/marchiesa/dafny), branch `proof-lifting`, commit `06ff43f7c` (reports itself as 4.11.1, two commits on top of upstream Dafny after 4.11.0) | `--fork` clones and builds it (needs the .NET 8 SDK; a JDK is fetched if none is on PATH). The fork adds `dafny verify --ast-mapping <file>`, a JSON mapping from Dafny source constructs (variables with their types, assertions, contracts) to the Boogie it generates; the classifier reads it to decide whether an equality is between collections. Every probe also runs on the stock 4.11.0 release, which the script always downloads; without the fork the collection decision falls back to the assertion's text. |
| Z3 | 4.12.1 | downloaded; passed to Dafny with `--solver-path` |
| Verus | 0.2026.02.22 with its bundled Z3 | [release page](https://github.com/verus-lang/verus/releases/tag/release/0.2026.02.22); pass the unpacked directory with `--verus` |
| cvc5 | 1.1.2 | [release page](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2); pass the unpacked directory with `--cvc5`. Dafny reaches it through `tools/cvc5_dafny.sh`, which puts the resource limit, seed and time limit on cvc5's command line because Boogie sends those options to Z3 only; Verus through `-V cvc5`. |

## Layout

```
solver_needs/          the package
  config.py            paths, toolchain lookup, resource limits
  corpora.py           the four corpora and how the extractors enumerate them
  labels.py            labels, the four configurations, the benchmark task sets
  dafny/               source.py (assert statements, terms, declarations), verify.py,
                       laws.py (the ten sequence laws), shape.py (AST mapping, collection
                       equalities), extract.py, classify.py, calibrate.py, dafnybench.py
  verus/               source.py, verify.py, laws.py (the nine sequence laws), extract.py,
                       classify.py
scripts/               table1.py, overlap.py, verus_laws.py
data/corpora/          CF-D/, DB/, CF-V/, VB/ (provenance and licences in data/corpora/README.md)
data/essential/        essential_{dafny,verus}_{z3,cvc5}.json: the extracted essential assertions
data/benchmark_sets/   dafny_tasks.json (320), verus_tasks.json (462): the task keys of the
                       paper's repair benchmark with the labels the paper assigns them
results/<config>/      probes.json (every probe outcome per assertion), labels.json
tools/                 setup_toolchain.sh, cvc5_dafny.sh, and the gitignored installs
tests/
LICENSE                MIT, the code
LICENSE-DATA           CC BY 4.0, the generated corpora, datasets and results
```

## Reproducing the tables

### Table 1

```sh
uv run python scripts/table1.py
```

prints the mechanism counts of the recorded run per configuration and
corpus and, for the Z3 configurations, the counts on the benchmark task sets
with the labels the paper assigns them.

The paper's Table 1 reports the 320 Dafny and 462 Verus benchmark tasks,
whose keys and labels are shipped in `data/benchmark_sets/`, so the paper's
rows reproduce from them exactly. The recorded run of the released pipeline
covers a larger set of essential assertions over the same corpora under the
essentiality screen (removal, second seed, placebo, enclosing-declaration
verification). The mismatch is due to running the benchmark evaluations on
an earlier version of the extraction pipeline.

| Configuration | Paper total | Release total | Note |
|---|---|---|---|
| Dafny + Z3 | 320 | 386 |  
| Dafny + cvc5 | 221 | 221 |
| Verus + Z3 | 462 | 468 |
| Verus + cvc5 | 275 | 281 |

The release labels Verus `assert forall` statements by probe evidence only,
where the paper assigns INST-forall to those that no probe explains, which
is where the INST and Other counts differ.

## Running the pipeline

Extraction and classification of a few programs, with Z3 (the commands the
release was checked with; outputs go under `work/`, which is gitignored):

```sh
# Dafny: extract the essential assertions of six programs, map their ASTs with the
# fork, classify them
uv run python -m solver_needs.dafny.extract \
    --programs 0078_1269_A 0012_1060_A 0031_1130_A \
               DB_Clover_only_once DB_Clover_count_lessthan DB_dafny-synthesis_task_id_627 \
    --out work/e2e/essential_dafny_z3.json --cache-dir work/e2e/extract_dafny_z3 --workers 6
uv run python -m solver_needs.dafny.shape work/e2e/essential_dafny_z3.json
uv run python -m solver_needs.dafny.classify \
    --dataset work/e2e/essential_dafny_z3.json --results-dir work/e2e/results_dafny_z3 --workers 6

# Verus: the same for seven programs
uv run python -m solver_needs.verus.extract \
    --programs 0052_12_A 0136_1411_A 0025_1096_A \
               Misc/basic_nonlinear Misc/trigger MBPP/task_id_605 MBPP/task_id_3 \
    --out work/e2e/essential_verus_z3.json --cache-dir work/e2e/verus_extract_z3 --workers 4
uv run python -m solver_needs.verus.classify \
    --dataset work/e2e/essential_verus_z3.json --results-dir work/e2e/results_verus_z3 --workers 4
```

Keys are carried over from the recorded dataset (`--previous`, default), so
the labels in `work/e2e/results_*/labels.json` can be compared with
`results/*/labels.json` key by key. Add `--solver cvc5` to every command for
the cvc5 configurations. Without `--programs` and `--out`, the extractors
process the whole corpora and overwrite the recorded datasets; without
`--dataset` and `--results-dir`, the classifiers process the recorded
datasets and write to `results/` (rows already in `results/<config>/rows/`
are skipped, `--keys` re-probes chosen rows, `--relabel` recomputes the
labels and `labels.json` from the stored evidence without solver runs).

Other entry points:

```sh
uv run python -m solver_needs.dafny.calibrate --solver z3|cvc5   # resource limits against the baselines
uv run python -m solver_needs.dafny.dafnybench --dafnybench DIR  # place the DB corpus from a DafnyBench checkout
```

## Definitions

**Resource limits.** Dafny with Z3: resource limit 10^9 (raw Z3 rlimit
units) per verify call, plus a 300 s wall-clock cap per call, and
verification restricted to the declaration enclosing the assertion. Dafny
with cvc5: 10^8 cvc5 resource units per check and a 60 s Dafny time limit.
Verus: its default `--rlimit 10`; removals that exhaust it are confirmed once
at `--rlimit 20`.

**Which assertions are candidates.** Every `assert` statement in statement
position, including `assert forall` and the assertions inside `assert ... by
{ }` bodies, each removed on its own; a statement is removed as a whole, by
character range, `by` block included. Dafny's labelled `assert L: E` is never
a candidate. The Rust macro `assert!` is never a candidate.

**Essentiality screen.** Only programs whose baseline verifies fully are
probed. A removal is verified (Dafny: the enclosing declaration; Verus: the
whole file, with the verdict read for the enclosing function). A failing
removal is re-verified under Boogie's second random seed (Dafny) and with
the statement replaced by an inert ghost declaration (`ghost var placeboTerm
:= 0;`, `let ghost placebo_term = 0int;`); a pass on either rerun marks the
assertion as brittle and excludes it. An exhausted budget on removal is
re-checked once at twice the limit, for the record. A Verus removal that no
longer compiles is excluded.

**Probe order.** FUEL (Verus only), INST, AX, NLA (Verus with Z3 only), then
Other; the first probe that restores verification decides the label. Every
family is still run on every assertion, so `categories` in `probes.json`
lists all that pass.

**INST probe.** Candidate terms come from splitting the assertion at
top-level Boolean operators and each atom at its comparison operator; every
operand and every maximal bracketed subterm is a candidate, excluding
literals, bare identifiers and anything containing a binder; membership
atoms are candidates as a whole. At most eight terms, in order of
appearance, plus the terms of the assertions inside a `by` body. Each term
is inserted on its own at the removal site as `ghost var seedTermN :=
<term>;` (`let ghost seed_termN = <term>;`), stopping at the first pass; if
none passes and at least two terms are valid, all are inserted together. The
label is INST-witness if a failing obligation contains an existential and
INST-forall otherwise. For a Verus `assert forall`, whose subterms all
mention the bound variable, the statement is instead replaced by `assert
forall ... by {}`; a pass is INST-forall.

**Equality-seed probe.** For each top-level equality `a == b` (at most
three), `ghost var eqTermN := (a == b);` (`let ghost eq_termN = (a =~= b);`)
at the removal site, stopping at the first pass. A pass is AX when one side
has collection type (sequence, set, multiset, map, string, or their `Keys`,
`Values`, `Items`; from the AST mapping when available, from the text
otherwise) and INST otherwise.

**AX probe.** Dafny: one law appended to the prelude of the Dafny in use,
ten preludes with one law each, never combined; the stripped program is
verified with that prelude, restricted to the enclosing declaration. The
laws (`solver_needs/dafny/laws.py`): take-take, take-append, take-full,
append-empty, take-build, split-concat, append-assoc, drop-append,
drop-build, drop-full. Verus: a module containing the law as a `broadcast
proof fn` with an explicit trigger is appended to the file and brought into
scope with `broadcast use` directly after `verus! {`
(`solver_needs/verus/laws.py`: subrange-full, push-subrange,
subrange-subrange, split-concat, add-subrange, subrange-push, add-empty,
subrange-empty, add-assoc).

**FUEL and NLA probes (Verus).** FUEL inserts `reveal_with_fuel(f, 20);` at
the removal site for each recursive `spec fn` the assertion mentions, one at
a time and then all together. NLA re-verifies the stripped program with
`--smt-option smt.arith.nl=true`; it is not run under cvc5.

## Data formats

`data/essential/*.json`: `toolchain` (versions and limits of the run),
`programs` (every corpus program with its baseline status and number of
asserts), `counts`, and `assertions`, one row per essential assertion with
`key`, `corpus`, `problem`, `source_path`, `line`, `end_line`, `text`, the
outcome of every screen run (`removal`, `removal_confirm`, `removal_seed2`
for Dafny, `placebo`) and `removal_errors`, the obligations that failed on
removal.

`results/<config>/probes.json`: one row per essential assertion with the
outcome of every probe (`seeds`, `eq_seeds`, `prelude_axioms` or `axioms`,
and for Verus `fuel`, `bridge`, `nla`), the assertion's `shape`, the
`categories` whose probe passed and the `label`. `labels.json` holds
`{key: label}` with the toolchain of the run.

`data/benchmark_sets/*.json`: `labels`, the mechanism of every benchmark
task; `fine_labels`, the same with the INST form; `aliases`, task
keys whose assertion carries another key in the recorded extraction.

## Recreating the datasets and results

With the toolchain installed, one extraction and one classification per
configuration recreate `data/essential/` and `results/` from the corpora
(the Dafny `shape` step needs the fork's AST mapping; without it the shape
comes from the text):

```sh
# Dafny
for solver in z3 cvc5; do
  uv run python -m solver_needs.dafny.extract --solver $solver --workers 6
  uv run python -m solver_needs.dafny.shape data/essential/essential_dafny_$solver.json
  uv run python -m solver_needs.dafny.classify --solver $solver --workers 6
done
# Verus
for solver in z3 cvc5; do
    uv run python -m solver_needs.verus.extract --solver $solver --workers 6
  uv run python -m solver_needs.verus.classify --solver $solver --workers 6
done
```

Per-program extraction records are cached under `work/` and per-row probe
results under `results/<config>/rows/`; delete them to probe again instead
of reusing them. Every verifier call is a separate process, so the run
scales with the number of workers; memory is not a constraint (a few hundred
MB per worker). On a Apple M4 with 6 workers full processing took roughly 30 min
for Verus and a few hours for Dafny.

## Licence

The code is released under the MIT licence (`LICENSE`). The generated
corpora CF-D and CF-V, the essential-assertion datasets, the benchmark sets
and the recorded results are released under CC BY 4.0 (`LICENSE-DATA`,
whose header gives the attribution chain from Codeforces through the
open-r1 datasets to the programs). The third-party corpora DB (Apache
License 2.0) and VB (MIT) keep their own licences, shipped as
`data/corpora/DB/LICENSE` and `data/corpora/VB/LICENSE`; the provenance of
every corpus is in `data/corpora/README.md`.
