# Tests

Validating the three translators of [`Implementation/`](../Implementation/README.md) against a
reachability graph computed **outside** this repository.

The translators are already well tested against each other: all six emitted specifications —
three fixtures, two encodings — are byte-identical across the Lean, Dafny and OCaml
developments, and each is checked against a recorded LTS. Both of those oracles are internal.
Three implementations written by one person from one set of documents cannot detect a misreading
of Definition 14 that is *in* the documents. This directory is the outside opinion: a
third-party Petri net library builds the reachability graph, and the comparison is against
something whose semantics were fixed before this project existed.

## Running it

```bash
bash Tests/scripts/check.sh                  # the whole corpus, all four comparisons
python Tests/scripts/fuzz.py --runs=50       # random nets, shrunk to a minimal one on failure
python Tests/scripts/mcc.py <dir> --survey   # how much of a PNML corpus fits, and why not
```

You need the [mCRL2 toolset](https://www.mcrl2.org/) (set `MCRL2_BIN` if it is not in a standard
place), the three translators built, and the oracle in `Tests/.venv` (`python -m venv Tests/.venv`,
then `pip install snakes`). A translator that cannot be run is reported and excluded rather than
silently counted as agreeing.

`check.sh` prints one block per net and ends in `all green` or `FAILURES`.

## What is compared

| | |
| --- | --- |
| **A** | The three translators emit byte-identical text |
| **B** | The LTS of the emitted specification is bisimilar to the oracle's reachability graph |
| **B2** | And on the bag encoding, marking for marking — sharper than B, which only sees transition labels |
| **C** | The bag and list encodings are bisimilar to each other |
| **D** | Every net in `corpus/rejected/` is refused, by all three, for the stated reason |

Plus two checks needing no oracle: the linearized process has the expected shape, and the state
and edge counts match numbers written down by hand before either machine ran.

The oracle is [SNAKES](https://snakes.ibisc.univ-evry.fr/), but the harness depends on an
*interface* rather than on that library: anything that emits an `.aut` file with bare transition
labels can replace it. The corpus starts with thirteen tiny nets over `Bool` and enumerations,
where the state space is small by construction and every graph can be checked by hand; records
and integers come later.

**None of this proves anything.** Its value is what it could falsify — a shared misreading of
Definition 14, which byte-identity between three agreeing translators is structurally blind to.

## Contents

| File | What it covers |
| --- | --- |
| [`docs/Plan.md`](docs/Plan.md) | Why an external oracle, what it can and cannot establish, the four comparisons, and the milestones |
| [`docs/Oracle.md`](docs/Oracle.md) | The contract any oracle must satisfy, the SNAKES evaluation, and the alternatives if it stops fitting |
| [`docs/Corpus.md`](docs/Corpus.md) | The test nets, and why each one is there |
| [`docs/Findings.md`](docs/Findings.md) | **What building it found** — the most interesting file in this directory |

## Results

`check.sh` is green on 21 nets, in both encodings, across all three translators. The point of
the exercise: **all three recorded LTSs are confirmed by an implementation that never read this
thesis**, and two of them had never been checked against anything.

Four things it found, in [`docs/Findings.md`](docs/Findings.md):

- **Three checks that could not fail** (§1, §4, §11). `ltscompare` returns its verdict on stdout
  and exits 0 either way, so seven checks written as `if ltscompare ...` had been passing
  unconditionally; and a translator that cannot run writes no output file, which is exactly how
  the harness recognised a *correct refusal*. All were found by asking whether a check could be
  made to go red, not by running it.
- **One genuine translator defect** (§8), found by the random search: two enumerations sharing a
  constructor name produce text `mcrl22lps` refuses, and nothing in Definition 5 forbade the
  net. All three translators now reject it at the boundary.
- **One negative result** (§10): none of the Model Checking Contest's coloured models fits the
  expression language — 0 of 443 files, because every one uses cyclic enumerations.
- **Everything the oracle confirmed** (§9), which is the part that was the goal.

## Making sure it can fail

A check that cannot go red is worth nothing, and three of the ones here could not. The cheapest
way to confirm the harness is live is to break something and watch it complain:

- change a number in `corpus/expected.tsv` — the `by hand` line must go red for that net;
- make `oracle/adapters/snakes_adapter.py` ignore guards — legs B and B2 must go red, and name
  the markings they disagree about;
- point one of the `BIN_*` variables in `scripts/check.sh` at a nonexistent file — that
  translator must drop out of the summary, and out of leg D's refusers.

`fuzz.py` answers to the same three, and reports the failing seed with a shrunk net. If a
mutation you expect to break something leaves the run green, that is a finding.
