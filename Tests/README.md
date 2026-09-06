# Tests

Validating the three translators of [`Implementation/`](../Implementation/README.md) against a
reachability graph computed outside this repository.

The translators are well tested against each other: all six emitted specifications — three
fixtures, two encodings — are byte-identical across the Lean, Dafny and OCaml developments, and
each is checked against a recorded golden LTS with `ltscompare`. Both of those oracles are
internal. Three implementations written by one person from one set of documents cannot detect a
misreading of Definition 14 that is in the documents, and two of the three golden LTSs were
derived by hand in the same commit as the harness that checks them.

This directory is the outside opinion: a third-party Petri net tool builds the reachability graph,
and the comparison is against something whose semantics were fixed before this project existed.

## Contents

| File | What it covers |
| --- | --- |
| [`docs/Plan.md`](docs/Plan.md) | Why an external oracle, what it can and cannot establish, why M7 comes first, the four comparison legs, and milestones E0 to E6 |
| [`docs/Oracle.md`](docs/Oracle.md) | The contract any oracle must satisfy, the SNAKES evaluation, and the ordered alternatives if it does not fit |
| [`docs/Corpus.md`](docs/Corpus.md) | The test nets: thirteen tiny ones over `Bool` and enumerations first, then records, then the integers |

## The short version

1. **M7 first.** With a PNML importer the corpus is a standard format that both sides read
   independently, and the bridge program leaves the test's trust boundary. Without it, the thing
   that feeds the oracle is a program written here, which is the one component whose bugs can
   produce a false pass.
2. **The oracle is an interface, not a library.** Anything that emits an `.aut` file with bare
   transition labels plugs in. SNAKES is the first candidate and not the plan; if it does not fit,
   [`docs/Oracle.md`](docs/Oracle.md) §4 says what to try next, in order.
3. **Finite colours first.** `Bool` and enumerations make the state space small by construction,
   which is a better defence against explosion than any cap. `Int` arrives in tier 3, always
   behind a bounding guard.
4. **It proves nothing.** Its value is in what it could falsify — a shared misreading of
   Definition 14, which byte-identity between three agreeing translators is structurally blind to.

## Status

**E0 to E5 are done; E6 has its tool and not its corpus.** `scripts/check.sh` is green on 21
nets — thirteen tier-1, five tier-2, and the three existing fixtures — in both encodings, across
all three translators, against SNAKES 0.9.33 as the oracle.

What it found is in [`docs/Findings.md`](docs/Findings.md), and the first two are the ones worth
reading:

1. **`ltscompare` exits zero whether or not the LTSs are equal.** Seven checks across the three
   translator harnesses were written as `if ltscompare ...`, so the T4 golden-LTS check and the
   T5 refinement check had been passing unconditionally since they were written. Both claims
   turn out to be true; nothing was hiding behind it.
2. **`expected.tsv` is checked out with CRLF**, so the shape check compared `3` with `3\r` and
   failed on every fixture in the Lean and Dafny harnesses.

One open defect, found by the random search and not fixed here because the fix is a decision
about the project rather than about this directory: **two enumerations that share a constructor
name emit text `mcrl22lps` refuses**, in all three translators, and nothing in Definition 5 or
in the T1 checks forbids the net. See [`docs/Findings.md`](docs/Findings.md) §8, and
`corpus/known-failing/shared-ctor.cpn.json`.

And the thing the directory exists for: **all three golden LTSs are confirmed by an
implementation that never read this thesis**, two of which had never been checked against
anything.

## Running it

```bash
bash Tests/scripts/check.sh              # the four legs, over the whole corpus
python Tests/scripts/fuzz.py --runs=50   # random nets, shrunk on failure
python Tests/scripts/mcc.py <dir>        # how much of a PNML corpus fits
```

The oracle lives in `Tests/.venv` (`pip install snakes`), so nothing outside this directory
depends on Python. The OCaml translator is a Linux binary here and is run through `wsl.exe`;
when neither works the harness reports leg A as comparing two translators rather than failing.
