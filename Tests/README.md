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
| [`docs/Findings.md`](docs/Findings.md) | What building it found: two checks that could not fail, one translator defect, and E6's negative result |

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

**E0 to E6 are done.** `scripts/check.sh` is green on 21 nets — thirteen tier-1, five tier-2,
and the three existing fixtures — in both encodings, across all three translators, against
SNAKES 0.9.33 as the oracle.

What it found is in [`docs/Findings.md`](docs/Findings.md), and the first two are the ones worth
reading:

1. **`ltscompare` exits zero whether or not the LTSs are equal.** Seven checks across the three
   translator harnesses were written as `if ltscompare ...`, so the T4 golden-LTS check and the
   T5 refinement check had been passing unconditionally since they were written. Both claims
   turn out to be true; nothing was hiding behind it.
2. **`expected.tsv` is checked out with CRLF**, so the shape check compared `3` with `3\r` and
   failed on every fixture in the Lean and Dafny harnesses.

**A third check that could not fail, found by running the harness from WSL instead of Git
Bash:** the Lean and Dafny binaries are Windows `.exe`, WSL launches them and hands them paths
they cannot open, and they write nothing — which is exactly how leg D recognises a correct
refusal. All twelve rejected nets were reported as `refused by lean,dafny,ocaml` while not one
translator had processed anything. Leg D now demands a diagnostic, and every translator is
probed on a net that must translate before its verdicts are believed.
[`docs/Findings.md`](docs/Findings.md) §11.

One genuine defect, found by the random search: **two enumerations that share a constructor name
emit text `mcrl22lps` refuses**, in all three translators, and nothing in Definition 5 or in the
seven T1 checks forbade the net. The author chose to narrow the input, so all three now refuse it
as an eighth T1 check, and `corpus/rejected/shared-ctor.cpn.json` asserts that they do. See
[`docs/Findings.md`](docs/Findings.md) §8.

One negative result, which is E6: **none of the Model Checking Contest's coloured models fits
the expression language** — 0 of 443 files over a 30-model sample, because every coloured model
declares its colours as cyclic enumerations and not one uses the finite enumeration the native
format has. [`InputFormat.md`](../Implementation/docs/InputFormat.md) §2.3 asked for that number
before M7 was scheduled; it is now measured rather than assumed. See
[`docs/Findings.md`](docs/Findings.md) §10.

And the thing the directory exists for: **all three golden LTSs are confirmed by an
implementation that never read this thesis**, two of which had never been checked against
anything.

## Running it

```bash
bash Tests/scripts/check.sh                  # the four legs, over the whole corpus
python Tests/scripts/fuzz.py --runs=50      # random nets, shrunk on failure
python Tests/scripts/mcc.py <dir> --survey  # how much of a PNML corpus fits, and why not
```

Both run from Git Bash and from WSL alike. They have to work out how to call each translator,
because they are not all native to the same shell — the Lean and Dafny binaries are Windows
`.exe` and the OCaml one is ELF — so each is probed on a net that must translate before any
verdict is believed, and the summary names which ones actually ran and how. A translator that
cannot run takes part in no leg; if too few run, the run stops rather than reporting a green
corpus. `scripts/toolchain.py` holds that logic for the Python side and `check.sh` carries it
in shell. See [`docs/Findings.md`](docs/Findings.md) §11 for why it is not over-engineering:
the assumption it replaces turned a completely broken toolchain into a green leg D.

The oracle lives in `Tests/.venv` (`pip install snakes`), so nothing outside this directory
depends on Python. Set `MCRL2_BIN` if mCRL2 is not in a standard place, and `PYTHON` to point
at a different interpreter.

## Making sure it can fail

A check that cannot go red is worth nothing, and three of the ones here could not — see
§1, §4 and §11 of [`docs/Findings.md`](docs/Findings.md). The cheapest way to confirm the
harness is live is to break something and watch it complain:

- change a number in `corpus/expected.tsv` — the `by hand` line must go red for that net;
- make `oracle/adapters/snakes_adapter.py` ignore guards — legs B and B2 must go red, and
  name the markings they disagree about;
- point one of the `BIN_*` variables at a nonexistent file — that translator must drop out
  of the summary's "translators used", and out of leg D's refusers.

`fuzz.py` answers to the same three, and reports the failing seed with a shrunk net.

If a mutation you expect to break something leaves the run green, that is a finding.
