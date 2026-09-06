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

Nothing is implemented. The plan is written and E0 has not started; E0 is M7 of
[`Implementation/docs/Plan.md`](../Implementation/docs/Plan.md) §6, which §6.2 there records as
the only open milestone in that directory.
