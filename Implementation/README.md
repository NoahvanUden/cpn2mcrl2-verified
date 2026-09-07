# Implementation

The same translation from Colored Petri Nets to mCRL2, written three times over in languages
with different proof technology, against one shared specification.

The mathematics was already settled: [`Thesis/docs/`](../Thesis/docs) transcribes the
definitions and [`Proof/`](../Proof/README.md) formalizes them in Lean with the soundness
theorem proved. What did not exist was a link between that proof and a program that emits mCRL2
text — [`LeanFormalization.md`](../Thesis/docs/LeanFormalization.md) §5 says so directly:

> Separately, and whatever is done about the two above: nothing here connects the Lean to the translation as it is actually implemented.

Closing that link is what this directory is for.

## The translators

Each reads the native CPN format of [`InputFormat.md`](docs/InputFormat.md) §4 and prints the
mCRL2 encoding of [`Target.md`](docs/Target.md) §1, in two encodings: one `Bag` per place, which
is Definition 14 literally, and one `List` per place, which is faster and is proved to refine it.

| Directory | Language | What is proved of it |
| --- | --- | --- |
| [`Lean/`](Lean/README.md) | Lean 4 | The emitted term denotes the $c_t$ and $g_t$ of Definition 14, and — composed with Theorem 1 in a separate `Bridge` package — an LTS bisimilar to the net's reachability graph |
| [`Dafny/`](Dafny/README.md) | Dafny | The same term-level statement, discharged by Z3 instead of by tactics. It cannot compose with Theorem 1, which is a Lean term |
| [`OCaml/`](OCaml/README.md) | OCaml | Nothing, and why not is the result. Cameleer will not read code written the way one would write it |
| [`tools/`](tools/README.md) | Python | A PNML importer. Unverified on purpose: an XML parser has no business inside the trust boundary |

**All six emitted specifications — three fixtures, two encodings — are byte-identical across the
three translators**, which share no code and were written against the documents below rather
than against each other. Each directory's `scripts/check.sh` rechecks that on every run, along
with feeding the output to the mCRL2 toolset.

## The documents they were written against

| File | What it covers |
| --- | --- |
| [`docs/Plan.md`](docs/Plan.md) | What "verifiable" is allowed to mean here, the architecture, the proof obligations, and the milestones with their status |
| [`docs/InputFormat.md`](docs/InputFormat.md) | Which CPN interchange formats exist, which one the verified core consumes, and the expression language it fixes |
| [`docs/Target.md`](docs/Target.md) | The mCRL2 output: the encoding, and the differential-testing harness |
| [`docs/Languages.md`](docs/Languages.md) | Dafny, Lean, OCaml, F\*, Why3, Rocq, Isabelle and Rust scored against those obligations — and, in §5, what building it three times actually showed |

## What is claimed, and what is only tested

[`Plan.md`](docs/Plan.md) §2 fixes a vocabulary for this, used throughout the repository:

| | |
| --- | --- |
| **T0** | `mcrl22lps` accepts the emitted text. Tested |
| **T1** | The input really is a CPN — the validation at the boundary. Proved |
| **T2** | The emitted term *denotes* Definition 14's $c_t$ and $g_t$. Proved, in Lean and in Dafny |
| **T3** | Theorem 1, composed with T2. A Lean term, in [`Lean/Bridge/`](Lean/Bridge) |
| **T4** | What `mcrl22lps` reads back denotes what was printed. **Not proved** — it would need a formalized mCRL2 grammar. Tested against a recorded LTS instead |
| **T5** | The list encoding refines the bag encoding. Proved |

T0 and T4 are the ceiling: they are about a tool this repository does not formalize, so they are
tested by running it. [`Tests/`](../Tests/README.md) exists because testing against oneself is
weak evidence, and adds a reachability graph computed by an unrelated Petri net library.

## Status

Milestones M0 and M2 through M6 are done; see [`Plan.md`](docs/Plan.md) §6 for the table and the
account of where the plan did not survive contact. Three results are worth knowing before
reading anything else:

- **The multi-language comparison came out mostly negative.** Obligations 1 to 3 were free in
  every technology, and obligation 4 — which [`Plan.md`](docs/Plan.md) §7 rated the project's
  high risk — was free in all three. What made it cheap was a design decision, not a language
  feature: scoping is extrinsic on every side. [`Dafny/Notes.md`](Dafny/Notes.md) §5.
- **M5 is a negative result.** OCaml was picked because Cameleer promises verified code that is
  also code somebody would have written anyway. It cannot read such code; rewriting the core
  into the fragment it accepts cost +280/−106 lines and bought no proof.
  [`OCaml/Notes.md`](OCaml/Notes.md).
- **M7's corpus turned out to be empty.** The importer works, but 0 of 443 Model Checking
  Contest files fall inside the expression language, because every coloured model uses cyclic
  enumerations. [`Tests/docs/Findings.md`](../Tests/docs/Findings.md) §10.
