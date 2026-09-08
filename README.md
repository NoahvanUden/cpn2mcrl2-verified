# cpn2mcrl2-verified
[![CI](https://github.com/NoahvanUden/Cpn2mCrl2/actions/workflows/ci.yml/badge.svg)](https://github.com/NoahvanUden/Cpn2mCrl2/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

A sound translation from **Colored Petri Nets** to **mCRL2**, with the translation proved correct and the
proof connected to a program that producesl mCRL2 model..

The material comes from the MSc thesis *Model checking for analysis of BPMN models*, which
defines a translation from Colored Petri Nets, the formal semantics of the BPMN models used
in the Matala project at TNO-ESI and ASML, to mCRL2 models, and proves the two
bisimilar. A property checked with the mCRL2 model checker therefore holds of the mCRL2
specification if and only if it holds of the original model.

The repository holds five things: the thesis, notes transcribing its definitions, a Lean 4
formalization with the soundness theorem proved, three implementations of the translation, and
a test harness that checks them against a reachability graph computed outside this repository.

The formalization of the proofs of the thesis and the implementation are done using Claude Code.

## Contents

| Path | What it is |
| --- | --- |
| [`Thesis/Thesis.pdf`](Thesis/Thesis.pdf) | The thesis (76 pages) |
| [`Thesis/docs/`](Thesis/docs) | The definitions and proofs of the thesis, transcribed into Markdown, one formalism per file |
| [`Proof/`](Proof/README.md) | A Lean 4 / Mathlib formalization of those definitions, with Theorem 1 — the soundness theorem — proved |
| [`Implementation/`](Implementation/README.md) | Three translators, and the documents they were all written against |
| [`Tests/`](Tests/README.md) | Validation against a third-party Petri net tool, so that the translators are not only checked against each other |

The three translators share one specification and one native input format, and emit
byte-identical text:

| | Language | What is proved of it |
| --- | --- | --- |
| [`Implementation/Lean/`](Implementation/Lean/README.md) | Lean 4 | The emitted term denotes Definition 14, and — composed with Theorem 1 — an LTS bisimilar to the net's reachability graph |
| [`Implementation/Dafny/`](Implementation/Dafny/README.md) | Dafny | The same term-level statement, discharged by Z3 instead of by tactics |
| [`Implementation/OCaml/`](Implementation/OCaml/README.md) | OCaml | Nothing. Why not is the result that milestone delivers |
| [`Implementation/tools/`](Implementation/tools/README.md) | Python | A PNML importer, deliberately outside the trust boundary |

### The notes

| File | Covers | From |
| --- | --- | --- |
| [`CommonDefinitions.md`](Thesis/docs/CommonDefinitions.md) | Bags, expressions, bindings and evaluation (Definitions 1–2) | Chapter 2 |
| [`LabeledTransitionSystems.md`](Thesis/docs/LabeledTransitionSystems.md) | Labeled Transition Systems (Definition 3) | Chapter 2 |
| [`ColoredPetriNets.md`](Thesis/docs/ColoredPetriNets.md) | Colored Petri Nets — syntax, semantics, reachability graph (Definitions 4–9) | Chapter 3 |
| [`mCRL2.md`](Thesis/docs/mCRL2.md) | Linear Process Equations, the CPN→LPE translation, the modal μ-calculus (Definitions 13–15, 18) | Chapters 5–6 |
| [`Bisimiliarity.md`](Thesis/docs/Bisimiliarity.md) | Bisimulation, and the soundness proof (Definitions 16–17, Theorem 1) | Chapter 5.3 |
| [`LeanFormalization.md`](Thesis/docs/LeanFormalization.md) | How faithful [`Proof/`](Proof) is to the notes — deviations and gaps | — |

Each file keeps the thesis's numbering, so any statement can be traced back to the PDF. The
notes cover Chapters 2, 3, 5.1–5.3 and 6.1. Out of scope: BPMN itself (Chapter 4), the property
templates (Chapter 6.2–6.3), results (Chapter 7) and the case study (Chapter 8).

## Checking it yourself

To verify the soundness of the proof or test the implementation again [SNAKES](https://snakes.ibisc.univ-evry.fr/), run the following commands.
```bash
cd Proof && lake build                 # the formalization, Theorem 1 included
cd Implementation/Lean && lake build   # translator #1, and its proofs
bash Tests/scripts/check.sh            # all three translators against an external oracle
```

The last needs the [mCRL2 toolset](https://www.mcrl2.org/) and takes a few minutes; it compares
the emitted specifications against each other, against the mCRL2 tools, and against a
reachability graph built by [SNAKES](https://snakes.ibisc.univ-evry.fr/), a Petri net library
that knows nothing about this thesis. [`Tests/README.md`](Tests/README.md) says what each of
those comparisons can and cannot establish.

## Relationship to the thesis

The notes are a transcription, not a rewrite. Where they depart from the printed text — because
the thesis contains a slip, or because a definition needed a gap closed to be total — the change
is marked inline as `> **Deviation from the thesis.**` or `> **Addition to the thesis.**`, with
the printed version quoted.

## The thesis

> N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report,
> Eindhoven University of Technology, Department of Mathematics and Computer Science,
> Formal System Analysis, April 2025.
> Supervisors: Dr. Ir. Tim Willemse, Dr. Debjyoti Bera, Dr. Raúl Monti.

The code written for the thesis itself lives on the `mcrl2-model-checking` branch of the
[OfflineMBT repository](https://github.com/dbera/OfflineMBT/tree/mcrl2-model-checking), not
here.
