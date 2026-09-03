# Cpn2mCrl2

Reference material for translating **Colored Petri Nets to mCRL2**, drawn from the MSc thesis
*Model checking for analysis of BPMN models*.

The thesis defines a translation from Colored Petri Nets (the formal semantics of the BPMN
models used in the Matala project at TNO-ESI/ASML) to mCRL2 Linear Process Equations, and
proves the two are bisimilar — so a property checked with the mCRL2 model checker holds for
the mCRL2 specification if and only if it holds for the original BPMN model.

This repository holds the thesis itself and a set of Markdown notes that extract the
formalisms it defines into a form that is easier to work from than the PDF.

## Contents

| Path | What it is |
| --- | --- |
| [`Thesis/Thesis.pdf`](Thesis/Thesis.pdf) | The thesis (76 pages) |
| [`Thesis/docs/`](Thesis/docs) | Per-formalism notes extracted from the thesis |
| [`Proof/`](Proof) | A Lean 4 / Mathlib formalization of the definitions in the notes |

### The notes

| File | Covers | From |
| --- | --- | --- |
| [`CommonDefinitions.md`](Thesis/docs/CommonDefinitions.md) | Bags, expressions, bindings and evaluation (Definitions 1–2) | Chapter 2 |
| [`LabeledTransitionSystems.md`](Thesis/docs/LabeledTransitionSystems.md) | Labeled Transition Systems (Definition 3) | Chapter 2 |
| [`ColoredPetriNets.md`](Thesis/docs/ColoredPetriNets.md) | Petri Nets and Colored Petri Nets — syntax, semantics, reachability graph (Definitions 4–9) | Chapter 3 |
| [`mCRL2.md`](Thesis/docs/mCRL2.md) | Linear Process Equations, the CPN→LPE translation, LPE semantics, the modal μ-calculus, tooling (Definitions 13–15, 18) | Chapters 5–6 |
| [`Bisimiliarity.md`](Thesis/docs/Bisimiliarity.md) | Bisimulation, the relation between a CPN and its translation, and the soundness proof (Definitions 16–17, Theorem 1) | Chapter 5.3 |
| [`LeanFormalization.md`](Thesis/docs/LeanFormalization.md) | How faithful the Lean formalization in [`Proof/`](Proof) is to these notes — remarks, deviations and gaps | — |

Each file states the syntax and semantics of one formalism, keeps the thesis's definition
numbering so anything can be traced back to the PDF, cross-links to the others, and ends with
the bibliography entries the thesis cites for that material.

The notes cover Chapters 2, 3, 5.1–5.3 and 6.1 in full. Out of scope: BPMN itself (Chapter 4),
related work and the property templates (Chapter 6.2–6.3, Appendix B), presentation of
model-checking results (Chapter 7), and the case study (Chapter 8).

## Relationship to the thesis

The notes are a transcription, not a rewrite. Where they depart from the printed text — either
because the thesis contains a slip, or because a definition needed a gap closed to be total —
the change is called out inline:

- `> **Deviation from the thesis.**` — the printed version is stated, then what was changed and why.
- `> **Addition to the thesis.**` — a convention not in the thesis at all.

One deviation is intentionally left unmarked: Definition 9 is written `S = {M₀} ∪ R(M₀)`
where the thesis writes `M₀ ∪ R(M₀)`, unioning an element with a set.

## The thesis

> N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report,
> Eindhoven University of Technology, Department of Mathematics and Computer Science,
> Formal System Analysis, April 2025.
> Supervisors: Dr. Ir. Tim Willemse, Dr. Debjyoti Bera, Dr. Raúl Monti.

The code written for the thesis lives on the `mcrl2-model-checking` branch of the
[OfflineMBT repository](https://github.com/dbera/OfflineMBT/tree/mcrl2-model-checking), not
in this repository.
