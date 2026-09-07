# Proof

The definitions of the thesis, formalized in Lean 4 with Mathlib, and Theorem 1 — the soundness
of the CPN-to-mCRL2 translation — proved.

## Building it

```bash
cd Proof
lake exe cache get      # Mathlib binaries, rather than an hour of compiling
lake build
```

A successful build is the check: there are no `sorry`s, so anything that compiles is proved.

## The files

| File | Covers |
| --- | --- |
| [`Proof/CommonDefinitions.lean`](Proof/CommonDefinitions.lean) | Bags, expressions, bindings, evaluation (Definitions 1–2) |
| [`Proof/LabeledTransitionSystems.lean`](Proof/LabeledTransitionSystems.lean) | Labeled Transition Systems (Definition 3) |
| [`Proof/ColoredPetriNets.lean`](Proof/ColoredPetriNets.lean) | Colored Petri Nets, and the reachability graph (Definitions 4–9) |
| [`Proof/MCRL2.lean`](Proof/MCRL2.lean) | Linear Process Equations, and the translation (Definitions 13–15) |
| [`Proof/Bisimulation.lean`](Proof/Bisimulation.lean) | Bisimulation (Definitions 16–17) |
| [`Proof/Soundness.lean`](Proof/Soundness.lean) | **Theorem 1**: `CPN.bisimulation_transRel` and `CPN.bisimilar_toLPESemantics` |
| [`Examples/`](Examples) | The thesis's worked examples, checked |

## What it does and does not settle

It settles the mathematics: for a Colored Petri Net, the reachability graph of Definition 9 and
the LTS of the translated Linear Process Equation are bisimilar.

It says nothing about any program. Nothing here emits mCRL2 text, so nothing here can be
accepted or rejected by the mCRL2 tools.
[`Implementation/`](../Implementation/README.md) is where that link is made — the Lean
translator's [`Bridge/`](../Implementation/Lean/Bridge) package composes this theorem with a
proof about the term a printer actually prints.

[`Thesis/docs/LeanFormalization.md`](../Thesis/docs/LeanFormalization.md) is the honest audit of
this package: where it is faithful to the thesis definition by definition, which representation
choices were made, and the deviations and gaps — including the ones that are still open.
