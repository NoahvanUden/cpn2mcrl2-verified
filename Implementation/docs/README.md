# Implementation

A verifiable translation from Colored Petri Nets to mCRL2, implemented several times over in
languages with different proof technology, against one shared specification.

The mathematics is settled: [`Thesis/docs/`](../../Thesis/docs) transcribes Definitions 1–18
and Theorem 1 from the thesis, and [`Proof/`](../../Proof) formalizes them in Lean 4 with the
soundness theorem fully proved. What does not exist anywhere — not in the thesis, not in the
Lean, and not in the reference implementation — is a link between that proof and a program
that actually emits mCRL2 text. [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md)
§5 says so directly:

> Separately, and whatever is done about the two above: nothing here connects the Lean to the translation as it is actually implemented.

Closing that link is what this directory is for.

## Contents

| File | What it covers |
| --- | --- |
| [`Plan.md`](Plan.md) | The goal, what "verifiable" is allowed to mean here, the architecture, the proof obligations and the milestones |
| [`InputFormat.md`](InputFormat.md) | Which CPN interchange formats exist, which one the verified core consumes, and the expression language it fixes |
| [`Target.md`](Target.md) | The mCRL2 output: validated syntax, the encoding the reference tool actually emits, and the differential-testing harness |
| [`Languages.md`](Languages.md) | Dafny, Lean, OCaml/OxCaml, F\*, Why3, Rocq, Isabelle, Rust — scored against the obligations in `Plan.md` |

## The short version

Read [`Plan.md`](Plan.md) for the argument. Its three conclusions:

1. **The verified core is a printer, not a solver.** Theorem 1 already covers the semantic
   content. What an implementation adds is the syntactic layer: that the term it emits
   *denotes* the $c_t$ and $g_t$ of Definition 14. That is exactly the work
   [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 sets out, moved into
   a program.
2. **The deployed translation is two unproved refinements away from Definition 14.** The
   reference generator emits `List(token)` over a single tagged-union sort, where Definition 14
   says one bag per place over $C(p)$. Neither refinement is justified anywhere. See
   [`Target.md`](Target.md) §3.
3. **The end-to-end check is cheap and already works.** `ltscompare -ebisim` between the
   independently generated reachability graph and the LTS of the emitted specification is
   Theorem 1 tested on concrete instances. See [`Target.md`](Target.md) §4.

## Status

Milestone M0 is done, and so is M3: [`Implementation/Lean/`](../Lean) is a Lean 4 translator
that reads the native CPN format of [`InputFormat.md`](InputFormat.md) §4, validates it,
builds the LPE of Definition 14 as *terms*, and prints the mCRL2 encoding of
[`Target.md`](Target.md) §1. Tier T2 is proved there: `Net.toLpe_cond` and `Net.toLpe_next`
are theorems rather than `rfl`, and `Net.toLpe_step` composes them. Tiers T0 and T4 are tested
by `scripts/check.sh` against mCRL2 202307.1 and are green on every fixture, including
Example 3, whose emitted specification reproduces the corrected seven-state chain of
Example 5.

M1 was skipped rather than done: the plan puts an unverified OCaml prototype first as an
oracle, and the Lean translator arrived before anything needed one. That leaves the M4 and M5
comparison without the differential oracle M1 was to provide.

The composition of T2 with Theorem 1 — which [`Languages.md`](Languages.md) §3 makes the
reason Lean is first — is now a Lean term and not an argument in prose:
`Net.bisimilar_reachabilityGraph_emitted` in
[`Implementation/Lean/Bridge/`](../Lean/Bridge), a second, proof-only package so that the
translator itself stays Mathlib-free. For a CPN that passes the T1 validation, the
reachability graph of Definition 9 and the LTS denoted by the emitted specification are
bisimilar. Building it also found two places where the translator was less faithful than the
thesis — bindings were not typed, and type soundness assumed an unsatisfiable hypothesis —
both now fixed; see [`Implementation/Lean/README.md`](../Lean/README.md) §4.4.

Not done: the list backend and the refinement of [`Plan.md`](Plan.md) §5, which is M6, and the
PNML importers of M7. Both are set out in
[`Implementation/Lean/README.md`](../Lean/README.md) §5.

Before any of that, M0's hand-written check that the target syntax is real: Example 9 of
[`mCRL2.md`](../../Thesis/docs/mCRL2.md) was written out as mCRL2 text in both encodings, both
were accepted by `mcrl22lps`, both produced the corrected seven-state chain of Example 5, and
`ltscompare` reported them strongly bisimilar. The transcripts are in
[`Target.md`](Target.md).
