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

Milestones M0, M2, M3, M4 and M6 are done. [`Implementation/Lean/`](../Lean) is a Lean 4 translator
that reads the native CPN format of [`InputFormat.md`](InputFormat.md) §4, validates it,
builds the LPE of Definition 14 as *terms*, and prints the mCRL2 encoding of
[`Target.md`](Target.md) §1. Tier T2 is proved there: `Net.toLpe_cond` and `Net.toLpe_next`
are theorems rather than `rfl`, and `Net.toLpe_step` composes them. Tiers T0 and T4 are tested
by `scripts/check.sh` against mCRL2 202307.1 and are green on every fixture, including
Example 3, whose emitted specification reproduces the corrected seven-state chain of
Example 5.

M1 was skipped rather than done: the plan puts an unverified OCaml prototype first as an
oracle, and the Lean translator arrived before anything needed one. That left the M4 and M5
comparison without the differential oracle M1 was to provide — and M4 turned out not to need
one, because the two verified translators are each other's oracle. See below.

The composition of T2 with Theorem 1 — which [`Languages.md`](Languages.md) §3 makes the
reason Lean is first — is now a Lean term and not an argument in prose:
`Net.bisimilar_reachabilityGraph_emitted` in
[`Implementation/Lean/Bridge/`](../Lean/Bridge), a second, proof-only package so that the
translator itself stays Mathlib-free. For a CPN that passes the T1 validation, the
reachability graph of Definition 9 and the LTS denoted by the emitted specification are
bisimilar. Building it also found two places where the translator was less faithful than the
thesis — bindings were not typed, and type soundness assumed an unsatisfiable hypothesis —
both now fixed; see [`Implementation/Lean/README.md`](../Lean/README.md) §4.4.

**M6, tier T5.** The list backend of [`Plan.md`](Plan.md) §5 exists, behind `--list`, and the
refinement between it and the bag encoding is proved rather than assumed — which §5 called
"the largest unacknowledged gap in the project". Of the two refinements it separates, typing is
discharged by construction (this backend emits `List(C(p))`, one list sort per place at that
place's own color, rather than the reference generator's shared tagged union), and order is the
lemma: `Net.bisimilar_reachabilityGraph_emittedList` puts the fast output on exactly the
footing the slow one has. §5's prediction is visible in the fixtures — on
`multitoken.cpn.json`, the net [`Target.md`](Target.md) §4.1 asks for, the bag encoding gives
four states and the list encoding five, and `ltscompare -ebisim` reports them equal anyway.

**M4, the second implementation.** [`Implementation/Dafny/`](../Dafny) is the same translator
again, both backends, with T1, T2 and T5 discharged by Z3 instead of by tactics — 266 proof
obligations, no assumptions, checked for vacuity. It is what [`Languages.md`](Languages.md) §5
proposes the multi-language exercise for, and the answer it gives is mostly negative:
**obligations 1 to 3 were already free in Lean, so SMT had nothing to give away, and obligation
4 — the one [`Plan.md`](Plan.md) §7 rates the project's high risk — was free in both.** What
made obligation 4 cheap was a design decision rather than a language feature, namely that
scoping is extrinsic on both sides, and the plan's risk assessment was aimed at the wrong axis:
the cost was never dependent types against SMT, it was intrinsic against extrinsic *scoping*.
Where the two did separate is not on the plan's list at all — the T2 file is the one file that
is *smaller* in Dafny, 175 lines against 266, because Z3 needs none of the `show` steps Lean
needs to force definitional unfolding. See
[`Implementation/Dafny/README.md`](../Dafny/README.md) §5.

The differential test M1 was to supply comes free with the second implementation: all six
emitted specifications — three fixtures, two encodings — are **byte-identical** between the two
translators, which share no code and were written against these documents rather than against
each other. Dafny cannot compose with Theorem 1, and [`Languages.md`](Languages.md) §3 says so
in advance; what M4 buys is an independent proof of the same T2 statement and a differential
test with real teeth, not a doubled guarantee.

**M2, the formalization made syntactic.** This one was scheduled first and finished last, and
it is the only milestone that changes [`Proof/`](../../Proof) rather than adding to
[`Implementation/`](..). `CPN.toLPE` used to give $c_t$ and $g_t$ as Lean functions, so
`CPN.toLPE_cond` and `CPN.toLPE_next` held by `rfl` and nothing showed that Definition 14's
output is *expressible* at all. It now assembles them as terms — `CPN.Term` and `CPN.Cond`,
the state components together with $\land$, $\subseteq$, $\cup$ and $\setminus$ over the CPN's
own guard and arc expressions — and `CPN.LPESyntax.denote` evaluates the result into the `LPE`
of Definition 13. Both theorems are proved from the evaluation equations, and `rfl` proves
neither. That is item 2 of
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §7, closed for *every*
expression language `ExprLang` admits rather than for the one concrete language a translator
fixes.

It was done differently than [`Plan.md`](Plan.md) §6 wrote it, and the difference is the
result. `ExprTy` gained no product former, because Definition 13's tuples are only ever bound;
`ExprLang` gained no fields, because assuming the tool's language already has bag operations
fills a gap Chapter 2 leaves open, and giving the state components to it would have forced a
new component into Definition 5's tuple. And obligation 4, the substitution lemma
[`Plan.md`](Plan.md) §7 rates the project's high risk, is absent here too — for the third
time, and for the same reason both translators found: scoping is extrinsic, so moving an arc
expression into the summand's context is a different restriction of the same binding rather
than a re-indexing of the term. See
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.2.

Not done: M5, the third translator in OCaml with GOSPEL/Cameleer, and the PNML importers of
M7. See [`Implementation/Lean/README.md`](../Lean/README.md) §5 and
[`Plan.md`](Plan.md) §6.1.

Before any of that, M0's hand-written check that the target syntax is real: Example 9 of
[`mCRL2.md`](../../Thesis/docs/mCRL2.md) was written out as mCRL2 text in both encodings, both
were accepted by `mcrl22lps`, both produced the corrected seven-state chain of Example 5, and
`ltscompare` reported them strongly bisimilar. The transcripts are in
[`Target.md`](Target.md).
