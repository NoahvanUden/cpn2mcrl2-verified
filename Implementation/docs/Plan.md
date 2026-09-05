# The plan

A verifiable CPN-to-mCRL2 translator, built more than once, against one specification.

---

## 1. What is already true, and what is missing

The soundness argument is finished. [`Proof/Soundness.lean`](../../Proof/Proof/Soundness.lean)
proves `CPN.bisimulation_transRel`: the reachability graph of a CPN (Definition 9) and the LTS
induced by the LPE that Definition 14 builds from it (Definition 15) are bisimilar. There is
no `sorry` and no non-standard axiom.

What that theorem is *about* is a mathematical function. `LPE.cond` is a Lean `Prop` and
`LPE.next` is a Lean function, so an `LPE` in the formalization is the transition-system schema
an LPE denotes — not a piece of mCRL2 text.
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5 states the consequence
plainly:

> So the formalization does not establish that the translation produces a well-formed mCRL2 specification at all.

That is the gap an implementation lives in. A translator's whole job is the step the proof
currently skips: turning $c_t$ and $g_t$ into terms, and terms into text.

### 1.1 The reference implementation

The thesis's own translator lives in the
[OfflineMBT repository](https://github.com/dbera/OfflineMBT/tree/mcrl2-model-checking), on the
`mcrl2-model-checking` branch, as Xtend sources under
`bundles/nl.asml.matala.product/src/nl/asml/matala/product/mcrl2/` — chiefly
`Cpn2mcrl2Generator.xtend`, `mCRL2Generator.xtend` and `TypesGenerator.xtend`, with the CPN
itself built in memory by `generator/PetriNet.xtend` from a Matala `.prj` model.

Three facts about it shape everything below:

- It is **unverified** Xtend, and there is no specification it is checked against.
- It emits **`List(token)` per place, over one tagged-union `token` sort**, not one bag per
  place over $C(p)$. That is not Definition 14. See [`Target.md`](Target.md) §3.
- There is **no external CPN file** anywhere in its pipeline. The CPN is an intermediate data
  structure. So the choice of input format is genuinely open, and is made in
  [`InputFormat.md`](InputFormat.md) rather than inherited.

---

## 2. What "verifiable" is allowed to mean

Not every link in the chain can be proved, and the plan is worth little if it pretends
otherwise. The chain is:

```
CPN file  --parse-->  CPN structure  --translate-->  LPE term  --print-->  mCRL2 text
                      (Definition 5)                (Definition 14)
                                                                              |
                                                                          mcrl22lps
                                                                              v
                                                                        LPS  -->  LTS
```

Each link admits a different kind of guarantee.

| Tier | Claim | Established by | Status |
| --- | --- | --- | --- |
| **T0** | The emitted text is accepted by `mcrl22lps` | Running the tool | Demonstrated by hand for Example 9 |
| **T1** | The parsed structure is a CPN satisfying Definition 5 | Runtime validation, once at the boundary | To build |
| **T2** | The emitted LPE term *denotes* the $c_t$ and $g_t$ of Definition 14 | Proof, in the implementation language | To build — this is the core |
| **T3** | Definition 14's LPE is bisimilar to the reachability graph | Theorem 1, `CPN.bisimulation_transRel` | Proved |
| **T4** | The text `mcrl22lps` reads back denotes the term that was emitted | Not provable without a formalized mCRL2 grammar | Test only |
| **T5** | The list encoding refines the bag encoding | Unproved anywhere; required by the fast output | Open |

**T2 composed with T3 is the theorem the project is for**: *the specification this program
prints denotes an LTS bisimilar to the CPN's reachability graph.* T3 is done. T2 is the work.

T0 and T4 are the honest ceiling.
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 already ranks three
readings of "well-formed" and rules the third one out, on the grounds that an intrinsically
typed term language establishes well-typedness but never well-formedness of text. An
intrinsically typed AST plus a printer gets T2. Getting T4 would need a formalized mCRL2 grammar
and a parser correctness proof, which is a separate research project and is out of scope. It is
mitigated by running `mcrl22lps` in CI on every fixture, which is cheap and catches everything a
printer realistically gets wrong.

T5 is the interesting one, and [§5](#5-the-bag-versus-list-problem) treats it separately.

---

## 3. Architecture

The standard verified-compiler shape: a small verified core with unverified adapters outside
the trust boundary.

```
      +---------------- outside the trust boundary ---------------+
      |                                                           |
PNML / .cpn / .prj  --importer-->   native CPN file (JSON)        |
      |                                     |                     |
      +-------------------------------------|---------------------+
                                            |  parse + validate  (T1)
      +---------------- verified core ------v---------------------+
      |                                                           |
      |  CPN structure  --translate-->  LPE term  --print-->  text |
      |  (Definition 5)      (T2)       (syntactic)                |
      +-------------------------------------|---------------------+
                                            |
                                       mcrl22lps   (T0 / T4: tested)
```

Three consequences worth stating up front.

**The Definition 5 side conditions stop being decorative.**
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §4.5 records that
`finitePlaces`, `finiteTransitions`, `finiteColors`, `finiteV`, `boolMem`, `colorMem` and
`varTypeMem` are declared and never used by any proof. §5.1 predicts that a syntactic
translation changes this, and it does: `finitePlaces` enumerates the components of $D$ and
unfolds the conjunction over $pre(t)$, `finiteV` enumerates $H_t$, and `finiteColors`,
`colorMem` and `varTypeMem` are what let the sort declarations be emitted at all. In an
implementation these become the validation performed at T1 and the hypotheses the T2 proof runs
on. `inArc` and `outArc` have to become decidable or finite so that $pre(t)$ computes.

**The expression language must be fixed and finite.** The notes assume one abstractly —
[`CommonDefinitions.md`](../../Thesis/docs/CommonDefinitions.md) §2 says only that the tools in
which the formalisms are modeled provide an expression language. A program cannot assume; it
must commit. [`InputFormat.md`](InputFormat.md) §4 fixes one.

**The printer is the only unverifiable part of the core, and it is the smallest.** Keeping the
LPE term intrinsically typed means the printer is a total function on a well-typed AST, with no
failure modes of its own beyond string formatting.

---

## 4. The proof obligations, concretely

T2 unfolds into five obligations. They are the same five that
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 lists, restated as work
items for a program rather than for the Lean development.

1. **Sorts gain products.** The Lean's `ExprTy` has exactly two constructors, `.color c` and
   `.bag c`, and `varType` maps a variable to a `Color`. In the LPE both $d : D$ and
   $h_t : H_t$ are variables of *tuple* sort, so neither is expressible. `ExprTy` gains a
   product former and `varType` becomes a map into `ExprTy Color`. In mCRL2 the tuple is a
   `struct`, which the reference generator already uses for its per-transition binding sorts.
2. **The operations Definition 14 uses become part of the language**, each with an evaluation
   equation: conjunction, bag $\subseteq$, $\setminus$, $\cup$, projection and tupling.
3. **The bounded quantifier is unfolded at translation time.** Since $pre(t)$ is a finite set of
   places known when the translator runs, the conjunction over it becomes a finite conjunction
   in the emitted text and needs no quantifier in the data language.
4. **A substitution lemma.** The free variables of $E(p,t)$ lie in $\mathrm{Var}(t)$; in the LPE
   they become components of $h_t$. Relating the value of $E(p,t)$ under a binding $b$ of the
   transition to the value of the translated term under $d \mapsto M$ and $h \mapsto b$ is the
   one genuinely new proof, and it is where the effort will actually go.
5. **`toLPE_cond` stops being `rfl`.** Today it holds definitionally, because both sides are
   transcriptions of one formula. Once `cond` is a term and `semantics` denotes it, the identity
   becomes a theorem proved from the evaluation equations of item 2. That is the point at which
   the translation acquires content beyond bookkeeping.

Obligation 4 is the risk. Obligations 1 to 3 are mechanical, and obligation 5 follows from them
together with 4.

### 4.1 One consequence to accept early

Bag inclusion on a bag modelled as a total function into $\mathbb{N}$ is a universally
quantified statement over the whole color set, which is not decidable for an arbitrary color
set. For $c_t$ to be a $\textit{Bool}$-valued *term* rather than a proposition, bags have to be
finitely supported and colors have to carry decidable equality.
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 spells this out and notes
that it reframes §4.10: `LPE.cond` landing in `Prop` was never a modelling convenience, it is a
consequence of how Definition 1 models a bag.

So the implementation's bags are finitely supported from the start. This is a further departure
from Definition 1 as printed, and should be recorded in
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §4 alongside §4.1 to §4.3 when
it is made.

---

## 5. The bag-versus-list problem

This is the largest unacknowledged gap in the project, and it is worth separating from
everything above because it is the one place that needs more mathematics rather than more
engineering.

Definition 14 stores one **bag** per place. [`mCRL2.md`](../../Thesis/docs/mCRL2.md) §4.1
reports that this is slow, and measures it on the thesis's own benchmark:

| Marking representation | Average time |
| --- | --- |
| `Bag` | 67 seconds |
| `FBag` | 60 seconds |
| `List` | 9 seconds |

The reference generator therefore emits `List(token)`. That is a sevenfold speedup, and it is
also a departure from the object Theorem 1 is about. Two refinements separate them.

**Order.** A list-encoded marking is a *representative* of a bag, and the translation must be
invariant under which representative it holds. This is not obvious: appending a produced token
at the end while removing the first match on consumption means two orders of production give two
distinct list states with the same underlying bag. Those states should be bisimilar, but they
are not equal — so the induced LTS has strictly more states than the reachability graph, and
bisimilarity holds where isomorphism fails. That is a provable lemma. Nobody has proved it.

**Typing.** Definition 5 requires $E(p,t)$ to land in $C(p)_{\mathrm{MS}}$, one color set per
place. A single tagged-union `token` sort shared by every place discards that, so nothing in the
emitted specification prevents a place from holding a token of the wrong tag. Either the
translation preserves a well-typedness invariant — provable, and worth proving — or the
guarantee is simply weaker than Definition 5's.

**How to sequence it.** Build the bag translator first. It is what Theorem 1 covers, it is what
T2 can be proved about today, and its output is a correct baseline. Add the list encoding as a
*second* backend behind the same T2 interface, and treat the refinement as milestone M6. Until
that lemma exists, the fast output is exactly as justified as the reference implementation's,
which is to say not at all.

Encouragingly, the two encodings can be compared mechanically: `ltscompare -ebisim` already
reports them strongly bisimilar on Example 9. See [`Target.md`](Target.md) §4. That is a test
and not a proof, but it makes the lemma cheap to *disprove* if it is false, which is the useful
direction to check first.

---

## 6. Milestones

| # | Milestone | Depends on | Tier reached |
| --- | --- | --- | --- |
| **M0** | Golden fixtures. Example 9 emitted by hand in both encodings, `mcrl22lps` green, LTS matching Example 5's corrected chain. | — | T0 |
| **M1** | Unverified prototype. Native CPN JSON in, bag-encoded mCRL2 out. Harness green on Examples 3, 5 and 9. | M0, [`InputFormat.md`](InputFormat.md) | T0, T1 |
| **M2** | The formalization made syntactic. `ExprTy` gains products, the expression language gains the Definition 14 operations with their evaluation equations, `toLPE_cond` becomes a theorem. | [§4](#4-the-proof-obligations-concretely) | T2, in Lean |
| **M3** | Verified translator **#1, Lean 4**. Compiled to a binary, differential-tested against M1. | M2 | T2 with T3 |
| **M4** | Verified translator **#2, Dafny**. Same specification, SMT-discharged. | M1, M3 | T2 with T3 |
| **M5** | Verified translator **#3, OCaml with GOSPEL/Cameleer**. | M1, M3 | T2 with T3 |
| **M6** | The bag-to-list refinement lemma, and the fast backend behind it. | M3, [§5](#5-the-bag-versus-list-problem) | T5 |
| **M7** | PNML importers, and the Model Checking Contest corpus as a test set. | M1 | broader T1 |

M0 through M3 are the spine. M4 and M5 are what the multiple languages are for: the same
obligations discharged by SMT automation and by a mainstream functional toolchain, which is the
comparison that makes building it three times worthwhile rather than merely repetitive.

M2 is the long pole. It is also the milestone that is valuable on its own even if no translator
is ever finished, because it is item 2 of
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §7's list of gaps worth acting
on.

---

## 7. Risks

| Risk | Severity | Mitigation |
| --- | --- | --- |
| Obligation 4, the substitution lemma, is harder than it looks | High | Prototype it in Lean at M2, before committing to three implementations |
| M2's `ExprTy` surgery ripples through `Examples/` | Low | §5.1 notes `CounterNet.Expr` is already a free-variable set paired with an evaluation function, so supplying the new fields is mechanical |
| Cameleer is research-grade and may not carry M5 | Medium | Fall back to plain Why3, or to OCaml with the proof in Lean and the OCaml differential-tested |
| The list refinement of [§5](#5-the-bag-versus-list-problem) is false as stated | Medium | Cheap to falsify with `ltscompare` on a net holding several tokens in one place. Do it at M1, not M6 |
| T4 stays untestable in some corner | Low | `mcrl22lps` in CI on every fixture |
| Scope creep into BPMN | High | Chapter 4 is out of scope for the notes and stays out of scope here. The input is a CPN |

---

## 8. What this does not cover

- **BPMN to CPN.** Chapter 4 of the thesis, out of scope for
  [`Thesis/docs/`](../../Thesis/docs) and out of scope here.
- **Property templates and the model-checking pipeline.** Chapters 6.2 to 6.3 and 7. Note that
  Definition 14 emits actions with *no parameters*, and
  [`mCRL2.md`](../../Thesis/docs/mCRL2.md) §1.3 records that parameters are reintroduced only
  where a property needs data exposed. Supporting the templates therefore needs material that
  has not been extracted from the PDF yet.
- **A verified `mcrl22lps`.** T4 is tested, never proved.
- **Semantics for the modal $\mu$-calculus.** `MuFormula` is syntax only, in the Lean and here.

---

## Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025. Definitions 5, 9, 13 to 17 and Theorem 1 are transcribed
  in [`Thesis/docs/`](../../Thesis/docs).
- The reference implementation:
  [OfflineMBT, branch `mcrl2-model-checking`](https://github.com/dbera/OfflineMBT/tree/mcrl2-model-checking),
  under `bundles/nl.asml.matala.product/src/nl/asml/matala/product/mcrl2/`.
- mCRL2 toolset 202307.1. [mcrl2.org](https://www.mcrl2.org/)
