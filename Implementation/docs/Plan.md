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
an LPE denotes, not a piece of mCRL2 text. The consequence, which
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5 records as the second of
two limits, is that the formalization does not establish that $c_t$ and $g_t$ are *expressible*
in the mCRL2 data language at all, let alone that they print as a well-formed specification.

That is the gap an implementation lives in. A translator's whole job is the step the proof
currently skips: turning $c_t$ and $g_t$ into terms, and terms into text.

> **Half of that has since been closed inside `Proof/` itself**, by M2 — `CPN.LPESyntax` is Definition 14's output as syntax and `LPE` is what it denotes, so `toLPE_cond` and `toLPE_next` are theorems rather than `rfl`, for an arbitrary expression language. The half that remains is text, and it is where this directory still lives. See [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.2 and [§6.1](#61-where-the-order-above-did-not-survive) below.

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
| **T0** | The emitted text is accepted by `mcrl22lps` | Running the tool | Tested on every fixture, both encodings, all three translators |
| **T1** | The parsed structure is a CPN satisfying Definition 5 | Runtime validation, once at the boundary | Done three times (M3, M4, M5); in the first two the predicate checked is also the hypothesis the T2 proofs run on |
| **T2** | The emitted LPE term *denotes* the $c_t$ and $g_t$ of Definition 14 | Proof, in the implementation language | Done twice (M3, M4), and once in [`Proof/`](../../Proof) for an arbitrary expression language (M2) |
| **T3** | Definition 14's LPE is bisimilar to the reachability graph | Theorem 1, `CPN.bisimulation_transRel` | Proved. Composed with T2 in Lean only |
| **T4** | The text `mcrl22lps` reads back denotes the term that was emitted | Not provable without a formalized mCRL2 grammar | Tested only, by design |
| **T5** | The list encoding refines the bag encoding | Was unproved anywhere; required by the fast output | Proved twice (M6, M4); emitted a third time without proof (M5) |
| **T6** | The reachability graph the fixtures assert is the one an independent implementation computes | Testing, never proof — [`Tests/`](../../Tests/README.md) | Green on 21 nets; it confirmed all three goldens, two of which had never been checked |

**T2 composed with T3 is the theorem the project is for**: *the specification this program
prints denotes an LTS bisimilar to the CPN's reachability graph.* T3 was done before this
plan; T2 was the work, and the composition is
`Net.bisimilar_reachabilityGraph_emitted` in [`Implementation/Lean/Bridge/`](../Lean/Bridge).
It exists in Lean and nowhere else, because Theorem 1 is a Lean term.

T0 and T4 are the honest ceiling.
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 already ranks three
readings of "well-formed" and rules the third one out, on the grounds that an intrinsically
typed term language establishes well-typedness but never well-formedness of text. An
intrinsically typed AST plus a printer gets T2. Getting T4 would need a formalized mCRL2 grammar
and a parser correctness proof, which is a separate research project and is out of scope. It is
mitigated by running `mcrl22lps` in CI on every fixture, which is cheap and catches everything a
printer realistically gets wrong.

T5 was the interesting one, and [§5](#5-the-bag-versus-list-problem) treats it separately.

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

> **One of those five came true and four did not.** M2 made `finitePlaces` load-bearing in `Proof/` exactly as predicted — it is what `CPN.preList` enumerates — and §4.5 now records that it is no longer inert. `finiteV` was not needed, because $H_t$ is never enumerated, and the other three are needed only for emitting sort declarations, which is a translator's job and not `Proof/`'s. In the translators the side conditions land where this paragraph says: as T1 validation.

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
5. **`toLPE_cond` stops being `rfl`.** As things stand it holds definitionally, because both sides are
   transcriptions of one formula. Once `cond` is a term and `semantics` denotes it, the identity
   becomes a theorem proved from the evaluation equations of item 2. That is the point at which
   the translation acquires content beyond bookkeeping.

Obligation 4 is the risk. Obligations 1 to 3 are mechanical, and obligation 5 follows from them
together with 4.

**How that turned out.** Obligation 4 was not the risk, and obligation 1 was not needed at
all. Three independent developments — [`Implementation/Lean/`](../Lean),
[`Implementation/Dafny/`](../Dafny) and, for an arbitrary expression language,
[`Proof/`](../../Proof) — reached the same two conclusions. The tuple sorts of item 1 are only
ever *bound*, never the sort of a subterm, so a product former is not needed anywhere and the
ripple item 1 predicts into `varType` and the examples never happens. And item 4 is not a
proof: in all three, an expression is evaluated under a binding restricted to its own free
variables, so moving $E(p,t)$ into the summand's context is not a re-indexing of the term and
the obligation collapses. What made that so is a modelling decision rather than a language
feature — scoping is extrinsic in all three — which is where [§7](#7-risks)'s severity rating
was aimed wrongly. Items 2, 3 and 5 behaved as predicted.

### 4.1 One consequence to accept early

Bag inclusion on a bag modelled as a total function into $\mathbb{N}$ is a universally
quantified statement over the whole color set, which is not decidable for an arbitrary color
set. For $c_t$ to be a $\textit{Bool}$-valued *term* rather than a proposition, bags have to be
finitely supported and colors have to carry decidable equality.
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 spells this out and notes
that it reframes §4.10: `LPE.cond` landing in `Prop` was never a modelling convenience, it is a
consequence of how Definition 1 models a bag.

So the implementation's bags are finitely supported from the start. This is a further departure
from Definition 1 as printed, and it is recorded:
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §4.10 carries it, next to the
`Prop`-versus-$\textit{Bool}$ choice it is the explanation of, and
[`Implementation/Lean/README.md`](../Lean/README.md) §3.1 states it at the point where it is
made. [`Proof/`](../../Proof) does *not* make it — its `Bag` is still Definition 1's total
function — which is why the condition there stays a proposition even now that it is syntax.

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

**How it turned out.** M6 is done, and so is the same refinement in Dafny. Of the two
refinements above, *typing* was discharged by construction rather than proved: all three
translators emit `List(C(p))`, one list sort per place at that place's own color, instead of
the reference generator's shared tagged union, so there is no invariant left to preserve.
*Order* is the lemma, and it is proved — `Net.listRel` relates a list marking to a bag marking
when they give every token the same count, and nothing anywhere asks two list states to be
equal, which is exactly why production order does not matter. The prediction in the paragraph
above is visible in the fixtures: on `multitoken.cpn.json` the bag encoding gives four states
and the list encoding five, and `ltscompare -ebisim` reports them equal anyway. See
[`Implementation/Lean/README.md`](../Lean/README.md) §4.5.

Encouragingly, the two encodings can be compared mechanically: `ltscompare -ebisim` already
reports them strongly bisimilar on Example 9. See [`Target.md`](Target.md) §4. That is a test
and not a proof, but it makes the lemma cheap to *disprove* if it is false, which is the useful
direction to check first.

---

## 6. Milestones

| # | Milestone | Depends on | Tier reached | Status |
| --- | --- | --- | --- | --- |
| **M0** | Golden fixtures. Example 9 emitted by hand in both encodings, `mcrl22lps` green, LTS matching Example 5's corrected chain. | — | T0 | Done |
| **M1** | Unverified prototype. Native CPN JSON in, bag-encoded mCRL2 out. Harness green on Examples 3, 5 and 9. | M0, [`InputFormat.md`](InputFormat.md) | T0, T1 | Skipped |
| **M2** | The formalization made syntactic. `ExprTy` gains products, the expression language gains the Definition 14 operations with their evaluation equations, `toLPE_cond` becomes a theorem. | [§4](#4-the-proof-obligations-concretely) | T2, in Lean | Done, differently, and last |
| **M3** | Verified translator **#1, Lean 4**. Compiled to a binary, differential-tested against M1. | M2 | T2 with T3 | Done |
| **M4** | Verified translator **#2, Dafny**. Same specification, SMT-discharged. | M1, M3 | T2 with T3 | Done |
| **M5** | Verified translator **#3, OCaml with GOSPEL/Cameleer**. | M1, M3 | T0 only; T2 not reached | Done, as a negative result: the translator, and the reason it is not verified |
| **M6** | The bag-to-list refinement lemma, and the fast backend behind it. | M3, [§5](#5-the-bag-versus-list-problem) | T5 | Done |
| **M7** | PNML importers, and the Model Checking Contest corpus as a test set. | M3 (M1 is gone) | broader T1 | Importer done; the corpus run is not |

M0 through M3 are the spine. M4 and M5 are what the multiple languages are for: the same
obligations discharged by SMT automation and by a mainstream functional toolchain, which is the
comparison that makes building it three times worthwhile rather than merely repetitive.

### 6.1 Where the order above did not survive

Three things about that table are worth recording rather than quietly editing.

**M1 was skipped, and is now obsolete.** Its purpose was to be a differential oracle for M3
and M4, and the Lean translator arrived before anything needed one. M4 then supplied a better
oracle than M1 could have been: two *verified* translators, sharing no code, written against
these documents rather than against each other, and emitting byte-identical text on every
fixture. The one thing its absence still costs is M5, which
[`Languages.md`](Languages.md) §3 planned as "add contracts to the prototype" and which now
starts from nothing.

**M2 was not the long pole, and it came last.** It was scheduled first, and scheduled first
because obligation 4 was to be prototyped there before committing to three implementations —
the top row of [§7](#7-risks). Both translators were finished before it, so it prototyped
nothing; and when it was finally done, the obligation it was meant to de-risk cost nothing
there either. What it does still carry is the value it has on its own: it is item 2 of
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §7's list of gaps worth acting
on, and it closes that gap for an *arbitrary* expression language rather than for the one
concrete language a translator fixes.

**M2 was done differently than written.** `ExprTy` did not gain products, and `ExprLang` did
not gain the Definition 14 operations as fields; the operations became a small inductive syntax
layered over the assumed language instead. Neither of the two written changes turned out to be
necessary, and the second turned out to be undesirable.
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.2 is the record of why, and
[§4](#4-the-proof-obligations-concretely) above summarises the finding.

**M5 is done, and what it delivers is a negative result.**
[`Implementation/OCaml/`](../OCaml) is a third translator that emits text byte-identical to the
other two on every fixture in both encodings, and nothing about it is proved. Cameleer will not read it: `=` in program code is `int`
equality, six of the standard-library functions it uses are unknown symbols, `when` guards and
`include` are unsupported, it verifies one file at a time, and `open` on a module in that file
is read as a Why3 library import. Rewriting the core into the fragment it does accept cost
+280/−106 lines and bought no proof — and the rewrite is the measurement, because what it
removes is exactly the idiom that made OCaml worth trying. The work was stopped there rather
than carried through the specification layer, on the grounds that finishing would confirm
obligation 4 free a fourth time and change nothing else. See
[`Implementation/OCaml/README.md`](../OCaml/README.md) §4 and §6.1, the second of which records
what finishing would take.

### 6.2 What is left

**M7's importer is done and its corpus run is not.**
[`Implementation/tools/`](../tools/README.md) reads ISO/IEC 15909-2 Symmetric Nets and HLPNG
into the native format, once rather than three times, because it is outside the trust boundary;
`counter` and `multitoken` round-trip to byte-identical output through all three translators.
`jobs` does not, and that is a finding rather than a defect: standard PNML has no projection on
a product sort, so the same behaviour has to be written as a tuple pattern, which is a different
net with a bisimilar LTS. See [`tools/README.md`](../tools/README.md) §3.3.

What remains of M7 is the measurement §2.3 of [`InputFormat.md`](InputFormat.md) asks for — how
much of the Model Checking Contest corpus falls inside the expression language.
`Tests/scripts/mcc.py` performs it, bucketed by why each file was refused; the corpus itself has
not been fetched.

**A defect the corpus work found, which is open.** Two enumerations that share a constructor
name produce text `mcrl22lps` refuses, in all three translators, and nothing in Definition 5 or
in the T1 checks forbids the net. Fixing it means either narrowing the input at T1 or qualifying
constructor names in the printer, and both change all three translators. See
[`Tests/docs/Findings.md`](../../Tests/docs/Findings.md) §8.

**M5's proofs are closed rather than pending**, on the grounds
[`Implementation/OCaml/README.md`](../OCaml/README.md) §6.1 records. That section also records
what reopening them would take, so the decision is reversible if Cameleer changes.

**Everything else is done, and the differential test is the thing that keeps it honest.** All
six emitted specifications — three fixtures, two encodings — are byte-identical across the
three translators, and each directory's `scripts/check.sh` rechecks that together with T0 and
T4 against mCRL2 202307.1.

---

## 7. Risks

| Risk | Severity | Mitigation | Outcome |
| --- | --- | --- | --- |
| Obligation 4, the substitution lemma, is harder than it looks | High | Prototype it in Lean at M2, before committing to three implementations | **Rated wrongly.** It cost nothing in any of the three, and the mitigation never ran, because M2 came last. See [§4](#4-the-proof-obligations-concretely) |
| M2's `ExprTy` surgery ripples through `Examples/` | Low | §5.1 notes `CounterNet.Expr` is already a free-variable set paired with an evaluation function, so supplying the new fields is mechanical | **Rated correctly, for the wrong reason.** There was no `ExprTy` surgery at all; the ripple was six lemmas in `Examples/CounterNetLPE.lean`, one `rw` each |
| Cameleer is research-grade and may not carry M5 | Medium | Fall back to plain Why3, or to OCaml with the proof in Lean and the OCaml differential-tested | **Materialised, and the rating was right.** It does not carry M5. The fallback taken is the second one: the OCaml is unverified and differential-tested against both other translators |
| The list refinement of [§5](#5-the-bag-versus-list-problem) is false as stated | Medium | Cheap to falsify with `ltscompare` on a net holding several tokens in one place. Do it at M1, not M6 | **Did not materialise.** The refinement holds and is proved twice; `multitoken.cpn.json` is the falsification test and it is in the harness |
| T4 stays untestable in some corner | Low | `mcrl22lps` in CI on every fixture | **Held.** `scripts/check.sh` runs the toolset on every fixture, in both encodings |
| Scope creep into BPMN | High | Chapter 4 is out of scope for the notes and stays out of scope here. The input is a CPN | **Held.** The input is still a CPN |

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
