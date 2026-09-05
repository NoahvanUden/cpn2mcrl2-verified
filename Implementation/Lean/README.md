# Verified translator #1, Lean 4

Milestone M3 of [`Implementation/docs/Plan.md`](../docs/Plan.md): a Colored Petri Net goes in
as a file, an mCRL2 specification comes out as text, and the term it prints is *proved* to
denote the $c_t$ and $g_t$ of Definition 14.

The package is self-contained. It does not depend on [`Proof/`](../../Proof) and it does not
depend on Mathlib; see [§5](#5-what-is-not-here) for what that costs.

---

## 1. Running it

```bash
cd Implementation/Lean
lake build
.lake/build/bin/cpn2mcrl2 fixtures/counter.cpn.json
```

That fixture is Example 3, and the output is Example 9:

```
act t1, t2, t3;

proc Spec(p1 : Bag(Int), p2 : Bag(Int), p3 : Bag(Int)) =
    sum h : Int . (({h: 1} <= p1) && true) -> t1 . Spec(((p1 - {h: 1}) + {:}), ((p2 - {:}) + {(h + 1): 1}), ((p3 - {:}) + {:}))
  + sum h : Int . (({h: 1} <= p2) && (h <= 3)) -> t2 . Spec(((p1 - {:}) + {h: 1}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {:}))
  + sum h : Int . (({h: 1} <= p2) && (3 < h)) -> t3 . Spec(((p1 - {:}) + {:}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {h: 1}));

init Spec({1: 1}, {:}, {:});
```

The `- {:}` and `+ {:}` at every place a transition does not touch are Definition 14 written
out literally; [`Target.md`](../docs/Target.md) §2 drops them when writing the same
specification by hand.

The harness of [`Target.md`](../docs/Target.md) §4 needs mCRL2 on the machine:

```bash
MCRL2_BIN=/path/to/mcrl2/bin bash scripts/check.sh
```

It translates every fixture, feeds it to `mcrl22lps`, checks the summand and parameter counts,
compares the LTS against a golden one with `ltscompare -ebisim`, and checks that every fixture
under `fixtures/rejected/` is refused.

---

## 2. The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right.

| File | What it holds | Tier |
| --- | --- | --- |
| [`Cpn2mCrl2/Util.lean`](Cpn2mCrl2/Util.lean) | duplicate removal, so that nothing outside the toolchain is needed | — |
| [`Cpn2mCrl2/Color.lean`](Cpn2mCrl2/Color.lean) | the color grammar of [`InputFormat.md`](../docs/InputFormat.md) §4.1, and values | — |
| [`Cpn2mCrl2/Bag.lean`](Cpn2mCrl2/Bag.lean) | Definition 1, finitely supported | — |
| [`Cpn2mCrl2/Expr.lean`](Cpn2mCrl2/Expr.lean) | `EXPR`, intrinsically typed, and **obligation 4** | — |
| [`Cpn2mCrl2/Typing.lean`](Cpn2mCrl2/Typing.lean) | evaluation preserves sorts | — |
| [`Cpn2mCrl2/Net.lean`](Cpn2mCrl2/Net.lean) | Definitions 4 and 5, and `Net.Valid` | T1 |
| [`Cpn2mCrl2/Semantics.lean`](Cpn2mCrl2/Semantics.lean) | Definitions 6 to 9 — the reference side | — |
| [`Cpn2mCrl2/Lpe.lean`](Cpn2mCrl2/Lpe.lean) | Definitions 13 and 15, syntactically | — |
| [`Cpn2mCrl2/Translate.lean`](Cpn2mCrl2/Translate.lean) | Definition 14 | — |
| [`Cpn2mCrl2/Correct.lean`](Cpn2mCrl2/Correct.lean) | **the T2 theorems** | T2 |
| [`Cpn2mCrl2/Print.lean`](Cpn2mCrl2/Print.lean) | the mCRL2 encoding of [`Target.md`](../docs/Target.md) §1 | — |
| [`Cpn2mCrl2/Json.lean`](Cpn2mCrl2/Json.lean) | the importer — **outside the trust boundary** | T1 |
| [`Main.lean`](Main.lean) | the command line | — |
| [`Examples/Counter.lean`](Examples/Counter.lean) | Examples 3, 4, 5 and 9, checked | — |

---

## 3. What is proved

The three theorems in [`Correct.lean`](Cpn2mCrl2/Correct.lean), for any net satisfying
`Net.Valid`:

| | |
| --- | --- |
| `Net.toLpe_cond` | the emitted condition holds under a marking and a binding exactly when Definition 6 says the binding element is enabled |
| `Net.toLpe_next` | the emitted next-state term for a place evaluates to the bag Definition 7 leaves there |
| `Net.toLpe_step` | consequently, the two transition relations agree |

[`Typing.lean`](Cpn2mCrl2/Typing.lean) adds one property that nothing else depends on but that
is the reason to believe `Expr.eval` is the semantics it is meant to be: under a well-typed
environment an expression of sort `τ` evaluates to a value of sort `τ`, so the `Color.junk`
fallback of `Expr.proj` is unreachable and `Value.asInt` and friends never misread a value.

`Proof/MCRL2.lean` proves the first two by `rfl`, and
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5 explains why that carries
so little:

> With the condition a proposition and the next state a Lean function, an `LPE` is not a piece of mCRL2 text.

Here neither is `rfl`. One side is a Lean predicate; the other is the *evaluation of a term*
the translation assembled. They agree only because the term was assembled out of the right
operations.

No `sorry`. The axioms are `propext`, `Quot.sound` and `Classical.choice`, which is what
`#print axioms` reports for anything built on Lean's standard library.

### 3.1 The five obligations of [`Plan.md`](../docs/Plan.md) §4

| # | Obligation | Where, and what it cost |
| --- | --- | --- |
| 1 | Sorts gain products, for $D$ and $H_t$ | **Not needed.** `ExprTy` keeps the two constructors `Proof/` gives it. mCRL2 already spells a tuple as a parameter list, so `Lpe.params` and `Summand.binder` are lists and their components are ordinary variables. The one change is that a variable may have *bag* sort, which is one constructor argument, not a type former. See [`Lpe.lean`](Cpn2mCrl2/Lpe.lean). |
| 2 | The Definition 14 operations join the language, each with an evaluation equation | `Expr.bagSubset`, `bagUnion`, `bagDiff`, `and`, `proj`, `mkRec`. The evaluation equations are the defining clauses of `Expr.eval`. Mechanical, as predicted. |
| 3 | The bounded quantifier is unfolded at translation time | `Net.condTerm` folds `Expr.andAll` over `pre(t)`. Nothing in `Expr` quantifies. Mechanical. |
| 4 | A substitution lemma | `Expr.eval_congr`, used as `Net.eval_toEnv`. [`Plan.md`](../docs/Plan.md) §7 rates this the project's high risk. It was not: see [§4.2](#42-scoping-is-extrinsic-which-is-what-makes-obligation-4-cheap). |
| 5 | `toLPE_cond` stops being `rfl` | `Net.toLpe_cond`. It follows from 2 and 4, as predicted. |

[`Plan.md`](../docs/Plan.md) §4.1 also requires bags to be finitely supported, and they are —
which is what makes `Bag.subsetB` a decision procedure and so lets $c_t$ be a
$\textit{Bool}$-valued term rather than a proposition.

> **Departure from Definition 1.** Definition 1 models a bag as a total function $S \to \mathbb{N}$, and `Proof/CommonDefinitions.lean` transcribes it so. `Bag` here is a list of coefficient entries, and `Bag.coeff` recovers the function. This is the departure [`Plan.md`](../docs/Plan.md) §4.1 asks for and says should be recorded.

---

## 4. Three design decisions

### 4.1 The product former is avoided rather than added

[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 calls the missing product
sort "the structural blocker", and the reference generator of
[`Target.md`](../docs/Target.md) §3 answers it with a `struct` per transition. Neither is
necessary, because the tuples of Definition 13 are only ever *bound*, never used as the sort of
a subterm: $d$ is the parameter list of `proc`, $h_t$ is the variable list of `sum`. Making
them binder lists keeps the data language exactly as `Proof/` has it.

Records are a different matter and do need a product in the data language — but
[`Color.lean`](Cpn2mCrl2/Color.lean) has had one from the start, because
[`InputFormat.md`](../docs/InputFormat.md) §4.1 puts records in the input grammar.

### 4.2 Scoping is extrinsic, which is what makes obligation 4 cheap

`Expr` is indexed by `ExprTy`, so a guard is boolean and an arc expression is a bag *by
construction* — checks 4 to 6 of [`InputFormat.md`](../docs/InputFormat.md) §4.3 hold for every
term that exists. It is **not** indexed by a typing context: a variable carries its name and
sort, and `Expr.ScopedIn` is a separate predicate.

That is the decision that made obligation 4 tractable. With intrinsic scoping, moving
$E(p,t)$ from the context $V$ into the summand's context — one place parameter per place
together with $\mathrm{Var}(t)$, which is generally *smaller* than $V$ — means re-indexing
every subterm through a strengthening lemma over dependent proofs. With extrinsic scoping the
translation moves the term by doing nothing to it, and the obligation becomes

```
Expr.eval_congr : (∀ p ∈ e.freeVars, env₁ p.2 p.1 = env₂ p.2 p.1) → eval e env₁ = eval e env₂
```

— one structural induction, no casts. Nothing is given up: scoping is still checked, at the
boundary where [`InputFormat.md`](../docs/InputFormat.md) §4.3 puts it.

### 4.3 Names are one namespace

> **Addition to the thesis.** Definition 4 requires $P \cap T = \emptyset$. `Net.Valid.namesDisjoint` also requires the names of $V$ to be distinct from those of $P$ and $T$, because the emitted `proc` binds a place parameter and the emitted `sum` binds a variable in the same mCRL2 scope.

The importer additionally refuses any identifier that is an mCRL2 keyword —
[`Target.md`](../docs/Target.md) §1 flags `val` — and refuses it rather than renaming it. A
name the user did not write is worse than an error.

Two smaller things worth knowing. The output is deterministic but the order of places,
transitions and variables follows the sorted order of the JSON object keys, not the order they
were written in. And a `sort` declaration may refer to a sort declared below it; mCRL2 accepts
that, and [`fixtures/jobs.cpn.json`](fixtures/jobs.cpn.json) exercises it.

---

## 5. What is not here

**The composition with Theorem 1 is not mechanized.** This is the one real gap.
[`Languages.md`](../docs/Languages.md) §3 makes it the reason Lean is translator #1:

> In Lean the translator's correctness theorem composes directly with `CPN.bisimulation_transRel`; nowhere else does it.

The composition holds mathematically — T2 here, T3 in [`Proof/`](../../Proof) — but no Lean
term connects them, because `Proof/` states everything over an abstract `ExprLang` and needs
Mathlib, and this package is Mathlib-free so that the trust boundary and the binary stay small.
Closing it is a bridge module that would: instantiate `ExprLang` with `Color`, `Value` and
`Expr`; relate `Bag` here to `Proof`'s `Bag S := S → ℕ` through `Bag.coeff`; build a
`CPN L P T` from a `Net` and its `Net.Valid`; and show `CPN.Enabled` and `CPN.fire` agree with
`Net.Enabled` and `Net.fire`. Then `CPN.bisimulation_transRel` applies and
`Net.toLpe_step` composes with it. Every definition here is named to line up with `Proof/` so
that this is instantiation rather than redesign.

**The list backend, and the refinement it needs.** Milestone M6.
[`Plan.md`](../docs/Plan.md) §5 is explicit that the bag translator comes first and that the
list encoding is "exactly as justified as the reference implementation's, which is to say not
at all". [`fixtures/multitoken.cpn.json`](fixtures/multitoken.cpn.json) is the net
[`Target.md`](../docs/Target.md) §4.1 asks for, so that when the second backend exists the
comparison is one `ltscompare` away.

**T0 and T4 are tested, never proved.** [`Plan.md`](../docs/Plan.md) §2 calls this "the honest
ceiling": whether `mcrl22lps` accepts the text, and whether what it reads back denotes the term
that was printed, would need a formalized mCRL2 grammar. `scripts/check.sh` runs the tool
instead.

**Importers.** Only the native format of [`InputFormat.md`](../docs/InputFormat.md) §4 is read.
PNML and the Model Checking Contest corpus are M7.

---

## 6. Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025. Definitions 1, 2, 4 to 9 and 13 to 15 are transcribed
  in [`Thesis/docs/`](../../Thesis/docs).
- [`Proof/`](../../Proof), where those definitions are formalized and Theorem 1 is proved.
- mCRL2 toolset 202307.1, which every claim in [`Target.md`](../docs/Target.md) and every run
  of `scripts/check.sh` is against. [mcrl2.org](https://www.mcrl2.org/)
