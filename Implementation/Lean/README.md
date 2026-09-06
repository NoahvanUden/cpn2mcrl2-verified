# Verified translator #1, Lean 4

Milestones M3 and M6 of [`Implementation/docs/Plan.md`](../docs/Plan.md): a Colored Petri Net
goes in as a file, an mCRL2 specification comes out as text, and the term it prints is *proved*
to denote the $c_t$ and $g_t$ of Definition 14 — and, composed with Theorem 1, to denote an LTS
bisimilar to the CPN's reachability graph. Both backends: one `Bag` per place, which is
Definition 14 literally, and one `List` per place, which is seven times faster and is proved to
refine it.

There are two Lake packages here, and the split is the point.
[`Cpn2mCrl2/`](Cpn2mCrl2) is the translator: no Mathlib, no dependency on
[`Proof/`](../../Proof), and a clean build in about fifteen seconds.
[`Bridge/`](Bridge) is proof only, produces no code, and depends on both — it is what makes
the composition with Theorem 1 a Lean term rather than an argument in prose.

---

## 1. Running it

```bash
cd Implementation/Lean
lake build
.lake/build/bin/cpn2mcrl2 fixtures/counter.cpn.json
```

`--list` selects the second backend:

```bash
.lake/build/bin/cpn2mcrl2 --list fixtures/counter.cpn.json
```

```
map rm_Int : Int # List(Int) -> List(Int);
    diff_Int : List(Int) # List(Int) -> List(Int);
    sub_Int : List(Int) # List(Int) -> Bool;
var _x, _y : Int;
    _l, _m : List(Int);
eqn rm_Int(_x, []) = [];
    rm_Int(_x, _y |> _l) = if(_x == _y, _l, _y |> rm_Int(_x, _l));
    diff_Int(_l, []) = _l;
    diff_Int(_l, _y |> _m) = diff_Int(rm_Int(_y, _l), _m);
    sub_Int([], _m) = true;
    sub_Int(_y |> _l, _m) = (_y in _m) && sub_Int(_l, rm_Int(_y, _m));

act t1, t2, t3;

proc Spec(p1 : List(Int), p2 : List(Int), p3 : List(Int)) =
    sum h : Int . (sub_Int([h], p1) && true) -> t1 . Spec(diff_Int(p1, [h]), (p2 ++ [(h + 1)]), p3)
  + sum h : Int . (sub_Int([h], p2) && (h <= 3)) -> t2 . Spec((p1 ++ [h]), diff_Int(p2, [h]), p3)
  + sum h : Int . (sub_Int([h], p2) && (3 < h)) -> t3 . Spec(p1, diff_Int(p2, [h]), (p3 ++ [h]));

init Spec([1], [], []);
```

The bridge is a separate package and is built separately. It needs Mathlib, which it shares
with [`Proof/`](../../Proof) rather than downloading twice:

```bash
cd Implementation/Lean/Bridge && lake build
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

It translates every fixture in *both* encodings, feeds each to `mcrl22lps`, checks the summand
and parameter counts, compares the LTS against a golden one with `ltscompare -ebisim`, compares
the two encodings against each other, and checks that every fixture under `fixtures/rejected/`
is refused.

---

## 2. The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right.

| File | What it holds | Tier |
| --- | --- | --- |
| [`Cpn2mCrl2/Util.lean`](Cpn2mCrl2/Util.lean) | duplicate removal, so that nothing outside the toolchain is needed | — |
| [`Cpn2mCrl2/Color.lean`](Cpn2mCrl2/Color.lean) | the color grammar of [`InputFormat.md`](../docs/InputFormat.md) §4.1, and values | — |
| [`Cpn2mCrl2/Bag.lean`](Cpn2mCrl2/Bag.lean) | Definition 1, finitely supported | — |
| [`Cpn2mCrl2/ListOps.lean`](Cpn2mCrl2/ListOps.lean) | lists as bags: the multiset operations, against Definition 1's | — |
| [`Cpn2mCrl2/Expr.lean`](Cpn2mCrl2/Expr.lean) | `EXPR`, intrinsically typed, and **obligation 4** | — |
| [`Cpn2mCrl2/Typing.lean`](Cpn2mCrl2/Typing.lean) | evaluation preserves sorts | — |
| [`Cpn2mCrl2/Net.lean`](Cpn2mCrl2/Net.lean) | Definitions 4 and 5, and `Net.Valid` | T1 |
| [`Cpn2mCrl2/Semantics.lean`](Cpn2mCrl2/Semantics.lean) | Definitions 6 to 9 — the reference side | — |
| [`Cpn2mCrl2/Lpe.lean`](Cpn2mCrl2/Lpe.lean) | Definitions 13 and 15, syntactically | — |
| [`Cpn2mCrl2/Translate.lean`](Cpn2mCrl2/Translate.lean) | Definition 14 | — |
| [`Cpn2mCrl2/Correct.lean`](Cpn2mCrl2/Correct.lean) | **the T2 theorems** | T2 |
| [`Cpn2mCrl2/ListEncoding.lean`](Cpn2mCrl2/ListEncoding.lean) | the second backend, and **the refinement** | T5 |
| [`Cpn2mCrl2/Print.lean`](Cpn2mCrl2/Print.lean) | the mCRL2 encoding of [`Target.md`](../docs/Target.md) §1 | — |
| [`Cpn2mCrl2/PrintList.lean`](Cpn2mCrl2/PrintList.lean) | the same for the list encoding | — |
| [`Cpn2mCrl2/Json.lean`](Cpn2mCrl2/Json.lean) | the importer — **outside the trust boundary** | T1 |
| [`Main.lean`](Main.lean) | the command line | — |
| [`Cpn2mCrl2/Examples/Counter.lean`](Cpn2mCrl2/Examples/Counter.lean) | Examples 3, 4, 5 and 9, checked | — |

And the bridge, which nothing above depends on:

| File | What it holds |
| --- | --- |
| [`Bridge/Bridge/Lang.lean`](Bridge/Bridge/Lang.lean) | the concrete language as one of `Proof/`'s `ExprLang`s |
| [`Bridge/Bridge/Cpn.lean`](Bridge/Bridge/Cpn.lean) | a validated `Net` as a `Proof/` `CPN` |
| [`Bridge/Bridge/Vars.lean`](Bridge/Bridge/Vars.lean) | arcs against index pairs, and the two readings of $\mathrm{Var}(t)$ |
| [`Bridge/Bridge/Semantics.lean`](Bridge/Bridge/Semantics.lean) | Definitions 6 and 7 on both sides |
| [`Bridge/Bridge/Soundness.lean`](Bridge/Bridge/Soundness.lean) | **T2 composed with Theorem 1** |
| [`Bridge/Bridge/ListSoundness.lean`](Bridge/Bridge/ListSoundness.lean) | **the list backend, composed with Theorem 1** |
| [`Bridge/Bridge/Example.lean`](Bridge/Bridge/Example.lean) | the whole chain, on Example 3 |

---

## 3. What is proved

The three theorems in [`Correct.lean`](Cpn2mCrl2/Correct.lean), for any net satisfying
`Net.Valid`:

| | |
| --- | --- |
| `Net.toLpe_cond` | the emitted condition holds under a marking and a binding exactly when Definition 6 says the binding element is enabled |
| `Net.toLpe_next` | the emitted next-state term for a place evaluates to the bag Definition 7 leaves there |
| `Net.toLpe_step` | consequently, the two transition relations agree |

and, in [`Bridge/`](Bridge), the one they compose into:

| | |
| --- | --- |
| `Net.bisimilar_reachabilityGraph_emitted` | for a CPN that passes the T1 validation, the reachability graph of Definition 9 and the LTS denoted by the specification the translator emits are bisimilar |
| `Net.bisimilar_reachabilityGraph_emittedList` | the same for the list-encoded specification |

That is what [`Plan.md`](../docs/Plan.md) §2 calls the theorem the project is for. Its
left-hand side is `Proof/`'s, unchanged; its right-hand side is the denotation of `Net.toLpe`,
the object [`Print.lean`](Cpn2mCrl2/Print.lean) prints; and between them stand
`CPN.bisimulation_transRel` — Theorem 1 of the thesis — and `Net.toLpe_step`, which is T2.
`Cpn2mCrl2.Examples.Counter.bisimilar_emitted` instantiates it on Example 3.

The second row is milestone M6, and [§4.5](#45-the-list-backend-and-the-order-problem) is what
it took.

[`Typing.lean`](Cpn2mCrl2/Typing.lean) adds one property that nothing else depends on but that
is the reason to believe `Expr.eval` is the semantics it is meant to be: under a well-typed
environment an expression of sort `τ` evaluates to a value of sort `τ`, so the `Color.junk`
fallback of `Expr.proj` is unreachable and `Value.asInt` and friends never misread a value.

`Proof/MCRL2.lean` proved the first two by `rfl` when this package was written, which is what
[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5 recorded as its second
limit. Milestone M2 has since closed that, so the two theorems hold there as well — over an
arbitrary expression language rather than the one concrete language fixed here. The contrast
is no longer definitional-versus-proved but printed-versus-not: `Proof/` builds the terms and
stops, since nothing there is text and so nothing there is accepted or rejected by
`mcrl22lps`. The first two rows above are about the term
[`Print.lean`](Cpn2mCrl2/Print.lean) prints.

Neither is `rfl` here either. One side is a Lean predicate; the other is the *evaluation of a
term* the translation assembled. They agree only because the term was assembled out of the
right operations.

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

## 4. Four design decisions

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

### 4.4 What the bridge cost, and what it found

Composing with Theorem 1 means exhibiting the concrete language as one of the languages
`Proof/` quantifies over, and a validated `Net` as a `Proof/` `CPN`. Four things had to be
reconciled, and each is a place where a decision on one side meets a decision on the other.

| | |
| --- | --- |
| **Values** | `ExprLang.val` must satisfy `val boolColor ≃ Bool`, so it cannot be all of `Value`; it is the values *of* a color, a subtype. That is why [`Typing.lean`](Cpn2mCrl2/Typing.lean) had to exist first — building the `ExprLang`'s `eval` at all needs evaluation to preserve sorts |
| **Bindings** | `Proof/` types a binding by construction, we type it with a separate `Env.WfOn`. `Expr.eval_congr` — obligation 4 again — is what makes the round trip invisible to any expression scoped where it should be |
| **Bags** | `Proof/`'s bag over a place holds only tokens of that place's color; ours holds any `Value`. `Bag.coeff_eq_zero_of_not_ofColor` closes the gap, and it needs type soundness to do it |
| **Quantifiers** | Definition 6 ranges over the places of $pre(t)$ and ours over the arcs into $t$; matching them is where `Net.Valid.inArcsNodup` and `placesNodup` earn their place |

Building it also found two places where the translator was *less* faithful than the thesis, and
both are now fixed in the core rather than papered over in the bridge:

- **Bindings were not typed.** Definition 2 types a binding — $b \in B(t)$ assigns each
  variable a value of *its own* type — and `Net.step` and `Lpe.step` quantified over arbitrary
  environments. That is more than Definition 15 allows, and more than mCRL2's `sum v : S`
  allows. Both now carry `Env.WfOn` on the binder.
- **Type soundness assumed too much.** `Expr.eval_wf` was stated for `Env.Wf`, well-typedness
  at every variable of every sort — which is not satisfiable, because `Env` is total and an
  enumeration with no constructors has no value for the junk environment to hold. It is now
  stated for `Env.WfOn e.freeVars`, which is what a binding of Definition 2 actually gives.

Finding those is what the exercise is for. [`Plan.md`](../docs/Plan.md) §1 says the gap is that
"nothing here connects the Lean to the translation as it is actually implemented"; connecting
them is what made the two slips visible.

### 4.5 The list backend, and the order problem

[`Plan.md`](../docs/Plan.md) §5 calls the list encoding "the largest unacknowledged gap in the
project" and separates two refinements between it and Definition 14.

**Typing is discharged by construction.** The reference generator of
[`Target.md`](../docs/Target.md) §3 shares one tagged-union `token` sort across every place,
which is what loses Definition 5's `E(p,t) : C(p)_MS`. This backend emits `List(C(p))` — one
list sort per place at that place's own color — so a place cannot hold a token of the wrong
color, and there is no invariant to preserve.
[`mCRL2.md`](../../Thesis/docs/mCRL2.md) §4.1 attributes the sevenfold speedup to `List` against
`Bag` and says nothing about sharing a sort, so nothing is given up by not copying it.

**Order is the lemma.** `Net.listRel` relates a list marking to a bag marking when they give
every token the same count, and `Net.step_of_toLpeList_step` and `Net.toLpeList_step_of_step`
match a step of either encoding with a step of the other. Nothing anywhere asks two list states
to be equal, which is exactly why the production order does not matter.

It is visible in the fixtures. [`multitoken.cpn.json`](fixtures/multitoken.cpn.json) is the net
[`Target.md`](../docs/Target.md) §4.1 asks for, and through the toolset the two backends give

```
bag encoding    des (0,4,4)
list encoding   des (0,4,5)
```

— four states against five, because the list encoding reaches `[1,2]` and `[2,1]` as distinct
states where the bag encoding reaches one marking, and `ltscompare -ebisim` reports them equal
anyway. That is [`Plan.md`](../docs/Plan.md) §5's own prediction observed:

> Those states should be bisimilar, but they are not equal — so the induced LTS has strictly more states than the reachability graph, and bisimilarity holds where isomorphism fails.

Two mechanical notes for anyone reading the file. `ListLpe` repeats the shape of `Lpe` with
list terms rather than making `Lpe` polymorphic in the state sort: `Lpe` and everything proved
about it is settled, and a second structure costs forty lines and reopens nothing. And
`Expr.bagToList` matches only the constructors that can land at bag sort, so its matcher
discriminates on the index and does *not* reduce definitionally — hence the explicit equation
lemmas beside it, which is a wrinkle worth knowing about before adding another such function.

---

## 5. What is not here

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
