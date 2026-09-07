# Design notes, Lean translator

Why the translator is shaped the way it is. Background to [`README.md`](README.md); nothing
here is needed to build or run it.

---

## Four design decisions

### 1. The product former is avoided rather than added

[`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5.1 calls the missing product
sort "the structural blocker", and the reference generator of
[`Target.md`](../docs/Target.md) §3 answers it with a `struct` per transition. Neither is
necessary, because the tuples of Definition 13 are only ever *bound*, never used as the sort of
a subterm: $d$ is the parameter list of `proc`, $h_t$ is the variable list of `sum`. Making
them binder lists keeps the data language exactly as `Proof/` has it.

Records are a different matter and do need a product in the data language — but
[`Color.lean`](Cpn2mCrl2/Color.lean) has had one from the start, because
[`InputFormat.md`](../docs/InputFormat.md) §4.1 puts records in the input grammar.

### 2. Scoping is extrinsic, which is what makes obligation 4 cheap

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

### 3. Names are one namespace

> **Addition to the thesis.** Definition 4 requires $P \cap T = \emptyset$. `Net.Valid.namesDisjoint` also requires the names of $V$ to be distinct from those of $P$ and $T$, because the emitted `proc` binds a place parameter and the emitted `sum` binds a variable in the same mCRL2 scope.

The importer additionally refuses any identifier that is an mCRL2 keyword —
[`Target.md`](../docs/Target.md) §1 flags `val` — and refuses it rather than renaming it. A
name the user did not write is worse than an error.

Two smaller things worth knowing. The output is deterministic but the order of places,
transitions and variables follows the sorted order of the JSON object keys, not the order they
were written in. And a `sort` declaration may refer to a sort declared below it; mCRL2 accepts
that, and [`fixtures/jobs.cpn.json`](fixtures/jobs.cpn.json) exercises it.

---

### 4. What the bridge cost, and what it found

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

### 5. The list backend, and the order problem

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

---

## The five obligations of [`Plan.md`](../docs/Plan.md) §4

| # | Obligation | Where, and what it cost |
| --- | --- | --- |
| 1 | Sorts gain products, for $D$ and $H_t$ | **Not needed.** `ExprTy` keeps the two constructors `Proof/` gives it. mCRL2 already spells a tuple as a parameter list, so `Lpe.params` and `Summand.binder` are lists and their components are ordinary variables. The one change is that a variable may have *bag* sort, which is one constructor argument, not a type former. See [`Lpe.lean`](Cpn2mCrl2/Lpe.lean). |
| 2 | The Definition 14 operations join the language, each with an evaluation equation | `Expr.bagSubset`, `bagUnion`, `bagDiff`, `and`, `proj`, `mkRec`. The evaluation equations are the defining clauses of `Expr.eval`. Mechanical, as predicted. |
| 3 | The bounded quantifier is unfolded at translation time | `Net.condTerm` folds `Expr.andAll` over `pre(t)`. Nothing in `Expr` quantifies. Mechanical. |
| 4 | A substitution lemma | `Expr.eval_congr`, used as `Net.eval_toEnv`. [`Plan.md`](../docs/Plan.md) §7 rates this the project's high risk. It was not: see [§2 above](#2-scoping-is-extrinsic-which-is-what-makes-obligation-4-cheap). |
| 5 | `toLPE_cond` stops being `rfl` | `Net.toLpe_cond`. It follows from 2 and 4, as predicted. |

[`Plan.md`](../docs/Plan.md) §4.1 also requires bags to be finitely supported, and they are —
which is what makes `Bag.subsetB` a decision procedure and so lets $c_t$ be a
$\textit{Bool}$-valued term rather than a proposition.

> **Departure from Definition 1.** Definition 1 models a bag as a total function $S \to \mathbb{N}$, and `Proof/CommonDefinitions.lean` transcribes it so. `Bag` here is a list of coefficient entries, and `Bag.coeff` recovers the function. This is the departure [`Plan.md`](../docs/Plan.md) §4.1 asks for and says should be recorded.
