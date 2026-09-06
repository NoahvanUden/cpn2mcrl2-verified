# Verified translator #2, Dafny

Milestone M4 of [`Implementation/docs/Plan.md`](../docs/Plan.md): the same translation as
[`Implementation/Lean/`](../Lean), against the same specification, with the obligations
discharged by SMT instead of by tactics. A Colored Petri Net goes in as a file, an mCRL2
specification comes out as text, and the term it prints is *proved* to denote the $c_t$ and
$g_t$ of Definition 14. Both backends: one `Bag` per place, which is Definition 14 literally,
and one `List` per place, which is seven times faster and is proved to refine it.

[`Languages.md`](../docs/Languages.md) §5 says what building it twice is for:

> which parts of [`Plan.md`](../docs/Plan.md) §4's five obligations does each technology make free, and which does it make expensive?

[§5](#5-what-the-comparison-actually-showed) is the answer. The short version is that the
prediction was wrong in both directions: SMT did not make obligations 1 to 3 free, because they
were already free in Lean, and the absence of dependent types did not make obligation 4
expensive, because obligation 4 never depended on them.

The strongest evidence that the two translators agree is not in any proof. It is that all six
emitted specifications — three fixtures, two encodings — are **byte-identical** to the ones
[`Implementation/Lean/`](../Lean) emits, and `scripts/check.sh` checks it on every run.

---

## 1. Running it

Dafny 4.11 with Z3, and .NET 8 or newer.

```bash
cd Implementation/Dafny
dafny build --standard-libraries --target:cs --output cpn2mcrl2 src/*.dfy
./cpn2mcrl2 fixtures/counter.cpn.json
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

`--list` selects the second backend, one `List` per place instead of one `Bag`.

To verify without building:

```bash
dafny verify --standard-libraries src/*.dfy
```

266 obligations, about 28 seconds on a laptop.

The harness of [`Target.md`](../docs/Target.md) §4 needs mCRL2 on the machine, and picks up the
Lean binary for the differential test if it is built:

```bash
MCRL2_BIN=/path/to/mcrl2/bin bash scripts/check.sh
```

It translates every fixture in both encodings, feeds each to `mcrl22lps`, checks the summand and
parameter counts, compares the LTS against a golden one with `ltscompare -ebisim`, compares the
two encodings against each other, diffs both against the Lean translator's output, and checks
that every fixture under `fixtures/rejected/` is refused.

---

## 2. The files

The chain of [`Plan.md`](../docs/Plan.md) §2, left to right. Every file has a counterpart in
[`Implementation/Lean/Cpn2mCrl2/`](../Lean/Cpn2mCrl2) of the same name, deliberately, so that
the two can be read side by side.

| File | What it holds | Tier |
| --- | --- | --- |
| [`src/Util.dfy`](src/Util.dfy) | duplicate removal, association lookup, string joining | — |
| [`src/Color.dfy`](src/Color.dfy) | the color grammar of [`InputFormat.md`](../docs/InputFormat.md) §4.1, and values | — |
| [`src/Bag.dfy`](src/Bag.dfy) | Definition 1, finitely supported | — |
| [`src/ListOps.dfy`](src/ListOps.dfy) | lists as bags: the multiset operations, against Definition 1's | — |
| [`src/Expr.dfy`](src/Expr.dfy) | `EXPR`, with `SortOf` inferring rather than indexing, and **obligation 4** | — |
| [`src/Typing.dfy`](src/Typing.dfy) | evaluation preserves sorts | — |
| [`src/Net.dfy`](src/Net.dfy) | Definitions 4 and 5, and `Valid` | T1 |
| [`src/Semantics.dfy`](src/Semantics.dfy) | Definitions 6 to 9 — the reference side | — |
| [`src/Lpe.dfy`](src/Lpe.dfy) | Definitions 13 and 15, syntactically | — |
| [`src/Translate.dfy`](src/Translate.dfy) | Definition 14 | — |
| [`src/Correct.dfy`](src/Correct.dfy) | **the T2 theorems** | T2 |
| [`src/ListEncoding.dfy`](src/ListEncoding.dfy) | the second backend, and **the refinement** | T5 |
| [`src/Print.dfy`](src/Print.dfy) | the mCRL2 encoding of [`Target.md`](../docs/Target.md) §1 | — |
| [`src/PrintList.dfy`](src/PrintList.dfy) | the same for the list encoding | — |
| [`src/Import.dfy`](src/Import.dfy) | the importer — **outside the trust boundary** | T1 |
| [`src/Main.dfy`](src/Main.dfy) | the command line | — |

There is no counterpart to [`Implementation/Lean/Bridge/`](../Lean/Bridge), and there cannot be.
See [§6](#6-what-is-not-here).

---

## 3. What is proved

The three lemmas in [`src/Correct.dfy`](src/Correct.dfy), for any net satisfying `Valid`:

| | |
| --- | --- |
| `ToLpeCond` | the emitted condition holds under a marking and a binding exactly when Definition 6 says the binding element is enabled |
| `ToLpeNext` | the emitted next-state term for a place evaluates to the bag Definition 7 leaves there |
| `ToLpeStep` | consequently, the two transition relations agree |

and, in [`src/ListEncoding.dfy`](src/ListEncoding.dfy), the refinement of
[`Plan.md`](../docs/Plan.md) §5:

| | |
| --- | --- |
| `StepOfToLpeListStep` | a step of the list encoding is matched by a step of the bag encoding, with the reached markings still representing the same bags |
| `ToLpeListStepOfStep` | and conversely |
| `ListRelInit` | the two encodings start in markings that represent the same bags |

`Proof/MCRL2.lean` proved the first two of these by `rfl` when this package was written, which
is what [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md) §5 recorded as its
second limit. Milestone M2 has since closed that, so they hold there as well — over an
arbitrary expression language rather than the one fixed here. The contrast is no longer
definitional-versus-proved but printed-versus-not: `Proof/` builds the terms and stops, since
nothing there is text and so nothing there is accepted or rejected by `mcrl22lps`.

Neither identity is definitional here either. One side is a predicate; the other is the
*evaluation of a term* the translation assembled. They agree only because the term was
assembled out of the right operations.

[`src/Typing.dfy`](src/Typing.dfy) adds one property that nothing else depends on but that is the
reason to believe `Eval` is the semantics it is meant to be: under a well-typed environment a
term of sort `τ` evaluates to a denotation of sort `τ`, so the fallback in `EProj` is unreachable
and `AsInt` and friends never misread a value.

No assumptions and no axioms: everything is `lemma` bodies checked by Z3. Checked for vacuity
with `--warn-contradictory-assumptions`; the only branch that proves anything from contradictory
assumptions is the `EVar` case of `CoeffBagToList`, which is marked `{:contradiction}` and is
vacuous on purpose — a bag-sorted variable cannot be color-sorted.

---

## 4. Four design decisions

### 4.1 Typing is inferred, not indexed

This is the one structural difference from the Lean, and everything else in this section
follows from it.

`Cpn2mCrl2/Expr.lean` makes `Expr` an inductive family indexed by `ExprTy`, so a guard is a
boolean expression and an arc expression is a bag expression *by construction*, and checks 4 to
6 of [`InputFormat.md`](../docs/InputFormat.md) §4.3 hold for every term that exists. Dafny has
no dependent types. Here `Expr` is one flat datatype, `SortOf : Expr → Option<ExprTy>` is a
total inference function, and `WellTyped(e, t)` is `SortOf(e) == Some(t)`.

Three things move as a result, and it is worth being exact about which:

- **`Valid` grows four conjuncts.** `InitTyped`, `GuardTyped`, `InArcTyped` and `OutArcTyped`
  are what Lean gets from the index. They are decided by the importer along with every other
  conjunct, so no cost falls on the user.
- **`src/Typing.dfy` has to prove sort preservation from a `SortOf` derivation** rather than
  from an index, which needs six closure lemmas in [`src/Bag.dfy`](src/Bag.dfy) — that a union
  of well-typed bags is well-typed, that a difference of one is, and so on.
- **`BagToList` takes the color as an argument** and has a fallback branch, because it can no
  longer match only the five constructors that land at bag sort.

And two things move the other way, which the plan did not anticipate:

- **The transport disappears.** `ArcDecl.exprAt` in Lean is
  `if h : a.color = c then h ▸ a.expr else .emptyBag c` — a dependently typed term transported
  along an equality proof — and three lemmas exist only to push evaluation, free variables and
  scoping through it. `ExprAt` here is an ordinary conditional and there is nothing to push
  anything through.
- **`BagToList` reduces.** Because the Lean version's matcher discriminates on the index, it
  does *not* reduce definitionally, and `Cpn2mCrl2/ListEncoding.lean` has to state five explicit
  equation lemmas beside it and warns the next reader about the wrinkle. Here it reduces and
  there are no equation lemmas.

### 4.2 Evaluation is `ghost`, and the translation is not

`Eval` is a `ghost function` and so is everything built on it — `Marking`, `Enabled`, `Fire`,
`Step`, `LpeStep`, `ListRel`. Every function in
[`src/Translate.dfy`](src/Translate.dfy), [`src/Print.dfy`](src/Print.dfy) and
[`src/Import.dfy`](src/Import.dfy) is compiled.

That is not decoration. It is [`Plan.md`](../docs/Plan.md) §2's line between the program and the
theorems about it, made checkable by the compiler: the translator computes terms and prints
them, and if it ever evaluated one the build would fail. Lean draws the same line by convention
and Dafny draws it in the language.

The same split shows up in [`src/Bag.dfy`](src/Bag.dfy): `Subset` and `BagEquiv` quantify over
`Value`, an infinite type, so they *must* be `ghost predicate`s, while `SubsetB` is compiled.
[`Plan.md`](../docs/Plan.md) §4.1 says exactly why that distinction matters —

> For $c_t$ to be a $\textit{Bool}$-valued *term* rather than a proposition, bags have to be finitely supported and colors have to carry decidable equality.

— and in Dafny confusing the two is a type error rather than a missing instance.

### 4.3 Records need a cons list, for the opposite reason to Lean's

`Cpn2mCrl2/Color.lean` splits the fields of a record into a separate `ColorFields` inductive
because Lean derives neither `DecidableEq` nor a usable recursor for the nested inductive
`List (String × Color)`. Dafny has the recursor and derives equality for free — and rejects the
recursion anyway, because it gives the elements of a bare `seq` no rank below the sequence. A
function recursing from `fs` into `fs[0].1` is refused; only one that keeps the enclosing
`Color` in scope and recurses by index is accepted, and that would make every lemma an induction
on `|fields| - i`.

So both files have a `ColorFields`, for unrelated reasons. The same applies to `Args` in
[`src/Expr.dfy`](src/Expr.dfy).

### 4.4 Names, ordering, and one Dafny wart

The naming rules are the Lean's, unchanged.

> **Addition to the thesis.** Definition 4 requires $P \cap T = \emptyset$. `NamesDisjoint` also requires the names of $V$ to be distinct from those of $P$ and $T$, because the emitted `proc` binds a place parameter and the emitted `sum` binds a variable in the same mCRL2 scope.

The importer refuses any identifier that is an mCRL2 keyword — [`Target.md`](../docs/Target.md)
§1 flags `val` — and refuses it rather than renaming it. `IsSafeIdent` is ASCII-only where
Lean's uses `Char.isAlpha`, which is stricter and is what the mCRL2 grammar actually admits.

Ordering is what makes the two outputs byte-identical. Lean's `Json` holds an object as a
balanced tree, so its importer sees the entries in key order; the Dafny standard library keeps
file order, so [`src/Import.dfy`](src/Import.dfy) sorts them explicitly. `Dedup` likewise keeps
the *last* occurrence, matching `Cpn2mCrl2/Util.lean`, so the summation variables of a summand
come out in the same order.

Two Dafny constraints left marks worth naming, because a reader will trip over both:

- **Five modules are named in the plural.** `Colors`, `Bags`, `Exprs`, `Nets`, `Lpes` — because
  the C# backend emits a module as a namespace and a datatype as a class inside it, and a module
  named `Expr` containing a datatype named `Expr` does not compile. The files keep their
  singular names so that they still map one-to-one onto the Lean files.
- **There is no exit code.** Dafny 4.11 forbids `Main` a non-ghost out parameter, so
  `scripts/check.sh` reads a rejection off the absence of the output file rather than off a
  non-zero status.

---

## 5. What the comparison actually showed

[`Languages.md`](../docs/Languages.md) §3 makes two predictions about Dafny. Both are wrong, and
the way they are wrong is the result.

> On obligations 1 to 3 — structural, first-order, finitely many cases — that should be nearly free, which is precisely where Lean is most tedious.

> Where it will hurt is C4. The substitution lemma is an induction over expression syntax, and in Dafny that means writing an explicit recursive `lemma` and trusting the termination checker. This is a well-worn Dafny idiom rather than a novelty, but it will be longer than it looks, and the resulting proof will not connect to Theorem 1 except on paper.

### 5.1 The five obligations, measured

| # | Obligation | In Lean | In Dafny |
| --- | --- | --- | --- |
| 1 | Sorts gain products, for $D$ and $H_t$ | Not needed | Not needed, for the same reason |
| 2 | The Definition 14 operations join the language, with evaluation equations | Mechanical | Mechanical |
| 3 | The bounded quantifier is unfolded at translation time | Mechanical | Mechanical |
| 4 | A substitution lemma | One structural induction, no casts | One structural induction, every case closed by Z3 with no hint |
| 5 | `toLPE_cond` stops being `rfl` | Follows from 2 and 4 | Follows from 2 and 4 |

Obligation 1 is discharged in both by the same observation, and it is about mCRL2 rather than
about either language: the tuples of Definition 13 are only ever *bound*, never used as the sort
of a subterm, so $d$ is the parameter list of `proc` and $h_t$ is the variable list of `sum`, and
neither needs a product former. [`LeanFormalization.md`](../../Thesis/docs/LeanFormalization.md)
§5.1 calls the missing product "the structural blocker" and the reference generator of
[`Target.md`](../docs/Target.md) §3 answers it with a `struct` per transition; neither
translator needs to.

Obligations 2, 3 and 5 are mechanical in both, and the reason they are mechanical in Lean is not
that Lean is good at them — it is that there are only about twenty of them and they are all
first-order. **SMT has nothing to give away here, because nothing was being paid.** That is the
first half of the answer to §5's question, and it is a negative result about the exercise's own
premise rather than about Dafny.

Obligation 4 is the interesting one. [`Plan.md`](../docs/Plan.md) §7 rates it the project's high
risk and schedules a Lean prototype "before committing to three implementations". It cost
nothing in either language, and for a reason that is a design decision rather than a language
feature: **scoping is extrinsic on both sides.** A variable carries its name and sort,
`Expr.ScopedIn` / `ScopedIn` is a separate predicate, and the translation moves a term from the
CPN's context into the summand's context by doing nothing to it at all. Obligation 4 is then a
congruence — the value of a term depends only on its free variables — which is one structural
induction with no casts in Lean and one recursive `lemma` in Dafny whose every case Z3 closes
without a hint.

Had either translator indexed `Expr` by a typing context, obligation 4 would have been a
strengthening lemma over dependent proofs in Lean and, in Dafny, a mess. The plan's risk
assessment was aimed at the wrong axis: the cost was never dependent types versus SMT, it was
intrinsic versus extrinsic *scoping*.

### 5.2 Where SMT did help, and where it did not

Three places in this development needed a hint Z3 would not supply, all of the same shape: a
quantified fact that will not instantiate where it is used. Each was fixed the same way, by
lifting the step into a lemma whose preconditions are exactly the facts to instantiate —
`ListRelAt`, `SubMultisetOfCounts`, and `SubMultisetComplete`, the last stated as a
contrapositive so that the recursion runs on the negation.

That last one is the sharpest instance and is worth recording. `SubMultisetIff` is an `<==>`
between a recursive predicate and a universally quantified counting statement. Proving it by
case-splitting on the biconditional inside one lemma failed no matter how many assertions were
added, including one that Z3 accepted as `assert false` on the branch it was still refusing to
close. Splitting it into a forward lemma and a contrapositive backward lemma made it go through
immediately. Auto-active verification is fast when the goal is a conjunction of ground facts and
brittle when it is a biconditional between quantifiers; that is not news, but it is where all
three of this development's hints went.

Against that, Z3 discharged [`src/Correct.dfy`](src/Correct.dfy) — the whole of T2 — on the
first attempt, given only the structure and the lemma calls, and it is **the one file that is
smaller than its Lean counterpart**: 175 lines of code against 266. `Cpn2mCrl2/Correct.lean`
spends most of that difference on explicit `show` steps that force definitional unfolding before
a `rw` will fire. Nothing in Dafny corresponds to them.

That is the one place where the technologies separated as advertised. It is not among the five
obligations the plan expected to separate them.

### 5.3 Size

| | Lean | Dafny |
| --- | --- | --- |
| Lines of code, excluding comments and blanks | 2670 | 3517 |
| Lemmas / theorems | 111 | 133 |
| Clean verify | ~15 s | ~28 s |

The Dafny is about a third larger, and the extra lines are not where the plan would have put
them. Per file, against the Lean of the same name:

| File | Lean | Dafny | |
| --- | --- | --- | --- |
| `Import` / `Json` | 311 | 507 | +196 |
| `Bag` | 131 | 309 | +178 |
| `ListEncoding` | 384 | 542 | +158 |
| `Net` | 193 | 334 | +141 |
| `Expr` | 368 | 414 | +46 |
| `Correct` | 266 | 175 | **−91** |

Two thirds of the growth is in the importer and in `Bag`, and neither is about verification.

The importer parses with the standard library's verified JSON reader, which is *less* work than
Lean's, and then spends it all back threading a fuel counter and a `Result` monad through four
mutually recursive functions where Lean writes `partial def` and a `do` block.

`Bag` is library depth. Its content is the coefficient laws — `EntryCoeffAppend`, `CoeffDiff`,
`SubsetBIff` — and in Lean each is three or four lines because `simp`, `omega` and the standard
library's list lemmas do the work. In Dafny each is an explicit induction, and every step over a
sequence needs `assert s[1..] == ...` to tell the solver that slicing a sequence is what it
looks like. The same effect accounts for `Net`: `MemPlaceNames`, `MemArcsOf`,
`MemCondConjuncts` and a dozen siblings are written out here and are `List.mem_map`,
`List.mem_filter` and `List.mem_append` there.

So the honest summary of the size difference is that it measures the two standard libraries, not
the two proof technologies. The file that measures the proof technologies is `Correct`, and it
goes the other way.

### 5.4 The result that is not a proof

All six emitted specifications are byte-identical to the Lean translator's, and
`scripts/check.sh` re-checks it on every run. That is worth more than it looks. The two
developments share no code, were written against the same three documents rather than against
each other, and make different structural choices about typing at every level — and they agree
on the text down to the parenthesization of `((p1 - {h: 1}) + {:})`.

[`Target.md`](../docs/Target.md) §4.1's prediction is also reproduced independently: on
`multitoken.cpn.json` and on `jobs.cpn.json` the bag encoding gives four states and the list
encoding five, and `ltscompare -ebisim` reports them equal anyway. That is
[`Plan.md`](../docs/Plan.md) §5's own sentence observed a second time:

> Those states should be bisimilar, but they are not equal — so the induced LTS has strictly more states than the reachability graph, and bisimilarity holds where isomorphism fails.

---

## 6. What is not here

**The composition with Theorem 1.** [`Languages.md`](../docs/Languages.md) §3 says it plainly
when it picks Dafny second:

> the resulting proof will not connect to Theorem 1 except on paper

and that is the situation. Theorem 1 is `CPN.bisimulation_transRel` in
[`Proof/`](../../Proof), a Lean 4 term; [`Implementation/Lean/Bridge/`](../Lean/Bridge) composes
it with T2 to get `Net.bisimilar_reachabilityGraph_emitted`, and nothing in Dafny can be an
argument to a Lean theorem. What this package establishes on its own is T1, T2 and T5, and the
composition with T3 is prose here where it is a term there.

That is the honest statement of what a second implementation buys and what it does not. It does
not double the guarantee. It buys an independent check that the specification in
[`Implementation/docs/`](../docs) is implementable as written, an independent proof of the same
T2 statement, and — through `scripts/check.sh` — a differential test with real teeth.

**T0 and T4 are tested, never proved.** [`Plan.md`](../docs/Plan.md) §2 calls this "the honest
ceiling": whether `mcrl22lps` accepts the text, and whether what it reads back denotes the term
that was printed, would need a formalized mCRL2 grammar. `scripts/check.sh` runs the tool
instead.

**Importers.** Only the native format of [`InputFormat.md`](../docs/InputFormat.md) §4 is read.
PNML and the Model Checking Contest corpus are M7.

---

## 7. Sources

- N. van Uden, *Model checking for analysis of BPMN models*, Master Thesis Report, Eindhoven
  University of Technology, April 2025. Definitions 1, 2, 4 to 9 and 13 to 15 are transcribed in
  [`Thesis/docs/`](../../Thesis/docs).
- [`Proof/`](../../Proof), where those definitions are formalized and Theorem 1 is proved, and
  [`Implementation/Lean/`](../Lean), the translator this one is compared against.
- Dafny 4.11 and the Dafny standard libraries — `Std.Wrappers`, `Std.JSON`, `Std.FileIO`.
  [dafny.org](https://dafny.org/)
- mCRL2 toolset 202307.1, which every claim in [`Target.md`](../docs/Target.md) and every run of
  `scripts/check.sh` is against. [mcrl2.org](https://www.mcrl2.org/)
