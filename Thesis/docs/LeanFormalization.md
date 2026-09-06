# The Lean formalization

The `Proof/` directory of this repository holds a Lean 4 / Mathlib formalization of the
definitions transcribed in these notes. This page records **how faithful that formalization
is to the definitions on the other pages**: where it follows them exactly, where it departs
from them and why, and what it does not cover.

The other pages are the reference; this page is a report on the Lean, not a definition of
anything. Nothing here changes what the notes say.

---

## 1. What is formalized where

| Lean file | Definitions | Notes page |
| --- | --- | --- |
| `Proof/CommonDefinitions.lean` | 1, 2, and the assumed expression language | [CommonDefinitions.md](CommonDefinitions.md) |
| `Proof/LabeledTransitionSystems.lean` | 3 | [LabeledTransitionSystems.md](LabeledTransitionSystems.md) |
| `Proof/ColoredPetriNets.lean` | 4, 5, 6, 7, 8, 9 | [ColoredPetriNets.md](ColoredPetriNets.md) |
| `Proof/MCRL2.lean` | 13, 14, 15, 18 | [mCRL2.md](mCRL2.md) |
| `Proof/Bisimulation.lean` | 16 | [Bisimiliarity.md](Bisimiliarity.md) |
| `Proof/Soundness.lean` | 17, Theorem 1 | [Bisimiliarity.md](Bisimiliarity.md) |

The `Examples/` library instantiates Examples 2, 3, 4, 5, 9 and 10, plus one bisimulation
example (a tennis game) that is not from the thesis.

### 1.1 Verification status

- `lake build` succeeds — 969 jobs, no errors and no warnings, covering both default targets
  (the `Proof` library and the `Examples` library).
- No `sorry`, no `axiom` declaration and no `native_decide` anywhere in `Proof/` or
  `Examples/`.
- `#print axioms` on `CPN.bisimulation_transRel`, `CPN.bisimilar_toLPESemantics`,
  `CPN.mem_RGState_of_directlyReachable`, `CPN.toLPE_cond` and `CPN.toLPE_next` reports only
  `propext`, `Classical.choice` and `Quot.sound` — the three standard Lean axioms.

---

## 2. Faithful, definition by definition

The following are transcribed exactly, modulo the representation choices of [§3](#3-representation-choices).

| Definition | Lean | Comment |
| --- | --- | --- |
| 1, bag | `Bag S := S → ℕ` | Operations 1, 2, 3 and 6 are the `Membership`, `Union`, `HasSubset` and `SDiff` instances; union adds coefficients, and difference is truncated subtraction on the naturals, which is exactly the printed maximum against zero |
| 2, binding | `Bindings val varType V` | A dependent function on the variables, valued in their types |
| 3, LTS | `LTS S L` | States and actions are type parameters; the transition relation is curried as `S → L → S → Prop` |
| 4, Petri Net | `PetriNet P T` | Disjointness of places and transitions holds by construction, since they are different types; the arc set is split into `inArc` and `outArc` |
| 5, CPN | `CPN L P T` | Every typing side condition is carried by a type: `G t` is boolean, `Ein` and `Eout` land in the bag of the color of their place, `I p` is closed. The remaining conditions are fields: `colorMem`, `boolMem` and `varTypeMem` |
| 6, enabled | `CPN.Enabled` | Both conjuncts, quantified over the preset |
| 7, occurrence | `CPN.fire`, `CPN.Occurs` | Quantified over all places, using the convention of §2.1.1 of the CPN notes |
| 8, reachability | `CPN.Reachable`, `CPN.R` | `Relation.TransGen`, i.e. **not** reflexive — the reading argued for in §3.5.1 of the CPN notes |
| 9, reachability graph | `CPN.reachabilityGraph` | The state set is the subtype `RGState`, and the transition relation ranges over it — the corrected form |
| 13, LPE | `LPE Act` | The family of summands indexed by `K` |
| 14, translation | `CPN.toLPE`, `CPN.toLPEInit` | Builds $c_t$ and $g_t$ from Definition 14's text, deliberately not from `Enabled` and `fire`; see [§5](#5-what-the-translation-is-and-what-theorem-1-therefore-establishes) |
| 15, LPE semantics | `LPE.semantics` | See [§4.9](#49-definition-15-is-read-not-transcribed) |
| 16, bisimulation | `LTS.Bisimulation`, `LTS.Bisimilar` | Both conditions, with the conclusion `R u u'` on each side |
| 17, the relation | `CPN.transRel` | |
| Theorem 1 | `CPN.bisimulation_transRel` | With `CPN.bisimilar_toLPESemantics` for §4 of the bisimilarity notes |
| 18, mu-calculus | `MuFormula` | All ten constructors, and the shorthands of §2.2 as `diaSet`, `boxSet`, `diaStar`, `boxStar`, `diaCompl`, `boxCompl` |

Two things the Lean gets right that are easy to get wrong:

- `MuFormula.diaSet []` is `false` and `boxSet []` is `true` — the correct empty disjunction
  and empty conjunction for the diamond and box over an empty set of actions.
- `LTS.Bisimulation` states condition 1's conclusion as `R u u'`. The proof text in
  [Bisimiliarity.md](Bisimiliarity.md) §3 writes it once as $s'Ru'$, a slip carried over from
  the thesis; Definition 16 itself has $uRu'$, and that is what the Lean encodes.

---

## 3. Representation choices

These are places where the Lean shape differs from the printed shape but carries the same
information. All of them are recorded in the module docstrings.

**Tuples as dependent functions.** Definition 14 writes the LPE state as an $n$-tuple with one
bag per place, and $H_t$ as a tuple over $\mathrm{Var}(t)$. The Lean uses `CPN.Marking` and
`CPN.TransBinding t`, dependent functions out of the places and out of $\mathrm{Var}(t)$. For
a finite place set these are the same data, and the choice is what makes Definition 17
collapse to the equation `M.1 = d`.

**Sets as types.** The states, actions, places and transitions are Lean types rather than
sets of an ambient type, so that Definition 16 can relate two LTSs with different state types
and so that the disjointness condition of Definition 4 is automatic. Finiteness becomes a
field.

**`Type[e]` as an index.** Instead of a function from expressions to types, the Lean indexes
the expressions themselves: `L.Expr τ` is what the notes write as the expressions whose type
is $\tau$. This makes the typing conditions of Definition 5 hold by construction rather than
needing a cast at each evaluation. Similarly $\mathrm{EXPR}_V$ is the subtype `L.ExprOn V τ`.

**Arc expressions take the membership proof.** `Ein` and `Eout` take the proof that the pair
is an arc as an argument, because $E$ is defined on $A$ only. Proof irrelevance makes this a
genuine function on $A$.

---

## 4. Deviations and gaps

### 4.1 Bag size is valued in the extended naturals

Operation 4 of the bag notes is the sum of all coefficients, over an $S$ that need not be
finite. `Bag.card` is valued in `ℕ∞`, defined as the supremum of the finite partial sums. For
a bag with finite support this agrees with the ordinary sum.

The notes do not flag that the printed sum is ill-defined for an infinite $S$; the Lean
resolves it. It is the right resolution, but it is a departure from the printed operation.

### 4.2 Operation 5 gains a finiteness hypothesis

`Bag.iUnion` takes an extra argument stating that each item has a non-zero coefficient in only
finitely many members of the family. Operation 5 of the notes writes the union of a family
indexed by the naturals with no such hypothesis, and without it the sum need not be a natural
number, so the result need not be a bag. The docstring says so; the notes do not.

### 4.3 Definition 1's non-emptiness is dropped

Definition 1 requires $S$ to be non-empty. `Bag S` does not. The docstring states this and
observes that the requirement plays no role in any operation or in any definition that uses
bags.

### 4.4 The expression language is restricted to two type shapes

`ExprTy Color` has exactly two constructors, a color and the bag of a color. The notes place
no restriction on what $\mathrm{Type}[e]$ may be; they only ever *use* a color (guards) or a
bag of a color (arc and initialization expressions). So the restriction is harmless for
everything on these pages, but an expression language with, say, product types or bags of bags
is not an `ExprLang`.

A second, smaller point: `ExprLang.eval` takes a binding of exactly the free variables of the
expression. This makes "evaluation depends only on the free variables" true by construction,
which the notes leave implicit. It also means `vars` must be the exact free-variable set, not
an over-approximation.

### 4.5 Every side condition of Definition 5 but one is inert

`finiteTransitions`, `finiteColors`, `finiteV`, `boolMem`, `colorMem` and `varTypeMem` are
declared as fields and discharged in `Examples/CounterNet.lean`, but no proof in `Proof/`
uses any of them. That is expected — Definitions 6 to 9 and Theorem 1 genuinely do not need
finiteness — but it means none of them is load-bearing, so an error in one would not be
caught by the build.

`finitePlaces` was in that list and no longer is. `CPN.preList` enumerates $pre(t)$ from it,
because Definition 14's bounded conjunction over $pre(t)$ is unfolded into a finite one when
the translation is built; see [§5](#5-what-the-translation-is-and-what-theorem-1-therefore-establishes).
That is the one prediction of [§5.1](#51-what-it-would-take-to-show-the-emitted-specification-is-well-formed)
about inert fields becoming load-bearing that has come true. The other four it names —
`finiteV`, `finiteColors`, `colorMem` and `varTypeMem` — were predicted to be needed for
enumerating $H_t$ and for emitting sort declarations, and neither of those is done here.

`Bag.coeff`, `Bag.card` and `Bag.iUnion` are likewise defined and never used.

### 4.6 The inclusion of a transition's variables in $V$ is provable but not proved

§3.2 of the CPN notes states $\mathrm{Var}(t) \subseteq V$. `CPN.Var t` is a bare
`Set L.Var`, and the inclusion follows immediately from the `ExprOn V` subtype proofs on `G`,
`Ein` and `Eout`, but it is not stated. As a result `CPN.TransBinding t` is not literally the
restriction of a binding of $V$.

### 4.7 Two unrelated notions called "reachable"

`LTS.Reachable` is the *reflexive*-transitive closure of the LTS step relation;
`CPN.Reachable` is the *transitive* closure of `DirectlyReachable`. Both readings are correct
in their own place — Definition 8 is transitive-only, as §3.5.1 of the CPN notes argues — but
the two share a name and nothing connects them. In particular there is no theorem saying that
the states of `RGState` are exactly the `LTS.Reachable` states of `reachabilityGraph`, which
is true and would confirm that `RGState` neither over- nor under-approximates the state set of
Definition 9.

### 4.8 Definition 16 forces one action type

Definition 16 gives the two LTSs separate action sets $L$ and $L'$; `LTS.Bisimulation` takes
one shared action type. The docstring justifies this: the two conditions match steps *carrying
the same action*, which only has meaning for actions common to both, and in Definition 17 both
LTSs have the CPN's transitions as their actions. It is still a restriction of Definition 16 as
printed.

### 4.9 Definition 15 is read, not transcribed

Definition 15 as printed writes the transition triple with a source $d_c$, binds $d$ and $d'$
in $D$ and $a_k$ in $Act$, leaves $h_k$ unbound, and adds the clause
$d_c = d\langle b \rangle$. `LPE.semantics` reads this as: quantify the summand index `k` and
the value of the summation variable, then require that the summand's action is the label, that
its condition holds, and that the target is its next state. The clause
$d_c = d\langle b \rangle$ is dropped, on the grounds that a state is already a value of $D$
and $b$ binds only the summation variable, so $d\langle b \rangle$ is $d$.

That reading is the only sensible one, and the docstring gives it. The notes reproduce
Definition 15 verbatim without recording that it needs one.

### 4.10 The condition of a summand is a proposition, not a boolean

Definition 13 types the condition as a function into $\textit{Bool}$. `LPE.cond` is
`D → H k → Prop`. The docstring's reason is that Definition 14 builds a condition containing a
bag inclusion over an arbitrary color, which is not decidable. A boolean-valued condition is
the special case where the proposition is that the boolean is `true`. This is a consequence of
[§5](#5-what-the-translation-is-and-what-theorem-1-therefore-establishes).

It survives the change recorded there. `CPN.Cond` is syntax now, but `CPN.Cond.eval` still
lands in `Prop`, for the same reason: its `subset` clause is bag inclusion over an arbitrary
color. Getting a $\textit{Bool}$ needs bags to be finitely supported, which is a further
departure from Definition 1 as printed and is not made here.

> **Departure from Definition 1, made elsewhere.** Both translators under [`Implementation/`](../../Implementation) do make it — their `Bag` is a list of coefficient entries rather than a total function $S \to \mathbb{N}$, which is exactly what lets their $c_t$ be a $\textit{Bool}$-valued term; [`Plan.md`](../../Implementation/docs/Plan.md) §4.1 asks for that departure to be recorded, and this is the record.

---

## 5. What the translation is, and what Theorem 1 therefore establishes

Definition 14 defines the translated LPE by giving, for each transition $t$, an explicit
condition and next state:

$$
\begin{aligned}
c_t(d, h_t) &= \big(\forall p \in pre(t) : E(p,t) \subseteq s_p\big) \land G(t) \\[4pt]
g_t(d, h_t) &= \big( (s_{p_1} \setminus E(p_1,t)) \cup E(t,p_1), \ldots \big)
\end{aligned}
$$

`CPN.toLPE` builds both, from Definition 14's own text. It could instead have set the
condition to `Enabled d b` and the next state to `fire d b`, since those right-hand sides are
symbol for symbol Definitions 6 and 7 — but then the translation would be *defined as* the
semantics it is compared against in Theorem 1, and the theorem could not fail. The
identification is therefore a claim, `CPN.toLPE_cond` and `CPN.toLPE_next`, rather than a
definition.

Neither holds by `rfl` any more, and that is the change [§5.1](#51-what-it-would-take-to-show-the-emitted-specification-is-well-formed)
asked for. `CPN.toLPE` no longer gives $c_t$ and $g_t$ as Lean functions; it *assembles*
them, as `CPN.condTerm` and `CPN.nextTerm`, out of the CPN's own guard and arc expressions
and four operations applied to those, and an `LPE` is what evaluating that syntax denotes. So
`toLPE_cond` says the condition the translation built evaluates to `CPN.Enabled`, and
`toLPE_next` says the same of `CPN.fire` — both proved from the evaluation equations of
`CPN.Term` and `CPN.Cond`. That `rfl` proves neither was checked by trying it.

The property the `rfl`s had survives the change. Injecting into `CPN.Enabled` the slip the
thesis itself makes — quantifying over $post(t)$ instead of $pre(t)$ — breaks `toLPE_cond`,
`toLPE_next` and `toLPESemantics_step`, where before `CPN.toLPE` was separated from the
semantics it broke nothing and left the build green.

What is still shared between the two sides is how the CPN's components are *read* — `pre`,
`G`, and `consume`/`produce` for the §2.1.1 convention on arc expressions of non-existing
arcs. That sharing is correct: those are the interpretation of $E$ and $G$, not part of the
translation, and Definition 14 refers to them exactly as Definitions 6 and 7 do.

`Examples/CounterNetLPE.lean` checks the result concretely against Example 9:
`cond_t₁`, `cond_t₂` and `cond_t₃` unfold the translated condition into the three printed
summand conditions, and `next_t₁_p₁`, `next_t₁_p₂` and `next_t₁_p₃` do the same for the next
state of the first summand. In particular `cond_t₃` confirms the deviation recorded in
[mCRL2.md](mCRL2.md) Example 9: the translation yields the inclusion in $s_{p_2}$, not in
$s_{p_3}$.

**Two limits were stated here. One is closed; one remains.**

1. **Theorem 1's proof stays short**, and this is the one that remains. `toLPE_cond` and
   `toLPE_next` are no longer definitional, so the two transition relations no longer agree
   by unfolding: `CPN.toLPESemantics_step` rewrites with both, and it is the only place that
   uses either. But the bisimulation argument is not deeper for it — the two theorems are
   consumed in one step each and everything after that is unchanged. What the Lean proof of
   Theorem 1 contributes beyond the thesis is still the step the thesis skips: an LPE step
   out of a state of the reachability graph lands back inside it, which is
   `CPN.mem_RGState_of_directlyReachable`.
2. **`LPE` modelled the transition-system schema an LPE denotes, not LPE syntax.** That was
   the second limit and it is closed. `CPN.LPESyntax` is an LPE as data — a condition per
   transition, a next-state term per transition and place, and the initial expression of each
   place — and `CPN.LPESyntax.denote` is the `LPE` it denotes. `LPE` is now the *meaning* of
   what the translation produces rather than the thing it produces, and $c_t$ and $g_t$ are
   expressible by construction in a language whose only primitives beyond the CPN's own
   expressions are $\land$, $\subseteq$, $\cup$ and $\setminus$. What that took is
   [§5.2](#52-what-closing-it-actually-took), and it is not what
   [§5.1](#51-what-it-would-take-to-show-the-emitted-specification-is-well-formed) predicted.

Separately, and whatever is done about the two above: nothing here connects the Lean to the
translation as it is actually implemented. That would need extraction, a shared serialization
format, or at minimum a documented correspondence, and is out of scope for these files.

That paragraph is left standing because [`Implementation/`](../../Implementation) is the
answer to it, and it is worth being exact about how much of an answer.
[`Implementation/Lean/`](../../Implementation/Lean) is a translator that emits mCRL2 text and
whose correctness theorem composes with `CPN.bisimulation_transRel` inside Lean;
[`Implementation/Dafny/`](../../Implementation/Dafny) is a second one, agreeing with it byte
for byte on every fixture. Neither is *this* development extracted. They fix one concrete
expression language where `Proof/` quantifies over every language `ExprLang` admits, and they
share no code with it — so what they add is a translation that runs, not a stronger theorem
about the one here.

None of this makes anything on the other pages wrong. It bounds what the Lean establishes:
**given** that an LPE means the transition system Definition 15 assigns it, the reachability
graph of a CPN and the LTS induced by the LPE Definition 14 builds from it are bisimilar, and
that bisimilarity is fully proved.

### 5.1 What it would take to show the emitted specification is well-formed

Limit 2 above is narrower than it first reads, so it is worth stating exactly what is missing
before saying what would close it.

The CPN's own pieces already *are* expressions of the assumed language: `G t` has the type
`L.ExprOn V (.color L.boolColor)`, and `Ein` and `Eout` land in `L.ExprOn V (.bag (C p))`.
What is not an expression is the thing Definition 14 *assembles* from them. In `CPN.toLPE`
the conjunction of bag inclusions is a Lean `Prop` built from the `HasSubset` instance on
`Bag`, and the tupling, $\setminus$ and $\cup$ of $g_t$ are Lean operations on `CPN.Marking`.
So the missing claim is precisely this: **$c_t$ and $g_t$ themselves live in `L.Expr`, not
just their ingredients.**

**Three readings of "well-formed".** They are not equally reachable.

| Reading | Reachable in Lean? |
| --- | --- |
| $c_t$ and $g_t$ are terms of the expression language Chapter 2 assumes | Yes, and this is the reading the thesis's own framing supports |
| Those terms are well-typed *mCRL2* data terms specifically | Yes, if `ExprLang` is committed to an mCRL2-shaped signature |
| The printed text is accepted by `mcrl22lps` | No — an intrinsically typed term language establishes well-typedness, never well-formedness of text |

The third would need a printer together with a formalized grammar; without the grammar the
best available is an empirical round trip through the tool.

> Whether the operations Definition 14 uses are native mCRL2 bag operators should be confirmed against the tool documentation before the second reading is relied on.

**The structural blocker.** `ExprTy` has exactly two constructors, `.color c` and `.bag c`,
and `varType` maps a variable to a `Color`. But in the LPE both $d : D$ and $h_t : H_t$ are
variables whose sorts are *tuples*, so neither can be written as a variable of the language
as it stands. This is where the restriction recorded in
[§4.4](#44-the-expression-language-is-restricted-to-two-type-shapes) stops being harmless.

What follows from it:

1. `ExprTy` gains a product former, and `ExprTy.Value` maps it to a dependent function.
2. `varType` becomes `Var → ExprTy Color`, which ripples into `Bindings`, `CPN.varTypeMem`
   and every example.
3. `ExprLang` gains the operations Definition 14 uses as fields — conjunction, bag
   $\subseteq$, $\setminus$ and $\cup$, projection and tupling — each with an evaluation
   equation.
4. A substitution lemma. The free variables of $E(p,t)$ lie in $\mathrm{Var}(t)$; in the LPE
   they become components of $h_t$. Relating "$E(p,t)$ evaluated under a binding $b$ of the
   transition" to "the translated term evaluated under $d \mapsto M$ and $h \mapsto b$" is
   the one genuinely new proof obligation.
5. `LPE.cond` and `LPE.next` become terms and `LPE.semantics` denotes them, so `toLPE_cond`
   and `toLPE_next` stop holding by `rfl` and become theorems proved from the evaluation
   equations of item 3.

The bounded $\forall$ over $pre(t)$ needs no quantifier in the data language: $pre(t)$ is a
finite set of places known at translation time, so that conjunction is unfolded there.

**Bags would have to become finitely supported.** One consequence has mathematical content
rather than being bookkeeping. Bag inclusion on `Bag S := S → ℕ` is
$\forall s \in S : m_1(s) \leq m_2(s)$, which is not decidable for an arbitrary $S$. For
$c_t$ to be a $\textit{Bool}$-valued term rather than a proposition, bags have to be finitely
supported and colors have to carry decidable equality.

That reframes [§4.10](#410-the-condition-of-a-summand-is-a-proposition-not-a-boolean):
`LPE.cond` landing in `Prop` is not a modelling convenience but a consequence of Definition 1
modelling a bag as a total function into $\mathbb{N}$. It also runs with the grain of §4.1 of
[mCRL2.md](mCRL2.md), where the thesis replaces bags with `FBag` and with lists for
performance. Restricting `Bag` this way would be a further departure from Definition 1 as
printed, to be recorded here alongside [§4.1](#41-bag-size-is-valued-in-the-extended-naturals)
to [§4.3](#43-definition-1s-non-emptiness-is-dropped).

**What would become load-bearing.** Several of the fields
[§4.5](#45-every-side-condition-of-definition-5-but-one-is-inert) records as inert would start
carrying weight: `finitePlaces` to enumerate the components of $D$ and to unfold the
conjunction over $pre(t)$, `finiteV` to enumerate $H_t$, and `finiteColors`, `colorMem` and
`varTypeMem` to emit the sort declarations. `inArc` and `outArc` would also have to be
decidable, or `Finset`s, so that $pre(t)$ computes.

**Three ways forward.**

- **A. Restate the scope and stop.** The thesis defines $c_t$ and $g_t$ as mathematical
  functions too, so a semantic `LPE` matches Definition 14 exactly. On this reading limit 2
  is not a gap in fidelity but a declared boundary, and the formalization is complete
  relative to the thesis.
- **B. Add the operations to `ExprLang` as fields, keeping `Expr` abstract.** This reaches
  the first reading and most of the second without an inductive syntax, a grammar or a
  printer, and the general `toLPE_cond` becomes a theorem quantified over every expression
  language satisfying the evaluation equations — which is where the content is. It is also
  the closest to Chapter 2's own framing: the thesis already assumes the tools provide an
  expression language, and this assumes only a richer one, carrying exactly the operations
  Definition 14 uses. Most of the cost does not land on `Examples/`, since `CounterNet.Expr`
  is already a free-variable set paired with an evaluation function, so supplying the new
  fields there is mechanical.
- **C. A syntactic mCRL2 fragment** — an inductive term language, sort and action
  declarations, and a printer. Worth it only if the goal is a verified translator, and even
  then the third reading bottoms out in a round trip that has to be tested rather than
  proved.

Independently of that choice, emitting the LPE of `Examples/CounterNetLPE.lean` as mCRL2 text
and checking that `mcrl22lps` accepts it is cheap. It proves nothing, but it is the only
check named here that tests the translation against the actual tool.

### 5.2 What closing it actually took

Everything above in [§5.1](#51-what-it-would-take-to-show-the-emitted-specification-is-well-formed)
is left as it was written, because the interest is in where it was wrong. It offered three
ways forward and the route taken is none of them.

**What was built.** `CPN.Term` and `CPN.Cond` are an inductive syntax for exactly the layer
Definition 14 *adds* to the CPN: the state components $s_p$, conjunction, bag $\subseteq$,
$\cup$ and $\setminus$. The guard and the arc expressions enter through one constructor each
and are never looked inside. `CPN.LPESyntax` bundles them into an LPE and
`CPN.LPESyntax.denote` evaluates it. That is option C stripped of the sort declarations and
the printer — which is to say, of the parts of C that only a translator needs, and
[`Implementation/`](../../Implementation) is where the translator lives.

**Why not option B.** Adding the operations to `ExprLang` as fields reads better and §5.1
recommends it, but it does not survive contact with the state components. For $s_p$ to be a
term of the language it has to *be* a variable of it, so `varType` becomes
`Var → ExprTy Color` and — the real cost — the CPN has to supply a fresh variable per place
together with its freshness conditions, which is a new component in Definition 5's tuple that
the thesis does not have. It also assumes the tool's expression language contains bag
operations, which Chapter 2 nowhere says. Building the four operations assumes nothing about
the tool and leaves Definition 5 alone.

**The structural blocker was not one.** §5.1 names the missing product former as the blocker.
Definition 13's $D$ and $H_t$ are indeed tuples, but they are only ever *bound*: $d$ is the
parameter list of the process and $h_t$ the variable list of the sum. So the tupling of $g_t$
is the indexing of `LPESyntax.next` by a place, the projection $s_p$ is a constructor, and
`ExprTy` keeps the two constructors it had. Items 1 and 2 of §5.1's list do not happen, and
neither does the ripple into `Bindings`, `CPN.varTypeMem` and every example that item 2
predicts. [`Implementation/Lean/README.md`](../../Implementation/Lean/README.md) §4.1 reaches
the same conclusion from the mCRL2 side, independently.

**Item 4, "the one genuinely new proof obligation", is not a proof.** There is no substitution
lemma here. `ExprLang.evalOn` evaluates an expression under any binding that contains its free
variables, by restricting that binding to them; so moving $E(p,t)$ from $V$ into
$\mathrm{Var}(t)$ is not a re-indexing of the term but a different restriction of the same
binding, and the obligation is discharged by how scoping is modelled rather than by an
induction. Both translators of [`Implementation/`](../../Implementation) report the same
thing, and [`Implementation/Dafny/README.md`](../../Implementation/Dafny/README.md) §5 draws
the conclusion the three developments now agree on: the cost of this obligation was never
dependent types against SMT, it was intrinsic scoping against extrinsic scoping.

**What did cost something.** Item 3, the operations with their evaluation equations; and the
unfolding of the bounded quantifier, which is `CPN.condOf` folding a conjunction over
`CPN.preList` and `CPN.eval_condOf_preList` folding it back into $\forall p \in pre(t)$. That
second one is where `finitePlaces` stops being inert, as §5.1 predicts and
[§4.5](#45-every-side-condition-of-definition-5-but-one-is-inert) now records. Item 5 follows
from the equations, as predicted.

**What is still not established.** The third reading of "well-formed" is untouched: nothing
here is text, so nothing here is accepted or rejected by `mcrl22lps`. `Cond.eval` still lands
in `Prop` rather than $\textit{Bool}$, for the reason in
[§4.10](#410-the-condition-of-a-summand-is-a-proposition-not-a-boolean). And the claim reached
is the first reading, not the second: $c_t$ and $g_t$ are terms of *a* language extending the
assumed one with four operations, and that those four are native mCRL2 bag operators is the
question §5.1 flags and [`Target.md`](../../Implementation/docs/Target.md) answers by running
the toolset rather than by proof.

---

## 6. Not formalized

- **Example 1**, the evaluation of an expression under a binding.
- **Semantics of the mu-calculus.** `MuFormula` is syntax only. The thesis gives no semantics
  either, so nothing is missing relative to the notes — but it also means the readings in the
  third column of Example 10 ("the model has no deadlocks", "the model eventually terminates")
  are unverified prose, and `Examples/MuFormulas.lean` says so.
- **The even-number-of-negations side condition** on the two fixpoints. Not enforced by
  `MuFormula`, which the docstring notes; with no semantics there is nothing for it to
  guarantee.
- **Everything about the toolset**: §2.3, §3 and §4 of [mCRL2.md](mCRL2.md) — the
  `lps2pbes`/`pbessolve` pipeline, the shapes of counterexamples, and the encoding notes on
  bags versus lists and on strings. These are not definitions and there is nothing to
  formalize.
- **Graphical notation** for PNs, CPNs and LTSs.
- **Definitions 10, 11 and 12**, which are BPMN (Chapter 4) and outside the scope of these
  notes altogether.

### 6.1 Example 5

Example 5 **is** formalized, in `Examples/CounterNetGraph.lean`. It was the notes' one
*computational* correction to the thesis, so it is worth saying exactly what is checked:

- `occurs_M₀_M₁` … `occurs_M₅_M₆`, the six steps of the chain, each with the binding that
  makes it occur, and `rg_step_M₀` … `rg_step_M₅`, the same six as transitions of
  `net.reachabilityGraph`.
- `not_enabled_t₂_M₅` — **the correction itself**: in $M_5$ the token in $p_2$ carries the
  value 4, so no binding of $t_2$ is enabled, and the seventh step Figure 3.4 draws cannot
  occur.
- `directlyReachable_M₀` … `directlyReachable_M₅`, and `not_directlyReachable_M₆`: each
  marking has exactly the one listed successor, and $M_6$ is a deadlock. This rules out any
  other chain, not just the one Figure 3.4 draws.
- `reachable_M₀_iff`: $\mathcal{R}(M_0)$ is exactly $\{M_1, \ldots, M_6\}$. With `rgStates_eq`
  and `states_injective`, $S = \{M_0\} \cup \mathcal{R}(M_0)$ is the range of an injection from
  `Fin 7` — seven states, not the eight of Figure 3.4.
- `not_mem_R_initialMarking`: $M_0 \notin \mathcal{R}(M_0)$, the premise §3.5.1 of the CPN
  notes argues from, with `step_init` the transition out of the initial state that restricting
  the transition relation to $\mathcal{R}(M_0)$ would drop.

Definitions 6 and 7 for this net were factored into `Examples/CounterNet.lean` first, as
`enabled_t₁_iff` / `enabled_t₂_iff` / `enabled_t₃_iff` and `fire_t₁` / `fire_t₂` / `fire_t₃`;
`Examples/CounterNetLPE.lean` now derives its Example 9 statements from those same lemmas
rather than repeating the computation.

---

## 7. Summary

The formalization is faithful. Every definition on these pages that has mathematical content is
present, and all three recorded corrections to the thesis are carried into the Lean and
checked there: Definition 9's transition relation over $S$, Example 9's condition on the third
summand (`cond_t₃`), and Example 5's seven-state chain (`not_enabled_t₂_M₅` and the
`directlyReachable_*` family). The convention of §2.1.1 on arc expressions of non-existing arcs
is implemented as `CPN.consume` and `CPN.produce`, with `fire_of_not_mem` confirming what it is
for. The proofs are complete and rest on nothing but the standard axioms.

Five gaps this review found have since been closed: the root module's stale
`import Proof.Basic`, which broke a bare `lake build`; the missing field of Definition 5
requiring the type of a variable to be a color of the net, now `CPN.varTypeMem`; Example 5,
now formalized in `Examples/CounterNetGraph.lean` ([§6.1](#61-example-5)); the circularity
in `CPN.toLPE`, which was defined as the very semantics Theorem 1 compares it against and now
builds $c_t$ and $g_t$ from Definition 14's own text
([§5](#5-what-the-translation-is-and-what-theorem-1-therefore-establishes)); and the second
limit that section recorded, `LPE` modelling a transition system rather than syntax. The last
is the newest: `CPN.LPESyntax` is an LPE as data and `CPN.LPESyntax.denote` is the `LPE` it
denotes, so `toLPE_cond` and `toLPE_next` are now proved from evaluation equations where they
used to hold by `rfl` ([§5.2](#52-what-closing-it-actually-took)).

One gap is still worth acting on:

1. Record in the notes the three readings the Lean had to make and the notes do not mention:
   the ill-definedness of bag size for an infinite $S$ ([§4.1](#41-bag-size-is-valued-in-the-extended-naturals)),
   the finiteness hypothesis operation 5 needs ([§4.2](#42-operation-5-gains-a-finiteness-hypothesis)),
   and the reading of Definition 15 ([§4.9](#49-definition-15-is-read-not-transcribed)).

---

## Sources

This page cites no work beyond the thesis. The bibliography entries for the definitions it
discusses are on the pages that state them: [CommonDefinitions.md](CommonDefinitions.md),
[LabeledTransitionSystems.md](LabeledTransitionSystems.md),
[ColoredPetriNets.md](ColoredPetriNets.md), [mCRL2.md](mCRL2.md) and
[Bisimiliarity.md](Bisimiliarity.md).
