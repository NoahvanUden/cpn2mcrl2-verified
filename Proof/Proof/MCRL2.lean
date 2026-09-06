/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.ColoredPetriNets

/-!
# mCRL2

Definitions 13, 14, 15 and 18 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Chapters 5 and 6: the Linear Process Equation, the translation of
a Colored Petri Net into one, the LTS an LPE induces, and the modal mu-calculus.

See `Thesis/docs/mCRL2.md` for the prose version. The rest of that page -- the model
checking pipeline, the shape of counterexamples, and the encoding notes on markings and
strings -- is about the toolset rather than about definitions, and has nothing to formalize.

## Implementation notes

**The condition `c_k` is a predicate, not a `Bool`.** Definition 13 types it as
`c_k : D × H_k → Bool`, which is what an mCRL2 data expression of sort `Bool` is. Here it is
`D → H_k → Prop`. The translation of Definition 14 is the reason: the condition it builds
contains a bag inclusion `E(p, t) ⊆ s_p`, and bag inclusion over an arbitrary color is not
decidable, so it cannot be given as a `Bool` without assuming decidability throughout. A
`Bool`-valued condition is the special case `fun d h => c k d h = true`. Making it a `Bool`
would need `Bag` to be finitely supported, which is a departure from Definition 1 as printed;
`Thesis/docs/LeanFormalization.md` §4.10 records the choice, and the two translators of
`Implementation/` make the other one.

**The action `a_k` is a label.** Definition 13 writes the shape of an LPE with `a_k(d, h_k)`
but lists `a_k ∈ Act` among the components, and Definition 15 uses `a_k` alone as the label
of a transition. It is modelled here as the label `act k ∈ Act`, which is also what the
translation produces: the note under Definition 14 records that the action it emits carries
no parameters.

**`d₀` is not part of the LPE.** Definition 13 does not mention an initial state; Definition
15 introduces it as "for a given `d₀ ∈ D`". So `LPE.semantics` takes it as an argument, and
the translation supplies `CPN.toLPEInit` alongside `CPN.toLPE`.

**The translation is syntactic, and `LPE` is what it denotes.** Definition 13 gives `c_k` and
`g_k` as functions, and `LPE` transcribes it that way. Definition 14 does not: it *writes*
`c_t` and `g_t` as expressions, out of the CPN's guard and arc expressions and five
operations applied to them. `CPN.Cond` and `CPN.Term` are those expressions as syntax,
`CPN.LPESyntax` is the LPE Definition 14 builds, and `CPN.LPESyntax.denote` is the `LPE` it
denotes. `CPN.toLPE_cond` and `CPN.toLPE_next` are therefore theorems, proved from the
evaluation equations, where before they held by `rfl`. See `CPN.Term` for what the syntactic
layer does and does not claim.

## Main definitions

* `LPE Act` : Definition 13.
* `LPE.semantics` : Definition 15, the LTS induced by an LPE.
* `CPN.Term`, `CPN.Cond` : the syntax Definition 14 assembles, with `Term.eval` and
  `Cond.eval` its evaluation equations.
* `CPN.LPESyntax`, `CPN.LPESyntax.denote` : an LPE as syntax, and the `LPE` it denotes.
* `CPN.toLPESyntax`, `CPN.toLPE`, `CPN.toLPEInit` : Definition 14, the translation of a CPN.
* `MuFormula` : Definition 18, the syntax of the modal mu-calculus.
-/

universe u v w x y

/-! ## Linear Process Equations -/

/-- **Definition 13 (Linear Process Equation (LPE)).**
An LPE is a specification of the shape

    Spec(d : D) = ∑_{k ∈ K} ∑_{h_k : H_k} c_k(d, h_k) → a_k · Spec(g_k(d, h_k))

given by a datatype `D` of states, an index set `K`, and for each `k ∈ K` a datatype `H_k`
of summation variables, a condition `c_k`, an action label `a_k ∈ Act` and a next state
`g_k`.

The summation `∑_{k ∈ K}` of Section 1.2 is a shorthand for the choice between the
summands, so an LPE is exactly the family of summands indexed by `K`. -/
structure LPE (Act : Type u) where
  /-- `D`, the datatype of the state. -/
  D : Type v
  /-- `K`, the index set of the summands. -/
  K : Type w
  /-- `H_k`, the datatype summed over in summand `k`. -/
  H : K → Type x
  /-- `c_k : D × H_k → Bool`, the condition of summand `k`. -/
  cond : (k : K) → D → H k → Prop
  /-- `a_k ∈ Act`, the action label of summand `k`. -/
  act : K → Act
  /-- `g_k : D × H_k → D`, the next state of summand `k`. -/
  next : (k : K) → D → H k → D

namespace LPE

variable {Act : Type u}

/-- **Definition 15 (Semantics of LPE).**
The LTS `(S, L, →, s₀)` induced by an LPE with a given initial state `d₀`: the states are
`D`, the actions are `Act`, the initial state is `d₀`, and there is a transition
`d -a_k→ d'` whenever some value of the summation variable `h_k` satisfies the condition of
summand `k` and takes `d` to `d'`.

Definition 15 writes the source of a transition as `d⟨b⟩` for a binding `b ∈ B[H_k]`. A
state of this LTS is already a value of `D` and `b` assigns a value to the summation
variable `h_k` only, so `d⟨b⟩` is `d`; the binding is the `h` quantified over here. -/
def semantics (Spec : LPE Act) (d₀ : Spec.D) : LTS Spec.D Act where
  step d a d' := ∃ (k : Spec.K) (h : Spec.H k),
    Spec.act k = a ∧ Spec.cond k d h ∧ d' = Spec.next k d h
  init := d₀

end LPE

/-! ## Translating a CPN to an LPE -/

namespace CPN

variable {L : ExprLang.{u, v, w, x}} {P T : Type y}

/-! ### The syntax Definition 14 assembles

Definition 14 does not produce `c_t` and `g_t` out of nothing. Their ingredients -- the guard
`G(t)` and the arc expressions `E(p,t)`, `E(t,p)` -- are already expressions of the language
Chapter 2 assumes. What Definition 14 adds is the layer around them: the state components
`s_p`, the conjunction, the bag inclusion, the union and the difference. `Term` and `Cond`
are that layer, as syntax; the ambient expressions enter through one constructor each and
are not looked inside.

What that does and does not establish is worth stating plainly. Chapter 2 never says the
tool's expression language contains bag operations, so assuming it does --
by giving `ExprLang` new fields -- would be filling a gap the thesis leaves open. Building
the operations instead assumes nothing about the tool, and leaves `ExprLang`, Definition 5
and every example untouched. What is claimed is exactly: *`c_t` and `g_t` are terms whose
only primitives beyond the tool's own expressions are `∧`, `⊆`, `∪`, `\` and the state
components.* Whether those five print as well-formed mCRL2 is a question about text, which
`Thesis/docs/LeanFormalization.md` §5.1 rules out of reach here and
`Implementation/docs/Target.md` §4 answers by running the toolset.

No product former is needed, and neither is a tupling operation. Definition 13's `D` and
`H_t` are tuples, but they are only ever *bound* -- `d` is the parameter list of the process
and `h_t` the variable list of the sum -- so the tupling of `g_t` is the indexing of `next`
by a place and the projection `s_p` is a constructor. `Implementation/Lean/README.md` §4.1
reaches the same conclusion from the mCRL2 side. -/

/-- A term of Definition 14's next state at place `p`: a value of sort `C(p)_MS`.

`Term` is indexed by the place rather than by an `ExprTy`, because `C(p)_MS` is the only sort
Definition 14's next state has. `V` is the set of variables its ambient expressions may use;
in the translation it is `Var(t)`, the variables the summand binds. -/
inductive Term (N : CPN L P T) (V : Set L.Var) (p : P) where
  /-- `s_p`, the component of the state holding the tokens of `p`. -/
  | state
  /-- An expression of the ambient language, with its free variables inside `V`. -/
  | expr (e : L.ExprOn V (.bag (N.C p)))
  /-- The empty bag, which the convention of Section 2.1.1 gives to a non-existing arc. -/
  | empty
  /-- `∪`. -/
  | union (a b : Term N V p)
  /-- `\`. -/
  | diff (a b : Term N V p)

/-- A term of Definition 14's condition `c_t`: the bag inclusions over `pre(t)`, the guard,
and the conjunction that joins them. -/
inductive Cond (N : CPN L P T) (V : Set L.Var) where
  /-- `a ⊆ b`, at the place whose color both sides have. -/
  | subset (p : P) (a b : Term N V p)
  /-- `G(t)`, an expression of the ambient language. -/
  | guard (e : L.ExprOn V (.color L.boolColor))
  /-- The empty conjunction, `true`. -/
  | triv
  /-- `∧`. -/
  | and (a b : Cond N V)

namespace Term

variable {N : CPN L P T} {V : Set L.Var} {p : P}

/-- The value of a term: the marking `d` supplies the state components and the binding `b`
supplies the variables of the ambient expressions.

The five clauses are the evaluation equations that `CPN.toLPE_next` is proved from. -/
def eval : N.Term V p → N.Marking → L.Binding V → Bag (L.val (N.C p))
  | .state, d, _ => d p
  | .expr e, _, b => ExprLang.evalOn e.1 e.2 b
  | .empty, _, _ => ∅
  | .union a c, d, b => a.eval d b ∪ c.eval d b
  | .diff a c, d, b => a.eval d b \ c.eval d b

@[simp] theorem eval_state (d : N.Marking) (b : L.Binding V) :
    (Term.state : N.Term V p).eval d b = d p := rfl

@[simp] theorem eval_expr (e : L.ExprOn V (.bag (N.C p))) (d : N.Marking)
    (b : L.Binding V) : (Term.expr e).eval d b = ExprLang.evalOn e.1 e.2 b := rfl

@[simp] theorem eval_empty (d : N.Marking) (b : L.Binding V) :
    (Term.empty : N.Term V p).eval d b = ∅ := rfl

@[simp] theorem eval_union (a c : N.Term V p) (d : N.Marking) (b : L.Binding V) :
    (a.union c).eval d b = a.eval d b ∪ c.eval d b := rfl

@[simp] theorem eval_diff (a c : N.Term V p) (d : N.Marking) (b : L.Binding V) :
    (a.diff c).eval d b = a.eval d b \ c.eval d b := rfl

end Term

namespace Cond

variable {N : CPN L P T} {V : Set L.Var}

/-- The truth of a condition under a marking and a binding.

It lands in `Prop` and not in `Bool` for the reason in the implementation notes above: the
`subset` clause is bag inclusion over an arbitrary color. The four clauses are the evaluation
equations that `CPN.toLPE_cond` is proved from. -/
def eval : N.Cond V → N.Marking → L.Binding V → Prop
  | .subset _ a c, d, b => a.eval d b ⊆ c.eval d b
  | .guard e, _, b => ExprLang.Holds e.1 e.2 b
  | .triv, _, _ => True
  | .and a c, d, b => a.eval d b ∧ c.eval d b

@[simp] theorem eval_subset (p : P) (a c : N.Term V p) (d : N.Marking) (b : L.Binding V) :
    (Cond.subset p a c).eval d b = (a.eval d b ⊆ c.eval d b) := rfl

@[simp] theorem eval_guard (e : L.ExprOn V (.color L.boolColor)) (d : N.Marking)
    (b : L.Binding V) : (Cond.guard e).eval d b = ExprLang.Holds e.1 e.2 b := rfl

@[simp] theorem eval_triv (d : N.Marking) (b : L.Binding V) :
    (Cond.triv : N.Cond V).eval d b = True := rfl

@[simp] theorem eval_and (a c : N.Cond V) (d : N.Marking) (b : L.Binding V) :
    (a.and c).eval d b = (a.eval d b ∧ c.eval d b) := rfl

end Cond

/-- An LPE of a CPN as syntax: the condition of each summand, the next state of each summand
at each place, and the initial expression of each place.

The remaining components of Definition 13 are not data here. `K` is `T`, `D` is the marking,
`H_t` is a binding of `Var(t)` and `a_t` is `t`, all of them fixed by Definition 14 rather
than chosen, so `denote` supplies them. -/
structure LPESyntax (N : CPN L P T) where
  /-- `c_t`, for each transition. -/
  cond : (t : T) → N.Cond (N.Var t)
  /-- `g_t` at each place, for each transition. -/
  next : (t : T) → (p : P) → N.Term (N.Var t) p
  /-- `d₀` at each place, as the closed expression `I(p)` of Definition 5. -/
  init : (p : P) → L.ExprOn ∅ (.bag (N.C p))

/-- The LPE that a syntactic LPE denotes: Definition 13's `c_k` and `g_k` are the evaluations
of the terms. This is the arrow that makes `LPE` the semantics of the syntax rather than the
translation's output. -/
def LPESyntax.denote {N : CPN L P T} (S : N.LPESyntax) : LPE T where
  D := N.Marking
  K := T
  H := N.TransBinding
  cond t d b := (S.cond t).eval d b
  act := id
  next t d b := fun p => (S.next t p).eval d b

variable (N : CPN L P T)

/-! ### Definition 14 -/

open Classical in
/-- `E(p, t)` as a term, for an arbitrary place `p`, read with the convention of Section
2.1.1 on arc expressions of non-existing arcs -- the same convention `CPN.consume` reads. -/
noncomputable def consumeTerm (t : T) (p : P) : N.Term (N.Var t) p :=
  if h : (p, t) ∈ N.inArc then .expr ⟨(N.Ein (p, t) h).1, N.vars_Ein_subset h⟩ else .empty

open Classical in
/-- `E(t, p)` as a term, read with the same convention as `consumeTerm`. -/
noncomputable def produceTerm (t : T) (p : P) : N.Term (N.Var t) p :=
  if h : (t, p) ∈ N.outArc then .expr ⟨(N.Eout (t, p) h).1, N.vars_Eout_subset h⟩ else .empty

/-- `g_t` at place `p`, which Definition 14 writes as `(s_p \ E(p,t)) ∪ E(t,p)`. -/
noncomputable def nextTerm (t : T) (p : P) : N.Term (N.Var t) p :=
  .union (.diff .state (N.consumeTerm t p)) (N.produceTerm t p)

/-- An enumeration of `pre(t)`.

This is the first thing `PetriNet.finitePlaces` is used for. `Thesis/docs/LeanFormalization.md`
§4.5 records that every side condition of Definition 5 is inert, and §5.1 predicts that
finiteness of `P` stops being inert exactly here, because the bounded conjunction of `c_t`
has to be unfolded into a finite one. -/
noncomputable def preList (t : T) : List P :=
  haveI := N.finitePlaces
  (Set.toFinite (N.pre t)).toFinset.toList

theorem mem_preList {t : T} {p : P} : p ∈ N.preList t ↔ p ∈ N.pre t := by
  simp [preList]

/-- The finite conjunction `⋀_{p ∈ ps} E(p,t) ⊆ s_p`.

Definition 14 writes `∀ p ∈ pre(t)`, a quantifier bounded by a set that is known when the
translation runs. Unfolding it here rather than asking the term language for a quantifier is
what `Implementation/docs/Plan.md` §4 lists as the third proof obligation. -/
noncomputable def condOf (t : T) : List P → N.Cond (N.Var t)
  | [] => .triv
  | p :: ps => .and (.subset p (N.consumeTerm t p) .state) (condOf t ps)

/-- `c_t`, which Definition 14 writes as `(∀ p ∈ pre(t) : E(p,t) ⊆ s_p) ∧ G(t)`. -/
noncomputable def condTerm (t : T) : N.Cond (N.Var t) :=
  .and (N.condOf t (N.preList t)) (.guard ⟨(N.G t).1, N.vars_G_subset t⟩)

/-- **Definition 14 (Translation).**
The LPE produced from a CPN: the index set `K` is the set of transitions `T`, the state `D`
is the tuple of bags of tokens holding one bag per place, `H_t` is the tuple of values of
the variables of `t`, and `a_t` is `t` itself, carrying no parameters.

`D` is `N.Marking` and `H_t` is `N.TransBinding t`: the tuple `(S_{p₁} × … × S_{pₙ})` with
one component per place *is* a marking, and the tuple `(Type[v₁] × … × Type[vₙ])` over
`v ∈ Var(t)` *is* a binding of `Var(t)`, which is what `B[H_t]` ranges over in Definition 15.

Definition 14 spells `c_t` and `g_t` out as

    c_t(d, h_t) = (∀ p ∈ pre(t) : E(p,t) ⊆ s_p) ∧ G(t)
    g_t(d, h_t) = ((s_{p₁} \ E(p₁,t)) ∪ E(t,p₁), …, (s_{pₙ} \ E(pₙ,t)) ∪ E(t,pₙ))

and both are built here, as `condTerm` and `nextTerm`, from Definition 14's own text.

They could instead have been given by `Enabled` and `fire`: the two right-hand sides above
are, symbol for symbol, the enabledness condition of Definition 6 and the marking reached in
Definition 7, as Section 1.3 of the notes says they should be. That is deliberately *not*
done. Theorem 1 is the claim that the reachability graph of Definition 9 and the LTS this
translation induces have the same behavior; if the translation were defined as the semantics
it is being compared against, the two would be one object under two names and the theorem
could not fail -- a slip introduced into `Enabled` (quantifying over `post(t)` rather than
`pre(t)`, say, which is the slip the thesis itself makes) would change both sides together
and still typecheck.

Keeping them separate makes the identification a claim instead: `toLPE_cond` and
`toLPE_next` below. Neither holds by `rfl`. One side is a predicate on markings and
bindings; the other is the *evaluation of a term* this translation assembled, and they agree
only because it was assembled out of the right operations.

What *is* shared with Definitions 6 and 7 is how the components of the CPN are read:
`pre`, `G`, and the convention of Section 2.1.1 on arc expressions of non-existing arcs.
Those are the interpretation of `E` and `G` themselves, not part of the translation, and
Definition 14 refers to them exactly as Definitions 6 and 7 do. -/
noncomputable def toLPESyntax : N.LPESyntax where
  cond := N.condTerm
  next := N.nextTerm
  init := N.I

/-- The LPE of Definition 14, as the transition-system schema of Definition 13 that the
syntax of `toLPESyntax` denotes. -/
noncomputable def toLPE : LPE T := N.toLPESyntax.denote

@[simp] theorem toLPE_K : N.toLPE.K = T := rfl

@[simp] theorem toLPE_D : N.toLPE.D = N.Marking := rfl

@[simp] theorem toLPE_H (t : T) : N.toLPE.H t = N.TransBinding t := rfl

@[simp] theorem toLPE_act (t : T) : N.toLPE.act t = t := rfl

/-! ### The translation computes the semantics

`toLPE_cond` and `toLPE_next` are the two halves of it, and they carry the content that the
definition of `toLPE` deliberately does not assume. -/

@[simp] theorem eval_consumeTerm (t : T) (p : P) (d : N.Marking) (b : N.TransBinding t) :
    (N.consumeTerm t p).eval d b = consume b p := by
  classical
  by_cases h : (p, t) ∈ N.inArc <;>
    simp [consumeTerm, consume, consumedBy, h]

@[simp] theorem eval_produceTerm (t : T) (p : P) (d : N.Marking) (b : N.TransBinding t) :
    (N.produceTerm t p).eval d b = produce b p := by
  classical
  by_cases h : (t, p) ∈ N.outArc <;>
    simp [produceTerm, produce, producedBy, h]

/-- The conjunction `condOf` unfolds over a list of places holds exactly when each of those
places has the tokens the arc into `t` asks for. -/
theorem eval_condOf (t : T) (d : N.Marking) (b : N.TransBinding t) (ps : List P) :
    (N.condOf t ps).eval d b ↔ ∀ p ∈ ps, consume b p ⊆ d p := by
  induction ps with
  | nil => simp [condOf]
  | cons p ps ih => simp [condOf, ih]

/-- The bag inclusions of `condTerm` are the inclusions of Definition 6.

This is where the bounded quantifier of Definition 6 and the finite conjunction `condOf`
unfolds meet: `mem_preList` turns the enumeration back into `pre(t)`, and `consume` agrees
with `consumedBy` on the places of `pre(t)` by the convention of Section 2.1.1. -/
theorem eval_condOf_preList (t : T) (d : N.Marking) (b : N.TransBinding t) :
    (N.condOf t (N.preList t)).eval d b ↔
      ∀ (p : P) (h : p ∈ N.pre t), consumedBy b p h ⊆ d p := by
  rw [N.eval_condOf]
  constructor
  · intro h p hp
    have hin : (p, t) ∈ N.inArc := hp
    have := h p (N.mem_preList.2 hp)
    simpa [consume, hin] using this
  · intro h p hp
    have hp' : p ∈ N.pre t := N.mem_preList.1 hp
    have hin : (p, t) ∈ N.inArc := hp'
    simpa [consume, hin] using h p hp'

/-- The condition `c_t` that Definition 14 builds evaluates to the enabledness of `(t, b)` in
`d` of Definition 6. -/
theorem eval_condTerm (t : T) (d : N.Marking) (b : N.TransBinding t) :
    (N.condTerm t).eval d b ↔ Enabled d b := by
  simp only [condTerm, Cond.eval_and, Cond.eval_guard, N.eval_condOf_preList t d b,
    Enabled]

@[simp] theorem toLPE_cond (t : T) (d : N.Marking) (b : N.TransBinding t) :
    N.toLPE.cond t d b = Enabled d b :=
  propext (N.eval_condTerm t d b)

/-- The next state `g_t` that Definition 14 builds evaluates, at each place, to the bag that
Definition 7 leaves there. -/
theorem eval_nextTerm (t : T) (p : P) (d : N.Marking) (b : N.TransBinding t) :
    (N.nextTerm t p).eval d b = fire d b p := by
  simp [nextTerm, fire]

/-- The next state `g_t` that Definition 14 builds evaluates to the marking that `(t, b)`
leads to in Definition 7. -/
@[simp] theorem toLPE_next (t : T) (d : N.Marking) (b : N.TransBinding t) :
    N.toLPE.next t d b = fire d b :=
  funext fun p => N.eval_nextTerm t p d b

/-- The initial state `d₀ = (M₀(p₁), …, M₀(pₙ))` of the translated LPE, which is the initial
marking of the CPN. `I(p)` is a closed expression of the ambient language already, so this
component of the LPE was syntactic before the rest of it was. -/
noncomputable def toLPEInit : N.toLPE.D := fun p => ExprLang.evalClosed (N.toLPESyntax.init p)

theorem toLPEInit_eq_initialMarking : N.toLPEInit = N.initialMarking := rfl

/-- The LTS induced by the translation of a CPN: Definition 15 applied to Definition 14. -/
noncomputable def toLPESemantics : LTS N.Marking T := N.toLPE.semantics N.toLPEInit

/-- A transition of the induced LTS is a binding element occurring, without the restriction
to reachable markings that the reachability graph of Definition 9 carries. -/
theorem toLPESemantics_step (d : N.Marking) (t : T) (d' : N.Marking) :
    N.toLPESemantics.step d t d' ↔ ∃ b : N.TransBinding t, Occurs d b d' := by
  constructor
  · rintro ⟨k, b, rfl, hc, rfl⟩
    exact ⟨b, Eq.mp (N.toLPE_cond k d b) hc, N.toLPE_next k d b⟩
  · rintro ⟨b, hc, rfl⟩
    exact ⟨t, b, rfl, Eq.mpr (N.toLPE_cond t d b) hc, (N.toLPE_next t d b).symm⟩

end CPN


/-! ## The modal mu-calculus -/

/-- **Definition 18 (the modal mu-calculus).**
The syntax of the mu-calculus in its basic form, over the actions `L` of an LTS and a set
`Var` of fixpoint variables:

    φ ::= false | true | ¬φ | φ ∨ φ | φ ∧ φ | ⟨a⟩φ | [a]φ | μX.φ | νX.φ | X

The thesis requires, so that the fixpoints `μX.φ` and `νX.φ` exist, that every occurrence of
`X` in `φ` is preceded by an even number of negations. That is a side condition on formulas,
not part of the grammar, and it is not enforced by this datatype; the thesis defines no
semantics for the logic, so nothing here depends on it. -/
inductive MuFormula (L : Type u) (Var : Type v) where
  /-- `false`. -/
  | false
  /-- `true`. -/
  | true
  /-- `¬φ`. -/
  | neg (φ : MuFormula L Var)
  /-- `φ ∨ ψ`. -/
  | or (φ ψ : MuFormula L Var)
  /-- `φ ∧ ψ`. -/
  | and (φ ψ : MuFormula L Var)
  /-- `⟨a⟩φ`, the action `a` can be done, reaching a state satisfying `φ`. -/
  | dia (a : L) (φ : MuFormula L Var)
  /-- `[a]φ`, every `a` step reaches a state satisfying `φ`. -/
  | box (a : L) (φ : MuFormula L Var)
  /-- `μX.φ`, the least fixpoint. -/
  | mu (X : Var) (φ : MuFormula L Var)
  /-- `νX.φ`, the greatest fixpoint. -/
  | nu (X : Var) (φ : MuFormula L Var)
  /-- A fixpoint variable. -/
  | var (X : Var)
  deriving Repr

namespace MuFormula

variable {L : Type u} {Var : Type v}

/-! ### Shorthand notation

Section 2.2 of the notes writes the shorthands over a finite set of actions `A ⊆ L`. A
finite set of actions is given here as a `List L`, which fixes the order and the bracketing
of the disjunction `⋁_{a ∈ A}` and the conjunction `⋀_{a ∈ A}` that the thesis leaves
unspecified. The empty list gives the empty disjunction `false` and the empty conjunction
`true`. -/

/-- `⟨A⟩φ = ⋁_{a ∈ A} ⟨a⟩φ`. -/
def diaSet : List L → MuFormula L Var → MuFormula L Var
  | [], _ => .false
  | a :: as, φ => .or (.dia a φ) (diaSet as φ)

/-- `[A]φ = ⋀_{a ∈ A} [a]φ`. -/
def boxSet : List L → MuFormula L Var → MuFormula L Var
  | [], _ => .true
  | a :: as, φ => .and (.box a φ) (boxSet as φ)

/-- `⟨A*⟩φ = μX.(⟨A⟩X ∨ φ)`. The fixpoint variable is a parameter here; the thesis leaves
the choice of a fresh `X` implicit. -/
def diaStar (X : Var) (A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  .mu X (.or (diaSet A (.var X)) φ)

/-- `[A*]φ = νX.([A]X ∧ φ)`. -/
def boxStar (X : Var) (A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  .nu X (.and (boxSet A (.var X)) φ)

section Complement

variable [DecidableEq L]

/-- `⟨Ā⟩φ = ⟨L \ A⟩φ`. The actions `L` have to be given as a list `all`: the notes write the
complement against the whole action set, which presupposes an enumeration of it. Writing
*true* in place of a set of actions, as Section 2.2 does for the complete set `L`, is
passing `all` itself. -/
def diaCompl (all A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  diaSet (all.filter fun a => decide (a ∉ A)) φ

/-- `[Ā]φ = [L \ A]φ`. -/
def boxCompl (all A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  boxSet (all.filter fun a => decide (a ∉ A)) φ

end Complement

end MuFormula
