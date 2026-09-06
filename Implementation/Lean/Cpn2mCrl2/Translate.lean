/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Lpe

/-!
# The translation

Definition 14: the LPE a CPN is translated into, built as *terms*.

Definition 14 spells out

    c_t(d, h_t) = (∀ p ∈ pre(t) : E(p,t) ⊆ s_p) ∧ G(t)
    g_t(d, h_t) = ((s_{p₁} \ E(p₁,t)) ∪ E(t,p₁), …, (s_{pₙ} \ E(pₙ,t)) ∪ E(t,pₙ))

and both are written out below, from Definition 14's own text and from nothing else. The
discipline `Proof/MCRL2.lean` sets is kept: the translation does not call `Net.Enabled` or
`Net.fire`, so `Cpn2mCrl2/Correct.lean` is a claim that can fail rather than a restatement.

Unlike in `Proof/`, it can now fail in a second way. There the two sides were transcriptions
of one formula and agreed by `rfl`. Here one side is a Lean predicate and the other is the
*evaluation of a term*, so the identity holds only if the term was assembled correctly out of
the right operations -- which is precisely the content
`Thesis/docs/LeanFormalization.md` §5 says `rfl` does not carry.

## What is total and what is checked

`Net.toLpe` is a total function needing no proof to run. Where Definition 14 relies on a side
condition -- that the arc `(p,t)` carries an expression of type `C(p)_MS` -- the translation
falls back on the empty bag rather than demanding the proof, using `ArcDecl.exprAt`. For a
valid net the fallback never fires, and `Cpn2mCrl2/Correct.lean` shows it. This keeps the
program and the proof separate, as `Implementation/docs/Plan.md` §3 wants.

## Main definitions

* `Net.condTerm` : `c_t`.
* `Net.nextTerm` : one component of `g_t`.
* `Net.toLpe` : Definition 14.
-/

namespace Cpn2mCrl2

namespace Net

variable (N : Net)

/-- One conjunct of `c_t`: `E(p,t) ⊆ s_p`, for an arc of `pre(t)`.

The place parameter `s_p` is the variable named after the place, at bag sort -- see
`Marking.toEnv` for why the two namespaces cannot collide. -/
def _root_.Cpn2mCrl2.ArcDecl.condConjunct (a : ArcDecl) : Expr (.color .bool) :=
  .bagSubset a.expr (.var a.place (.bag a.color))

/-- `c_t(d, h_t) = (∀ p ∈ pre(t) : E(p,t) ⊆ s_p) ∧ G(t)`.

The bounded quantifier is unfolded here, at translation time, into a finite conjunction over
the arcs of `pre(t)`: obligation 3 of `Implementation/docs/Plan.md` §4. -/
def condTerm (t : TransDecl) : Expr (.color .bool) :=
  Expr.andAll ((N.pre t.name).map ArcDecl.condConjunct ++ [t.guard])

/-- `E(p,t)` as a term of the place's own bag sort.

`ArcDecl.exprAt` reads the arc expression at the place's color; the two agree for a valid net
and the empty bag stands in otherwise. Where there is no arc the empty bag is what Definition
7's convention on non-existing arcs prescribes anyway. -/
def consumeTerm (t : TransDecl) (d : PlaceDecl) : Expr (.bag d.color) :=
  match N.inArc? d.name t.name with
  | some a => a.exprAt d.color
  | none => .emptyBag d.color

/-- `E(t,p)` as a term of the place's own bag sort, read as `Net.consumeTerm` is. -/
def produceTerm (t : TransDecl) (d : PlaceDecl) : Expr (.bag d.color) :=
  match N.outArc? t.name d.name with
  | some a => a.exprAt d.color
  | none => .emptyBag d.color

/-- `g_t` at the place `d`: `(s_p \ E(p,t)) ∪ E(t,p)`. -/
def nextTerm (t : TransDecl) (d : PlaceDecl) : Expr (.bag d.color) :=
  .bagUnion (.bagDiff (.var d.name (.bag d.color)) (N.consumeTerm t d)) (N.produceTerm t d)

/-- The summand of `t`. `H_t` is `Var(t)`, `a_t` is `t` itself carrying no parameters. -/
def summandOf (t : TransDecl) : Summand where
  binder := N.Var t
  cond := N.condTerm t
  act := t.name
  next := N.places.map fun d => (d.name, ⟨d.color, N.nextTerm t d⟩)

/-- **Definition 14 (Translation).**
The LPE built from a CPN: one summand per transition, one bag-sorted parameter per place, and
`d₀ = (I(p₁)⟨⟩, …, I(pₙ)⟨⟩)` -- emitted as the closed initialization *terms*, which denote
those values without the translator ever evaluating anything. -/
def toLpe : Lpe where
  sorts := N.colors
  params := N.places.map fun d => (d.name, d.color)
  acts := N.transNames
  summands := N.transitions.map N.summandOf
  init := N.places.map fun d => (d.name, ⟨d.color, d.init⟩)

@[simp] theorem toLpe_params : N.toLpe.params = N.places.map fun d => (d.name, d.color) := rfl

@[simp] theorem toLpe_acts : N.toLpe.acts = N.transNames := rfl

@[simp] theorem toLpe_summands : N.toLpe.summands = N.transitions.map N.summandOf := rfl

@[simp] theorem summandOf_act (t : TransDecl) : (N.summandOf t).act = t.name := rfl

@[simp] theorem summandOf_cond (t : TransDecl) : (N.summandOf t).cond = N.condTerm t := rfl

@[simp] theorem summandOf_binder (t : TransDecl) : (N.summandOf t).binder = N.Var t := rfl

end Net

end Cpn2mCrl2
