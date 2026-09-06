/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Bridge.Cpn

/-!
# Arcs and indices, and `Var(t)` on both sides

`Cpn2mCrl2/Net.lean` keeps the arcs of `A` as a list and `Var(t)` as a list of typed
variables; `Proof/ColoredPetriNets.lean` keeps the arcs as a set of index pairs and `Var(t)`
as a set of names. This file is the dictionary.

The two are the same data, but only because of `Net.Valid`: an arc has an index because
`Net.Valid.inArcPlace` says its place is a place of the net, and it has *one* index because
`Net.Valid.inArcsNodup` says `A` is a set.

## Main results

* `Net.exists_cpnInArc`, `Net.exists_cpnOutArc` : every arc at a transition is the arc of some
  index pair, and of only one.
* `Net.mem_cpnVar_of_mem_Var`, `Net.mem_Var_of_mem_cpnVar` : the two readings of `Var(t)`
  agree.
-/

namespace Cpn2mCrl2

namespace Net

/-! ## An arc is an index pair -/

theorem exists_cpnInArc {N : Net} (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.inArcs)
    (t : N.TIdx) (hat : a.transition = (N.transAt t).name) :
    ∃ (p : N.PIdx) (hp : (p, t) ∈ N.cpnInArc), N.arcOfIn (p, t) hp = a := by
  obtain ⟨p, hp⟩ := exists_placeAt (mem_placeNames_of_placeColor? (h.inArcPlace a ha))
  have hfind : N.inArc? (N.placeAt p).name (N.transAt t).name = some a := by
    rw [hp, ← hat]
    exact Bridge.find?_arc_of_mem h.inArcsNodup ha
  have hsome : (p, t) ∈ N.cpnInArc := by
    show (N.inArc? (N.placeAt p).name (N.transAt t).name).isSome = true
    rw [hfind]; rfl
  exact ⟨p, hsome, Option.some.inj ((N.inArc?_arcOfIn (p, t) hsome).symm.trans hfind)⟩

theorem exists_cpnOutArc {N : Net} (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.outArcs)
    (t : N.TIdx) (hat : a.transition = (N.transAt t).name) :
    ∃ (p : N.PIdx) (hp : (t, p) ∈ N.cpnOutArc), N.arcOfOut (t, p) hp = a := by
  obtain ⟨p, hp⟩ := exists_placeAt (mem_placeNames_of_placeColor? (h.outArcPlace a ha))
  have hfind : N.outArc? (N.transAt t).name (N.placeAt p).name = some a := by
    rw [hp, ← hat]
    exact Bridge.find?_arc_of_mem h.outArcsNodup ha
  have hsome : (t, p) ∈ N.cpnOutArc := by
    show (N.outArc? (N.transAt t).name (N.placeAt p).name).isSome = true
    rw [hfind]; rfl
  exact ⟨p, hsome, Option.some.inj ((N.outArc?_arcOfOut (t, p) hsome).symm.trans hfind)⟩

theorem arcOfIn_mem_pre (N : Net) {p : N.PIdx} {t : N.TIdx} (hp : (p, t) ∈ N.cpnInArc) :
    N.arcOfIn (p, t) hp ∈ N.pre (N.transAt t).name :=
  List.mem_filter.2 ⟨N.arcOfIn_mem _ hp, by simp [(N.arcOfIn_names (p, t) hp).2]⟩

theorem arcOfOut_mem_post (N : Net) {p : N.PIdx} {t : N.TIdx} (hp : (t, p) ∈ N.cpnOutArc) :
    N.arcOfOut (t, p) hp ∈ N.post (N.transAt t).name :=
  List.mem_filter.2 ⟨N.arcOfOut_mem _ hp, by simp [(N.arcOfOut_names (t, p) hp).2]⟩

/-! ## The free variables an arc contributes

`Ein` reads the arc expression at the place's own color, which for a valid net changes
nothing -- `ArcDecl.freeVars_exprAt` -- so the two sides contribute the same variables. -/

theorem freeVars_cpnEin {N : Net} (h : N.Valid) {p : N.PIdx} {t : N.TIdx}
    (hp : (p, t) ∈ N.cpnInArc) :
    ((N.toCPN h).Ein (p, t) hp).1.1.freeVars = (N.arcOfIn (p, t) hp).expr.freeVars :=
  ArcDecl.freeVars_exprAt (N.arcOfIn_color h (p, t) hp)

theorem freeVars_cpnEout {N : Net} (h : N.Valid) {p : N.PIdx} {t : N.TIdx}
    (hp : (t, p) ∈ N.cpnOutArc) :
    ((N.toCPN h).Eout (t, p) hp).1.1.freeVars = (N.arcOfOut (t, p) hp).expr.freeVars :=
  ArcDecl.freeVars_exprAt (N.arcOfOut_color h (t, p) hp)

/-! ## `Var(t)` -/

/-- Every variable of `Var(t)` in the sense of `Cpn2mCrl2/Net.lean` is one in the sense of
`Proof/ColoredPetriNets.lean`. -/
theorem mem_cpnVar_of_mem_Var {N : Net} (h : N.Valid) (t : N.TIdx) {x : String} {σ : ExprTy}
    (hx : (x, σ) ∈ N.Var (N.transAt t)) : x ∈ (N.toCPN h).Var t := by
  have hx' := ListUtil.mem_dedup.1 hx
  rcases List.mem_append.1 hx' with hx' | hx'
  · rcases List.mem_append.1 hx' with hg | hpre
    · exact Or.inl (Or.inl ⟨σ, hg⟩)
    · obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.1 hpre
      obtain ⟨hain, hat⟩ := List.mem_filter.1 ha
      obtain ⟨p, hp, rfl⟩ := exists_cpnInArc h hain t (by simpa using hat)
      refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, ⟨σ, ?_⟩⟩⟩))
      rw [freeVars_cpnEin h hp]
      exact hfa
  · obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.1 hx'
    obtain ⟨haout, hat⟩ := List.mem_filter.1 ha
    obtain ⟨p, hp, rfl⟩ := exists_cpnOutArc h haout t (by simpa using hat)
    refine Or.inr (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, ⟨σ, ?_⟩⟩⟩)
    rw [freeVars_cpnEout h hp]
    exact hfa

/-- And conversely, at the sort `V` gives it. -/
theorem mem_Var_of_mem_cpnVar {N : Net} (h : N.Valid) (t : N.TIdx) {x : String}
    (hx : x ∈ (N.toCPN h).Var t) :
    (x, ExprTy.color (N.varTypeOf x)) ∈ N.Var (N.transAt t) := by
  rcases hx with hx | hx
  · rcases hx with hg | hpre
    · obtain ⟨σ, hσ⟩ := hg
      have hs : Expr.ScopedIn N.vars (N.transAt t).guard := h.guardScoped _ (N.transAt_mem t)
      rw [← Net.varTypeOf_of_mem h (hs (x, σ) hσ)]
      exact N.mem_Var_of_guard hσ
    · obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hpre
      obtain ⟨hpin, σ, hσ⟩ := Set.mem_iUnion.1 hp
      rw [freeVars_cpnEin h hpin] at hσ
      have hs : Expr.ScopedIn N.vars (N.arcOfIn (p, t) hpin).expr :=
        h.inArcScoped _ (N.arcOfIn_mem _ hpin)
      rw [← Net.varTypeOf_of_mem h (hs (x, σ) hσ)]
      exact N.mem_Var_of_pre (N.arcOfIn_mem_pre hpin) hσ
  · obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hpout, σ, hσ⟩ := Set.mem_iUnion.1 hp
    rw [freeVars_cpnEout h hpout] at hσ
    have hs : Expr.ScopedIn N.vars (N.arcOfOut (t, p) hpout).expr :=
      h.outArcScoped _ (N.arcOfOut_mem _ hpout)
    rw [← Net.varTypeOf_of_mem h (hs (x, σ) hσ)]
    exact N.mem_Var_of_post (N.arcOfOut_mem_post hpout) hσ

end Net

end Cpn2mCrl2
