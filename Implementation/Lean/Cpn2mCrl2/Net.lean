/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Expr

/-!
# Colored Petri Nets

Definitions 4 and 5 of the thesis, as data a program can hold, together with the validation
that turns that data into a CPN.

`Proof/ColoredPetriNets.lean` makes `P` and `T` Lean *types*, which discharges the finiteness
of Definition 4 and the disjointness `P ∩ T = ∅` by construction. A file cannot carry a type,
so here they are lists of named declarations and both conditions become checks. That is the
shift `Implementation/docs/Plan.md` §3 predicts:

> The Definition 5 side conditions stop being decorative.

`Thesis/docs/LeanFormalization.md` §4.5 records that `finitePlaces`, `finiteTransitions`,
`finiteColors`, `finiteV`, `boolMem`, `colorMem` and `varTypeMem` are declared in `Proof/` and
used by no proof. Every one of them appears below as a field of `Net.Valid`, and `boolMem`,
`colorMem` and `varTypeMem` are what let `Cpn2mCrl2/Print.lean` emit the sort declarations at
all.

## Implementation notes

**Validity is a separate predicate, not a field of the structure.** `Net` is plain data, so
the JSON importer can build one and then check it; `Net.Valid` is the conjunction of the T1
checks of `Implementation/docs/InputFormat.md` §4.3, decidable, and the hypothesis every
theorem in `Cpn2mCrl2/Correct.lean` runs on. This is exactly the split
`Implementation/docs/Plan.md` §3 draws between the importer and the verified core.

**An arc carries the color of its place.** Definition 5 requires `E(p,t)` to have type
`C(p)_MS`; here the arc's expression has type `Bag(a.color)` by construction and
`Net.Valid.inArcPlace` says `a.color` is the color of the place `a` names. That is check 5 of
`InputFormat.md` §4.3, and splitting it this way is what keeps `Net` first-order: the
alternative, indexing the arc by the place's color, makes the structure dependent and the
importer much harder to write.

**Names are one namespace.** Definition 4 requires `P ∩ T = ∅`. The emitted mCRL2 puts place
names and variable names in one scope -- the place parameters of `proc` and the `sum`
variables of a summand -- so `Net.Valid.namesDisjoint` extends the requirement to `V`.

> **Addition to the thesis.** Definition 4 requires only `P ∩ T = ∅`. `Net.Valid.namesDisjoint` also requires the names of `V` to be distinct from those of `P` and `T`, because the emitted specification binds a place and a variable in the same scope.

## Main definitions

* `Net` : Definition 5, as data.
* `Net.Valid` : the T1 checks of `InputFormat.md` §4.3.
* `Net.pre`, `Net.post`, `Net.Var` : `pre(t)`, `post(t)` and `Var(t)`.
-/

namespace Cpn2mCrl2

/-- A place, with its color and its initialization expression `I(p)`. -/
structure PlaceDecl where
  /-- The name of the place. -/
  name : String
  /-- `C(p)`, the color of the place. -/
  color : Color
  /-- `I(p)`, a closed expression of type `C(p)_MS`. -/
  init : Expr (.bag color)

/-- A transition, with its guard `G(t)`. -/
structure TransDecl where
  /-- The name of the transition. -/
  name : String
  /-- `G(t)`, an expression of type `Bool`. -/
  guard : Expr (.color .bool)

/-- An arc together with its expression `E(a)`.

The same structure serves both sides of `A ⊆ (P × T) ∪ (T × P)`; which side an arc is on is
recorded by the field of `Net` it appears in, exactly as `Proof/ColoredPetriNets.lean` splits
`inArc` from `outArc`. -/
structure ArcDecl where
  /-- The place the arc is attached to. -/
  place : String
  /-- The transition the arc is attached to. -/
  transition : String
  /-- The color of that place. `Net.Valid` requires it to be so. -/
  color : Color
  /-- `E(a)`, an expression of type `C(p)_MS`. -/
  expr : Expr (.bag color)

/-- The expression of an arc read at the color `c`, or the empty bag if the arc is not at
that color.

The fallback never happens for a valid net -- `Net.Valid.inArcPlace` and
`Net.Valid.outArcPlace` are exactly the statement that it does not -- but having it lets the
translation be a total function `Net → Lpe` that needs no proof to run, with the proof
appearing where `Implementation/docs/Plan.md` §2 puts it: in T2, not in the program. -/
def ArcDecl.exprAt (a : ArcDecl) (c : Color) : Expr (.bag c) :=
  if h : a.color = c then h ▸ a.expr else .emptyBag c

@[simp] theorem ArcDecl.exprAt_self (a : ArcDecl) : a.exprAt a.color = a.expr := by
  simp [exprAt]

theorem ArcDecl.eval_exprAt {a : ArcDecl} {c : Color} (h : a.color = c) (env : Env) :
    Expr.eval (a.exprAt c) env = Expr.eval a.expr env := by
  subst h; simp

theorem ArcDecl.freeVars_exprAt {a : ArcDecl} {c : Color} (h : a.color = c) :
    (a.exprAt c).freeVars = a.expr.freeVars := by
  subst h; simp

/-- Reading an arc expression at another color leaves its free variables where they were, so
scoping survives. The mismatched case is the empty bag, which has none. -/
theorem ArcDecl.scopedIn_exprAt {Γ : Ctx} {a : ArcDecl} (hs : Expr.ScopedIn Γ a.expr)
    (c : Color) : Expr.ScopedIn Γ (a.exprAt c) := by
  by_cases hc : a.color = c
  · intro p hp
    rw [ArcDecl.freeVars_exprAt hc] at hp
    exact hs p hp
  · have he : a.exprAt c = Expr.emptyBag c := by simp [ArcDecl.exprAt, hc]
    intro p hp
    rw [he] at hp
    cases hp

/-- **Definition 5 (Colored Petri Net)**, as data.

The tuple `(P, T, A, Σ, V, C, E, G, I)`, component for component: `places` carries `P`, `C`
and `I`; `transitions` carries `T` and `G`; `inArcs` and `outArcs` carry the two sides of `A`
together with `E`; `colors` is `Σ` and `vars` is `V` with `Type[.]`.

`Var(t)` and `pre(t)`/`post(t)` are derived, not stored, as
`Implementation/docs/InputFormat.md` §1 says they must be. -/
structure Net where
  /-- `Σ`, the colors of the net. -/
  colors : List Color
  /-- `V`, the typed variables of the net. Every entry is a `.color`; `Net.Valid` says so. -/
  vars : Ctx
  /-- `P`, with `C` and `I`. -/
  places : List PlaceDecl
  /-- `T`, with `G`. -/
  transitions : List TransDecl
  /-- The arcs of `A` in `P × T`, with `E`. -/
  inArcs : List ArcDecl
  /-- The arcs of `A` in `T × P`, with `E`. -/
  outArcs : List ArcDecl

namespace Net

variable (N : Net)

/-! ### Lookups -/

/-- The names of the places. -/
def placeNames : List String := N.places.map PlaceDecl.name

/-- The names of the transitions. -/
def transNames : List String := N.transitions.map TransDecl.name

/-- The names of the variables. -/
def varNames : List String := N.vars.map Prod.fst

/-- `C(p)`, if `p` is a place of the net. -/
def placeColor? (p : String) : Option Color :=
  (N.places.find? fun d => d.name == p).map PlaceDecl.color

/-- The arc `(p, t)`, if there is one. -/
def inArc? (p t : String) : Option ArcDecl :=
  N.inArcs.find? fun a => a.place == p && a.transition == t

/-- The arc `(t, p)`, if there is one. -/
def outArc? (t p : String) : Option ArcDecl :=
  N.outArcs.find? fun a => a.place == p && a.transition == t

/-- `pre(t)`, as the arcs into `t` rather than as the places -- which is the same data, and
carries `E(p, t)` with it. -/
def pre (t : String) : List ArcDecl := N.inArcs.filter fun a => a.transition == t

/-- `post(t)`, as the arcs out of `t`. -/
def post (t : String) : List ArcDecl := N.outArcs.filter fun a => a.transition == t

/-- `Var(t)`, the variables appearing in the guard of `t` and in the arc expressions of the
arcs connected to `t`.

Derived, never stored. Duplicates are removed so that the emitted `sum` binds each variable
once. -/
def Var (t : TransDecl) : Ctx :=
  ListUtil.dedup <|
    t.guard.freeVars ++
      (N.pre t.name).flatMap (fun a => a.expr.freeVars) ++
      (N.post t.name).flatMap (fun a => a.expr.freeVars)

theorem mem_Var_of_guard {t : TransDecl} {p : String × ExprTy} (h : p ∈ t.guard.freeVars) :
    p ∈ N.Var t :=
  ListUtil.mem_dedup.2 (List.mem_append_left _ (List.mem_append_left _ h))

theorem mem_Var_of_pre {t : TransDecl} {a : ArcDecl} (ha : a ∈ N.pre t.name)
    {p : String × ExprTy} (h : p ∈ a.expr.freeVars) : p ∈ N.Var t :=
  ListUtil.mem_dedup.2 <| List.mem_append_left _ <| List.mem_append_right _ <|
    List.mem_flatMap.2 ⟨a, ha, h⟩

theorem mem_Var_of_post {t : TransDecl} {a : ArcDecl} (ha : a ∈ N.post t.name)
    {p : String × ExprTy} (h : p ∈ a.expr.freeVars) : p ∈ N.Var t :=
  ListUtil.mem_dedup.2 <| List.mem_append_right _ <| List.mem_flatMap.2 ⟨a, ha, h⟩

/-- The nullary constructors the emitted specification declares.

`Cpn2mCrl2/Print.lean` prints an enumeration as `struct id1 | id2 | ...` and a record with no
fields as `struct R`, so both contribute *constants* to one mCRL2 namespace. Two constants of
the same name are rejected by `mcrl22lps` -- "Double declaration of constructor constant" --
even when they belong to different sorts. A record with fields contributes a constructor of
positive arity, which may share a name with a constant, so it does not appear here. -/
def nullaryCtors (N : Net) : List String :=
  N.colors.flatMap fun c =>
    match c with
    | .enum _ ids => ids
    | .record n .nil => [n]
    | _ => []

/-! ### Validity

The T1 checks of `Implementation/docs/InputFormat.md` §4.3, plus what
`Cpn2mCrl2/Print.lean` needs to emit legal mCRL2. Every field is decidable, so the importer
can establish the whole thing at the boundary and hand it to the core as a hypothesis. -/

/-- The T1 validation of `Implementation/docs/InputFormat.md` §4.3.

Field by field against that list: `placesNodup`, `transNodup` and `namesDisjoint` are check 1
together with `P ∩ T = ∅` of Definition 4; `colorMem` and `boolMem` are check 2 and
Definition 5's `Bool ∈ Σ`; `varTypeMem` is check 3; checks 4 and 5 are partly structural --
`TransDecl.guard` is a boolean expression and `ArcDecl.expr` a bag expression by
construction -- with the remainder of check 5 in `inArcPlace` and `outArcPlace`; `initClosed`
is check 6; and `guardScoped`, `inArcScoped` and `outArcScoped` are check 7. -/
structure Valid : Prop where
  /-- The places have distinct names: `P` is a set. -/
  placesNodup : ListUtil.NoDup N.placeNames
  /-- The transitions have distinct names: `T` is a set. -/
  transNodup : ListUtil.NoDup N.transNames
  /-- The variables have distinct names: `V` is a set. -/
  varsNodup : ListUtil.NoDup N.varNames
  /-- No name is used twice across `P`, `T` and `V`. The `P ∩ T = ∅` of Definition 4, extended
  to `V` because the emitted specification binds a place and a variable in one scope. -/
  namesDisjoint : ∀ n ∈ N.placeNames, n ∉ N.transNames ∧ n ∉ N.varNames
  /-- No transition shares a name with a variable. -/
  transVarsDisjoint : ∀ n ∈ N.transNames, n ∉ N.varNames
  /-- `Bool ∈ Σ`, as Definition 5 requires. -/
  boolMem : Color.bool ∈ N.colors
  /-- `C(p) ∈ Σ` for every place. -/
  colorMem : ∀ d ∈ N.places, d.color ∈ N.colors
  /-- Every variable of `V` is typed by a color, not by a bag. Definition 5's `Type[v] ∈ Σ`
  presupposes it; `Cpn2mCrl2/Expr.lean` allows bag-sorted variables only so that Definition
  14 can build the place parameters. -/
  varsAreColors : ∀ q ∈ N.vars, q.2.isColor = true
  /-- `Type[v] ∈ Σ` for every variable of `V`. -/
  varTypeMem : ∀ q ∈ N.vars, q.2.color! ∈ N.colors
  /-- Every in-arc names a place of the net, at that place's color. -/
  inArcPlace : ∀ a ∈ N.inArcs, N.placeColor? a.place = some a.color
  /-- Every out-arc names a place of the net, at that place's color. -/
  outArcPlace : ∀ a ∈ N.outArcs, N.placeColor? a.place = some a.color
  /-- Every in-arc names a transition of the net. -/
  inArcTrans : ∀ a ∈ N.inArcs, a.transition ∈ N.transNames
  /-- Every out-arc names a transition of the net. -/
  outArcTrans : ∀ a ∈ N.outArcs, a.transition ∈ N.transNames
  /-- `A` is a set: at most one arc from a given place to a given transition. -/
  inArcsNodup : ListUtil.NoDup (N.inArcs.map fun a : ArcDecl => (a.place, a.transition))
  /-- `A` is a set: at most one arc from a given transition to a given place. -/
  outArcsNodup : ListUtil.NoDup (N.outArcs.map fun a : ArcDecl => (a.place, a.transition))
  /-- `I(p)` is closed, so that `M₀` is well-defined without a binding. -/
  initClosed : ∀ d ∈ N.places, d.init.freeVars = []
  /-- `Var(t) ⊆ V` for the guard. -/
  guardScoped : ∀ t ∈ N.transitions, Expr.ScopedIn N.vars t.guard
  /-- `Var(t) ⊆ V` for the in-arc expressions. -/
  inArcScoped : ∀ a ∈ N.inArcs, Expr.ScopedIn N.vars a.expr
  /-- `Var(t) ⊆ V` for the out-arc expressions. -/
  outArcScoped : ∀ a ∈ N.outArcs, Expr.ScopedIn N.vars a.expr
  /-- The nullary constructors of `Σ` are distinct.

  Not one of the seven checks of `InputFormat.md` §4.3, and not a requirement of Definition 5:
  colour sets are sets, and two of them may perfectly well both contain an element spelled `a`.
  It is a constraint the *target* imposes, in the same way as `Target.md` §1's reserved
  keywords, and without it the emitted text is refused by `mcrl22lps`. See
  `Tests/docs/Findings.md` §8. -/
  ctorsNodup : ListUtil.NoDup N.nullaryCtors

instance : DecidablePred Net.Valid := fun N =>
  decidable_of_iff
    (ListUtil.NoDup N.placeNames ∧ ListUtil.NoDup N.transNames ∧ ListUtil.NoDup N.varNames ∧
      (∀ n ∈ N.placeNames, n ∉ N.transNames ∧ n ∉ N.varNames) ∧
      (∀ n ∈ N.transNames, n ∉ N.varNames) ∧
      Color.bool ∈ N.colors ∧ (∀ d ∈ N.places, d.color ∈ N.colors) ∧
      (∀ q ∈ N.vars, q.2.isColor = true) ∧ (∀ q ∈ N.vars, q.2.color! ∈ N.colors) ∧
      (∀ a ∈ N.inArcs, N.placeColor? a.place = some a.color) ∧
      (∀ a ∈ N.outArcs, N.placeColor? a.place = some a.color) ∧
      (∀ a ∈ N.inArcs, a.transition ∈ N.transNames) ∧
      (∀ a ∈ N.outArcs, a.transition ∈ N.transNames) ∧
      ListUtil.NoDup (N.inArcs.map fun a : ArcDecl => (a.place, a.transition)) ∧
      ListUtil.NoDup (N.outArcs.map fun a : ArcDecl => (a.place, a.transition)) ∧
      (∀ d ∈ N.places, d.init.freeVars = []) ∧
      (∀ t ∈ N.transitions, Expr.ScopedIn N.vars t.guard) ∧
      (∀ a ∈ N.inArcs, Expr.ScopedIn N.vars a.expr) ∧
      (∀ a ∈ N.outArcs, Expr.ScopedIn N.vars a.expr) ∧
      ListUtil.NoDup N.nullaryCtors)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
      fun h => ⟨h.placesNodup, h.transNodup, h.varsNodup, h.namesDisjoint, h.transVarsDisjoint,
        h.boolMem, h.colorMem, h.varsAreColors, h.varTypeMem, h.inArcPlace, h.outArcPlace,
        h.inArcTrans, h.outArcTrans, h.inArcsNodup, h.outArcsNodup, h.initClosed,
        h.guardScoped, h.inArcScoped, h.outArcScoped, h.ctorsNodup⟩⟩

/-! ### Consequences of validity used by the translation -/

variable {N}

/-- Under validity the arc expression of an in-arc can be read at the color of its place
without changing what it evaluates to. -/
theorem eval_inArc_exprAt (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.inArcs) {c : Color}
    (hc : N.placeColor? a.place = some c) (env : Env) :
    Expr.eval (a.exprAt c) env = Expr.eval a.expr env :=
  ArcDecl.eval_exprAt (Option.some.inj ((h.inArcPlace a ha).symm.trans hc)) env

/-- The same for an out-arc. -/
theorem eval_outArc_exprAt (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.outArcs) {c : Color}
    (hc : N.placeColor? a.place = some c) (env : Env) :
    Expr.eval (a.exprAt c) env = Expr.eval a.expr env :=
  ArcDecl.eval_exprAt (Option.some.inj ((h.outArcPlace a ha).symm.trans hc)) env

theorem mem_inArcs_of_mem_pre {t : String} {a : ArcDecl} (h : a ∈ N.pre t) : a ∈ N.inArcs :=
  (List.mem_filter.1 h).1

theorem mem_outArcs_of_mem_post {t : String} {a : ArcDecl} (h : a ∈ N.post t) :
    a ∈ N.outArcs :=
  (List.mem_filter.1 h).1

end Net

end Cpn2mCrl2
