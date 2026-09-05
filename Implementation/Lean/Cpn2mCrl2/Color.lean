/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/

/-!
# Colors and values

The color universe `Σ` of Definition 5, fixed concretely, and the values that inhabit it.

`Implementation/docs/InputFormat.md` §4.1 fixes the grammar:

```
color ::= Bool | Int | enum(name, [id, ...]) | record(name, [(field, color), ...])
```

That is the whole of `Σ`. A CPN file declares a finite list of colors; the importer resolves
every color *name* a declaration mentions into the tree below, so that nothing inside the
trust boundary has to chase a name through an environment.

## Implementation notes

**Fields are a dedicated list type.** `record` would naturally carry a
`List (String × Color)`, but that is a *nested* inductive and Lean derives neither
`DecidableEq` nor a usable structural recursor for it. `ColorFields` and `ValueFields` are the
same data as an ordinary mutual inductive, which derives both. Every function over colors is
therefore a `mutual def` over the pair.

**Values are untyped, with typing as a separate predicate.** The alternative -- a family
`Color → Type` of intrinsically typed values -- makes `DecidableEq` (which bags need, per
`Implementation/docs/Plan.md` §4.1) a recursion over colors and buys nothing here: the
translator never evaluates, so values appear only in the *statement* of the T2 theorems.
`Value.ofColor` is the typing judgement, and `Cpn2mCrl2/Expr.lean` proves the expression
evaluator preserves it.

**Record values carry their field names.** Redundant, given that a well-typed record value is
always in the declared field order, but it keeps `DecidableEq` structural and projection
independent of the color.
-/

namespace Cpn2mCrl2

/-! ## Colors -/

mutual

/-- A color: `Bool`, `Int`, a finite enumeration, or a record. This is `Σ` of Definition 5,
with the grammar of `Implementation/docs/InputFormat.md` §4.1. -/
inductive Color where
  /-- The booleans. Definition 5 requires `Bool ∈ Σ`; here it is a constructor, so the
  requirement holds by construction. -/
  | bool
  /-- The integers. -/
  | int
  /-- A finite enumeration `name`, with the listed constructors. -/
  | enum (name : String) (ids : List String)
  /-- A record `name` with the listed fields. -/
  | record (name : String) (fields : ColorFields)
  deriving Repr

/-- The fields of a record color, as an association list of field name to color. -/
inductive ColorFields where
  /-- No fields. -/
  | nil
  /-- One field, followed by the rest. -/
  | cons (name : String) (c : Color) (rest : ColorFields)
  deriving Repr

end

deriving instance DecidableEq for Color, ColorFields

namespace ColorFields

/-- The color of the field `f`, if there is one. -/
def lookup : ColorFields → String → Option Color
  | .nil, _ => none
  | .cons n c rest, f => if n = f then some c else rest.lookup f

/-- The field names, in declaration order. -/
def names : ColorFields → List String
  | .nil => []
  | .cons n _ rest => n :: rest.names

/-- The fields as an ordinary list. -/
def toList : ColorFields → List (String × Color)
  | .nil => []
  | .cons n c rest => (n, c) :: rest.toList

/-- The fields of an ordinary list. -/
def ofList : List (String × Color) → ColorFields
  | [] => .nil
  | (n, c) :: rest => .cons n c (ofList rest)

@[simp] theorem toList_ofList (l : List (String × Color)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih => cases hd; simp [ofList, toList, ih]

end ColorFields

/-! ## Values -/

mutual

/-- A value of some color. Untyped; `Value.ofColor` is the typing judgement. -/
inductive Value where
  /-- A boolean. -/
  | bool (b : Bool)
  /-- An integer. -/
  | int (i : Int)
  /-- A constructor of an enumeration. -/
  | ctor (id : String)
  /-- A record value, one entry per field of its color, in declaration order. -/
  | record (fields : ValueFields)
  deriving Repr

/-- The fields of a record value. -/
inductive ValueFields where
  /-- No fields. -/
  | nil
  /-- One field, followed by the rest. -/
  | cons (name : String) (v : Value) (rest : ValueFields)
  deriving Repr

end

deriving instance DecidableEq for Value, ValueFields

instance : Inhabited Value := ⟨.bool false⟩

namespace ValueFields

/-- The value of the field `f`, if there is one. -/
def lookup : ValueFields → String → Option Value
  | .nil, _ => none
  | .cons n v rest, f => if n = f then some v else rest.lookup f

end ValueFields

mutual

/-- The typing judgement `v : c`, as a decision procedure.

A record value has to list exactly the fields of its color, in order, with each value of the
declared color. -/
def Value.ofColor : Value → Color → Bool
  | .bool _, .bool => true
  | .int _, .int => true
  | .ctor id, .enum _ ids => decide (id ∈ ids)
  | .record vs, .record _ fs => ValueFields.ofColorFields vs fs
  | _, _ => false

/-- `Value.ofColor`, lifted to the fields of a record. -/
def ValueFields.ofColorFields : ValueFields → ColorFields → Bool
  | .nil, .nil => true
  | .cons n v vs, .cons n' c fs => n == n' && Value.ofColor v c && ValueFields.ofColorFields vs fs
  | _, _ => false

end

/-- Looking a field up in a well-typed record value finds it, at the color the record's own
type gives it.

This is what `Cpn2mCrl2/Typing.lean` needs to show that `Expr.proj` never reaches
`Color.junk`. -/
theorem ValueFields.lookup_ofColorFields :
    ∀ {vs : ValueFields} {fs : ColorFields}, ValueFields.ofColorFields vs fs = true →
      ∀ {f : String} {c : Color}, fs.lookup f = some c →
        ∃ v, vs.lookup f = some v ∧ v.ofColor c = true
  | .nil, .nil, _, _, _, hf => absurd hf (by simp [ColorFields.lookup])
  | .nil, .cons _ _ _, hwf, _, _, _ => absurd hwf (by simp [ValueFields.ofColorFields])
  | .cons _ _ _, .nil, hwf, _, _, _ => absurd hwf (by simp [ValueFields.ofColorFields])
  | .cons n v vs, .cons n' c' fs', hwf, f, c, hf => by
    simp only [ValueFields.ofColorFields, Bool.and_eq_true, beq_iff_eq] at hwf
    obtain ⟨⟨hn, hv⟩, hrest⟩ := hwf
    subst hn
    by_cases hnf : n = f
    · rw [ColorFields.lookup, ite_eq_left_of_eq_true _ _ (by simp [hnf])] at hf
      refine ⟨v, by rw [ValueFields.lookup, ite_eq_left_of_eq_true _ _ (by simp [hnf])], ?_⟩
      rw [← Option.some.inj hf]; exact hv
    · rw [ColorFields.lookup, ite_eq_right_of_eq_false _ _ (by simp [hnf])] at hf
      obtain ⟨w, hw, hwc⟩ := ValueFields.lookup_ofColorFields hrest hf
      exact ⟨w, by rw [ValueFields.lookup, ite_eq_right_of_eq_false _ _ (by simp [hnf])]; exact hw, hwc⟩

/-- A well-typed value of a record color is a record value whose fields are well-typed. -/
theorem Value.eq_record_of_ofColor {v : Value} {n : String} {fs : ColorFields}
    (h : v.ofColor (.record n fs) = true) :
    ∃ vs, v = .record vs ∧ ValueFields.ofColorFields vs fs = true := by
  cases v with
  | record vs => exact ⟨vs, rfl, h⟩
  | bool _ => exact absurd h (by simp [Value.ofColor])
  | int _ => exact absurd h (by simp [Value.ofColor])
  | ctor _ => exact absurd h (by simp [Value.ofColor])

/-- A value of the color `c`, used as the result of an evaluation that typing rules out.

`Expr.eval` is total, so the projection of a field that a value does not carry has to return
something; `Expr.eval_wf` of `Cpn2mCrl2/Typing.lean` proves the case never arises for a
well-typed environment. -/
def Color.junk : Color → Value
  | .bool => .bool false
  | .int => .int 0
  | .enum _ ids => .ctor (ids.headD "")
  | .record _ _ => .record .nil

end Cpn2mCrl2
