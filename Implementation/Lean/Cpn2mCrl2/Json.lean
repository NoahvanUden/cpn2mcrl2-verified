/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Print
import Lean.Data.Json

/-!
# The importer

Reading the native CPN format of `Implementation/docs/InputFormat.md` §4, and the T1
validation that turns it into a `Net`.

This file is **outside the trust boundary**. `Implementation/docs/Plan.md` §3 draws the line:

> The standard verified-compiler shape: a small verified core with unverified adapters outside the trust boundary.

Nothing here is proved about. What it produces is a `Net` together with a *proof* of
`Net.Valid`, obtained by deciding it -- and from that point on the core has the T1 hypotheses
of `Implementation/docs/InputFormat.md` §4.3 available, which is the whole purpose of doing
the validation at the boundary.

Two things it does beyond `Net.Valid`.

**Type checking.** The JSON carries an untyped tree; `Expr` is indexed by `ExprTy`. Turning
one into the other *is* checks 4 to 6 of `Implementation/docs/InputFormat.md` §4.3, and once
it succeeds those checks hold by construction and never have to be stated again. Checking is
bidirectional: a guard is checked against `Bool` and an arc expression against `Bag(C(p))`,
which is what lets `["emptyBag"]` and `["ctor", id]` be written without an annotation.

**Identifier legality.** `Implementation/docs/Target.md` §1 records that `val` is a reserved
mCRL2 keyword and that a generator has to deal with it. This one refuses the net, naming the
offending identifier, rather than renaming it: the user wrote that name, and silently emitting
a different one is worse than an error.

## The grammar it accepts

Exactly `Implementation/docs/InputFormat.md` §4.1, as JSON arrays whose head is the operator:

```
["var", x] | ["int", n] | ["bool", b] | ["ctor", id]
["rec", C, [[field, e], ...]] | ["proj", e, field]
["+", a, b] | ["-", a, b] | ["*", a, b]
["=", a, b] | ["<=", a, b] | ["<", a, b]
["&&", a, b] | ["||", a, b] | ["!", a]
["bag", [[n, e], ...]] | ["emptyBag"] | ["union", a, b] | ["diff", a, b]
```

`bagSubset` is deliberately absent: it is the one operation Definition 14 assembles and a CPN
never contains, and `Cpn2mCrl2/Expr.lean` says so where it is declared.
-/

namespace Cpn2mCrl2

namespace Import

open Lean (Json)

/-- The importer's error monad. -/
abbrev M := Except String

private def idx (a : Array Json) (i : Nat) (what : String) : M Json :=
  match a[i]? with
  | some j => .ok j
  | none => .error s!"{what}: missing element {i}"

private def entries (j : Json) : M (List (String × Json)) := do
  let m ← j.getObj?
  return m.toList

private def checkIdent (kind : String) (s : String) : M String :=
  if Mcrl2.isSafeIdent s then .ok s
  else .error s!"{kind} {s} is not usable as an mCRL2 identifier: it is a reserved keyword, or \
    not a letter or underscore followed by letters, digits, underscores and primes"

/-! ### Colors -/

/-- Resolve a color *name* into the color tree `Cpn2mCrl2/Color.lean` holds.

A record field names another color, so resolution recurses; `fuel` bounds the recursion by the
number of declarations, which turns a cyclic definition into an error instead of a loop. -/
partial def resolveColor (decls : List (String × Json)) (fuel : Nat) (name : String) :
    M Color := do
  if fuel = 0 then
    .error s!"color {name} is defined cyclically, or nested deeper than there are colors"
  let some j := decls.lookup name
    | .error s!"undeclared color {name}"
  let kind ← (← j.getObjVal? "kind").getStr?
  match kind with
  | "bool" => return .bool
  | "int" => return .int
  | "enum" =>
    let _ ← checkIdent "color" name
    let arr ← (← j.getObjVal? "ids").getArr?
    let ids ← arr.toList.mapM fun i => do checkIdent "constructor" (← i.getStr?)
    if ids.isEmpty then
      .error s!"enumeration {name} has no constructors, so it has no values"
    return .enum name ids
  | "record" =>
    let _ ← checkIdent "color" name
    let arr ← (← j.getObjVal? "fields").getArr?
    let fs ← arr.toList.mapM fun f => do
      let p ← f.getArr?
      let fname ← checkIdent "field" (← (← idx p 0 "record field").getStr?)
      let cname ← (← idx p 1 "record field").getStr?
      return (fname, ← resolveColor decls (fuel - 1) cname)
    return .record name (ColorFields.ofList fs)
  | k => .error s!"color {name} has unknown kind {k}"

/-! ### Expressions -/

mutual

/-- Bidirectional type checking.

The four functions below are one recursion. `checkExpr` dispatches on the *expected sort*,
which is what lets `["emptyBag"]`, `["ctor", id]` and `["rec", ...]` be written without an
annotation: their color comes from the place or the guard they annotate. Anything the expected
sort does not settle falls through `coerceTo` to `inferExpr`.

Dispatching on the sort is also where the intrinsic typing of `Cpn2mCrl2/Expr.lean` pays for
itself: once a branch returns, the expression *is* of the sort the place or guard requires,
and checks 4 to 6 of `Implementation/docs/InputFormat.md` §4.3 never have to be stated
again. -/
partial def checkExpr (vars : Ctx) (colors : List Color) (j : Json) :
    (τ : ExprTy) → M (Expr τ)
  | .bag c => do
    let a ← j.getArr?
    let hd ← (← idx a 0 "expression").getStr?
    match hd with
    | "emptyBag" => return .emptyBag c
    | "bag" =>
      let items ← (← idx a 1 "bag literal").getArr?
      let terms ← items.toList.mapM fun it => do
        let p ← it.getArr?
        let n ← (← idx p 0 "bag item").getNat?
        return Expr.single n (← checkExpr vars colors (← idx p 1 "bag item") (.color c))
      return Expr.unionAll terms
    | "union" =>
      return .bagUnion (← checkExpr vars colors (← idx a 1 "union") (.bag c))
        (← checkExpr vars colors (← idx a 2 "union") (.bag c))
    | "diff" =>
      return .bagDiff (← checkExpr vars colors (← idx a 1 "diff") (.bag c))
        (← checkExpr vars colors (← idx a 2 "diff") (.bag c))
    | _ => coerceTo vars colors j (.bag c)
  | .color (.enum n ids) => do
    let a ← j.getArr?
    let hd ← (← idx a 0 "expression").getStr?
    if hd == "ctor" then
      let id ← (← idx a 1 "constructor").getStr?
      if h : id ∈ ids then return .ctorLit n ids id h
      else .error s!"{id} is not a constructor of the enumeration {n}"
    else coerceTo vars colors j (.color (.enum n ids))
  | .color (.record n fs) => do
    let a ← j.getArr?
    let hd ← (← idx a 0 "expression").getStr?
    if hd == "rec" then
      let arr ← (← idx a 2 "record literal").getArr?
      let given ← arr.toList.mapM fun f => do
        let p ← f.getArr?
        return ((← (← idx p 0 "record field").getStr?), ← idx p 1 "record field")
      for (fname, _) in given do
        if (fs.lookup fname).isNone then
          .error s!"record literal for {n} gives a field {fname} that the color does not have"
      return .mkRec n (← checkArgs vars colors n given fs)
    else coerceTo vars colors j (.color (.record n fs))
  | .color .bool => coerceTo vars colors j (.color .bool)
  | .color .int => coerceTo vars colors j (.color .int)
  | .list _ => .error "the input format has no list sort; lists belong to the second backend"

/-- Infer the sort of an expression and require it to be the expected one. -/
partial def coerceTo (vars : Ctx) (colors : List Color) (j : Json) (τ : ExprTy) :
    M (Expr τ) := do
  let s ← inferExpr vars colors j
  if h : s.1 = τ then return h ▸ s.2
  else .error s!"expression has sort {Mcrl2.sortRef s.1} where {Mcrl2.sortRef τ} is expected"

/-- One expression per field of a record color, taken from the literal by name so that the
file need not list the fields in declaration order. -/
partial def checkArgs (vars : Ctx) (colors : List Color) (n : String)
    (given : List (String × Json)) : (fs : ColorFields) → M (Args fs)
  | .nil => return .nil
  | .cons f c rest => do
    let some j := given.lookup f
      | .error s!"record literal for {n} is missing the field {f}"
    return .cons (← checkExpr vars colors j (.color c)) (← checkArgs vars colors n given rest)

/-- Bidirectional type checking, inferring half. -/
partial def inferExpr (vars : Ctx) (colors : List Color) (j : Json) :
    M ((τ : ExprTy) × Expr τ) := do
  let a ← j.getArr?
  let hd ← (← idx a 0 "expression").getStr?
  let int2 (mk : Expr (.color .int) → Expr (.color .int) → Expr (.color .int)) :
      M ((τ : ExprTy) × Expr τ) := do
    let x ← checkExpr vars colors (← idx a 1 hd) (.color .int)
    let y ← checkExpr vars colors (← idx a 2 hd) (.color .int)
    return ⟨.color .int, mk x y⟩
  let cmp2 (mk : Expr (.color .int) → Expr (.color .int) → Expr (.color .bool)) :
      M ((τ : ExprTy) × Expr τ) := do
    let x ← checkExpr vars colors (← idx a 1 hd) (.color .int)
    let y ← checkExpr vars colors (← idx a 2 hd) (.color .int)
    return ⟨.color .bool, mk x y⟩
  let bool2 (mk : Expr (.color .bool) → Expr (.color .bool) → Expr (.color .bool)) :
      M ((τ : ExprTy) × Expr τ) := do
    let x ← checkExpr vars colors (← idx a 1 hd) (.color .bool)
    let y ← checkExpr vars colors (← idx a 2 hd) (.color .bool)
    return ⟨.color .bool, mk x y⟩
  match hd with
  | "var" =>
    let x ← (← idx a 1 "variable").getStr?
    let some τ := List.lookup x vars
      | .error s!"{x} is not a variable of the net"
    return ⟨τ, .var x τ⟩
  | "int" => return ⟨.color .int, .intLit (← (← idx a 1 "integer literal").getInt?)⟩
  | "bool" => return ⟨.color .bool, .boolLit (← (← idx a 1 "boolean literal").getBool?)⟩
  | "+" => int2 .add
  | "-" => int2 .sub
  | "*" => int2 .mul
  | "<=" => cmp2 .le
  | "<" => cmp2 .lt
  | "&&" => bool2 .and
  | "||" => bool2 .or
  | "!" => return ⟨.color .bool, .not (← checkExpr vars colors (← idx a 1 "not") (.color .bool))⟩
  | "=" =>
    let rhs ← idx a 2 "equality"
    match (← inferExpr vars colors (← idx a 1 "equality")) with
    | ⟨.color c, x⟩ =>
      return ⟨.color .bool, .eq x (← checkExpr vars colors rhs (.color c))⟩
    | _ => .error "equality compares values, not bags or lists"
  | "proj" =>
    let f ← (← idx a 2 "projection").getStr?
    match (← inferExpr vars colors (← idx a 1 "projection")) with
    | ⟨.color (.record n fs), e⟩ =>
      match hf : fs.lookup f with
      | some c => return ⟨.color c, .proj e f c hf⟩
      | none => .error s!"the record {n} has no field {f}"
    | _ => .error s!"{f} is projected out of something that is not a record"
  | "rec" =>
    let n ← (← idx a 1 "record literal").getStr?
    let some c := colors.find? fun c => Mcrl2.sortName c == n
      | .error s!"undeclared color {n}"
    match c with
    | .record n' fs =>
      return ⟨.color (.record n' fs), ← checkExpr vars colors j (.color (.record n' fs))⟩
    | _ => .error s!"{n} is not a record color"
  | "ctor" =>
    let id ← (← idx a 1 "constructor").getStr?
    match colors.filter fun c => match c with | .enum _ ids => ids.contains id | _ => false with
    | [.enum n ids] =>
      if h : id ∈ ids then return ⟨.color (.enum n ids), .ctorLit n ids id h⟩
      else .error s!"{id} is not a constructor of {n}"
    | [] => .error s!"{id} is not a constructor of any declared enumeration"
    | _ => .error s!"{id} is a constructor of more than one enumeration, so its color cannot \
        be inferred here"
  | "bag" =>
    let items ← (← idx a 1 "bag literal").getArr?
    let some first := items[0]?
      | .error "an empty bag literal needs a known color; write it where the sort is expected"
    let p ← first.getArr?
    let s ← inferExpr vars colors (← idx p 1 "bag item")
    match s.1 with
    | .color c => return ⟨.bag c, ← checkExpr vars colors j (.bag c)⟩
    | _ => .error "a bag cannot hold bags or lists"
  | "union" | "diff" =>
    let s ← inferExpr vars colors (← idx a 1 hd)
    match s.1 with
    | .bag c => return ⟨.bag c, ← checkExpr vars colors j (.bag c)⟩
    | _ => .error s!"{hd} takes bags"
  | "emptyBag" =>
    .error "the empty bag needs a known color; write it where the sort is expected"
  | k => .error s!"unknown expression form {k}"

end

/-! ### The net -/

/-- Read a `Net` from the JSON of `Implementation/docs/InputFormat.md` §4.2.

Nothing here checks `Net.Valid`; `Net.ofJsonString` does that afterwards, so that a failure
can name the condition that failed. -/
def netOfJson (j : Json) : M Net := do
  let colorDecls ← entries (← j.getObjVal? "colors")
  let fuel := colorDecls.length + 1
  let colors ← colorDecls.mapM fun d => resolveColor colorDecls fuel d.1
  let colorNamed : String → M Color := fun n =>
    match colors.find? fun c => Mcrl2.sortName c == n with
    | some c => .ok c
    | none => .error s!"undeclared color {n}"
  let vars ← (← entries (← j.getObjVal? "variables")).mapM fun v => do
    let _ ← checkIdent "variable" v.1
    return (v.1, ExprTy.color (← colorNamed (← v.2.getStr?)))
  let places ← (← entries (← j.getObjVal? "places")).mapM fun p => do
    let _ ← checkIdent "place" p.1
    let c ← colorNamed (← (← p.2.getObjVal? "color").getStr?)
    let init ← checkExpr [] colors (← p.2.getObjVal? "init") (.bag c)
    return ({ name := p.1, color := c, init := init } : PlaceDecl)
  let transitions ← (← entries (← j.getObjVal? "transitions")).mapM fun t => do
    let _ ← checkIdent "transition" t.1
    let g ← checkExpr vars colors (← t.2.getObjVal? "guard") (.color .bool)
    return ({ name := t.1, guard := g } : TransDecl)
  let arc : Json → M ArcDecl := fun aj => do
    let p ← (← aj.getObjVal? "place").getStr?
    let t ← (← aj.getObjVal? "transition").getStr?
    let some d := places.find? fun d => d.name == p
      | .error s!"an arc names a place {p} that the net does not have"
    let e ← checkExpr vars colors (← aj.getObjVal? "expr") (.bag d.color)
    return { place := p, transition := t, color := d.color, expr := e }
  let inArcs ← (← (← j.getObjVal? "inArcs").getArr?).toList.mapM arc
  let outArcs ← (← (← j.getObjVal? "outArcs").getArr?).toList.mapM arc
  return { colors := if colors.contains .bool then colors else colors ++ [.bool]
           vars := vars, places := places, transitions := transitions
           inArcs := inArcs, outArcs := outArcs }

end Import

/-- The T1 checks that fail, by name, so that a rejection can say what is wrong rather than
only that something is.

This mirrors `Net.Valid` field for field. It is a convenience for the error message and
nothing depends on it: `Net.ofJsonString` decides `Net.Valid` itself, and that decision is
what the core receives. -/
def Net.explainInvalid (N : Net) : List String :=
  let no := fun (b : Bool) (m : String) => if b then [] else [m]
  no (decide (ListUtil.NoDup N.nullaryCtors))
      "two colors declare a constructor of the same name, which mCRL2 refuses"
  ++ no (decide (ListUtil.NoDup N.placeNames)) "two places share a name"
  ++ no (decide (ListUtil.NoDup N.transNames)) "two transitions share a name"
  ++ no (decide (ListUtil.NoDup N.varNames)) "two variables share a name"
  ++ no (decide (∀ n ∈ N.placeNames, n ∉ N.transNames ∧ n ∉ N.varNames))
      "a place shares its name with a transition or a variable"
  ++ no (decide (∀ n ∈ N.transNames, n ∉ N.varNames))
      "a transition shares its name with a variable"
  ++ no (decide (Color.bool ∈ N.colors)) "Bool is not among the colors"
  ++ no (decide (∀ d ∈ N.places, d.color ∈ N.colors)) "a place has an undeclared color"
  ++ no (decide (∀ q ∈ N.vars, q.2.isColor = true)) "a variable is not typed by a color"
  ++ no (decide (∀ q ∈ N.vars, q.2.color! ∈ N.colors)) "a variable has an undeclared color"
  ++ no (decide (∀ a ∈ N.inArcs, N.placeColor? a.place = some a.color))
      "an in-arc expression is not of the color of its place"
  ++ no (decide (∀ a ∈ N.outArcs, N.placeColor? a.place = some a.color))
      "an out-arc expression is not of the color of its place"
  ++ no (decide (∀ a ∈ N.inArcs, a.transition ∈ N.transNames))
      "an in-arc names a transition the net does not have"
  ++ no (decide (∀ a ∈ N.outArcs, a.transition ∈ N.transNames))
      "an out-arc names a transition the net does not have"
  ++ no (decide (ListUtil.NoDup (N.inArcs.map fun a : ArcDecl => (a.place, a.transition))))
      "two in-arcs connect the same place and transition"
  ++ no (decide (ListUtil.NoDup (N.outArcs.map fun a : ArcDecl => (a.place, a.transition))))
      "two out-arcs connect the same transition and place"
  ++ no (decide (∀ d ∈ N.places, d.init.freeVars = []))
      "an initialization expression is not closed"
  ++ no (decide (∀ t ∈ N.transitions, Expr.ScopedIn N.vars t.guard))
      "a guard mentions a variable outside V"
  ++ no (decide (∀ a ∈ N.inArcs, Expr.ScopedIn N.vars a.expr))
      "an in-arc expression mentions a variable outside V"
  ++ no (decide (∀ a ∈ N.outArcs, Expr.ScopedIn N.vars a.expr))
      "an out-arc expression mentions a variable outside V"

/-- Read a CPN from the text of a native CPN file, validated.

The `Net.Valid` in the result is what the core runs on: from here inwards the T1 checks of
`Implementation/docs/InputFormat.md` §4.3 are hypotheses, not assumptions. -/
def Net.ofJsonString (s : String) : Except String ((N : Net) × PLift N.Valid) := do
  let j ← Lean.Json.parse s
  let N ← Import.netOfJson j
  if h : N.Valid then return ⟨N, PLift.up h⟩
  else
    .error ("the input is not a CPN:\n  - "
      ++ String.intercalate "\n  - " N.explainInvalid)

end Cpn2mCrl2
