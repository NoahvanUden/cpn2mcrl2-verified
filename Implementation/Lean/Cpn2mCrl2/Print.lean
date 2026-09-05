/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Translate

/-!
# Printing mCRL2

The last link of the chain, and the only part of the verified core that nothing is proved
about. `Implementation/docs/Plan.md` §3 puts it this way:

> The printer is the only unverifiable part of the core, and it is the smallest. Keeping the LPE term intrinsically typed means the printer is a total function on a well-typed AST, with no failure modes of its own beyond string formatting.

That is what this file is. `Expr` is indexed by `ExprTy`, so every term reaching `printExpr`
is well-typed by construction and there is no case to reject; the function is total and
returns a `String`. What it cannot establish is tier T4 -- that `mcrl22lps` reads the text back
as the term that was printed -- which `Implementation/docs/Plan.md` §2 rules out of scope for
want of a formalized mCRL2 grammar, and which `scripts/check.sh` tests instead.

## The encoding

`Implementation/docs/Target.md` §1 fixes it, having checked each operator against the toolset:

| Definition 14 writes | printed as |
| --- | --- |
| `C(p)_MS` | `Bag(C)` |
| the empty bag | `{:}` |
| `{n`e}` | `{e: n}` |
| `m₁ ∪ m₂` | `m1 + m2` |
| `m₁ \ m₂` | `m1 - m2` |
| `m₁ ⊆ m₂` | `m1 <= m2` |

Colors become sorts: `Bool` and `Int` are mCRL2's own, an enumeration is
`struct id1 | id2 | ...`, and a record is `struct R(f1 : S1, ...)` whose field names are
mCRL2's projection functions, so `Expr.proj` prints as `f(e)`. mCRL2 accepts a constructor
with the same name as its sort, which is what keeps the printed names the ones the CPN file
used.

Everything is fully parenthesized. That is uglier than
`Implementation/docs/Target.md` §2 prints by hand, and it is deliberate: precedence is exactly
the sort of thing a printer gets wrong, and T4 is tested rather than proved.

## Identifiers

`Implementation/docs/Target.md` §1 flags one hazard:

> One implementation note that will bite a code generator: **`val` is a reserved keyword**, so record field names taken from a CPN's color definitions must be checked against mCRL2's keyword list and escaped.

`Mcrl2.isSafeIdent` is that check. It is not escaping but rejection, done by the importer at
the boundary: a CPN whose names collide with mCRL2's is refused with a message, rather than
silently renamed into something the user did not write.
-/

namespace Cpn2mCrl2

namespace Mcrl2

/-- The name the emitted process is given. Reserved along with the keywords, so that no place,
transition or variable can shadow it. -/
def procName : String := "Spec"

/-- The keywords of the mCRL2 language, which an identifier taken from a CPN file may not
be. -/
def keywords : List String :=
  ["sort", "cons", "map", "var", "eqn", "act", "proc", "init", "struct", "glob", "pbes",
   "Bool", "Pos", "Nat", "Int", "Real", "List", "Set", "Bag", "FSet", "FBag",
   "true", "false", "whr", "end", "lambda", "forall", "exists", "div", "mod", "in", "if",
   "delta", "tau", "sum", "block", "allow", "hide", "rename", "comm", "val", "yaled", "delay",
   "nu", "mu", "min", "max", "succ", "pred", "abs", "floor", "ceil", "round", "exp",
   "A2B", "head", "tail", "rhead", "rtail", "count", "Nat2Pos", "Pos2Nat", "Int2Nat",
   "Nat2Int", "Int2Real", "Real2Int", "Nat2Real", "Real2Nat", "Pos2Real", "Real2Pos",
   procName]

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Whether a name taken from a CPN file may be printed as an mCRL2 identifier: a letter or
underscore followed by letters, digits, underscores and primes, and not a keyword.

The importer refuses a net that fails this, rather than renaming behind the user's back. -/
def isSafeIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentChar && !keywords.contains s

/-! ### Sorts -/

/-- The mCRL2 sort a color is printed as. -/
def sortName : Color → String
  | .bool => "Bool"
  | .int => "Int"
  | .enum n _ => n
  | .record n _ => n

/-- The mCRL2 sort an expression type is printed as. -/
def sortRef : ExprTy → String
  | .color c => sortName c
  | .bag c => "Bag(" ++ sortName c ++ ")"
  | .list c => "List(" ++ sortName c ++ ")"

/-- The name of the `rm` map for a color. mCRL2 has no polymorphic user-defined maps, so the
three list operations the second backend needs are declared once per color. -/
def rmName (c : Color) : String := "rm_" ++ sortName c

/-- The name of the multiset-difference map for a color. -/
def diffName (c : Color) : String := "diff_" ++ sortName c

/-- The name of the multiset-inclusion map for a color. -/
def subName (c : Color) : String := "sub_" ++ sortName c

mutual

/-- The colors that need a `sort` declaration, including those reached through record
fields. -/
def namedColors : Color → List Color
  | .bool => []
  | .int => []
  | .enum n ids => [.enum n ids]
  | .record n fs => Color.record n fs :: namedColorsFields fs

/-- `namedColors`, over the fields of a record. -/
def namedColorsFields : ColorFields → List Color
  | .nil => []
  | .cons _ c rest => namedColors c ++ namedColorsFields rest

end

/-- The field declarations of a record sort. -/
def fieldDecls : ColorFields → List String
  | .nil => []
  | .cons n c rest => (n ++ " : " ++ sortName c) :: fieldDecls rest

/-- The `sort` declaration of a color, if it needs one. -/
def sortDecl : Color → Option String
  | .bool => none
  | .int => none
  | .enum n ids => some ("sort " ++ n ++ " = struct " ++ String.intercalate " | " ids ++ ";")
  | .record n fs =>
    match fieldDecls fs with
    | [] => some ("sort " ++ n ++ " = struct " ++ n ++ ";")
    | ds => some ("sort " ++ n ++ " = struct " ++ n ++ "(" ++ String.intercalate ", " ds ++ ");")

/-- The `sort` declarations of a list of colors, each emitted once. -/
def sortDecls (cs : List Color) : List String :=
  let named := (cs.flatMap namedColors).foldl
    (fun acc c => if acc.any (fun d => sortName d == sortName c) then acc else acc ++ [c]) []
  named.filterMap sortDecl

/-! ### Terms -/

/-- An integer literal, parenthesized when negative so that `{-1: 1}` cannot be misread. -/
private def intLit (n : Int) : String :=
  if n < 0 then "(" ++ toString n ++ ")" else toString n

mutual

/-- An expression as mCRL2 text.

Total on a well-typed term, which is every term of type `Expr τ`. -/
def printExpr : {τ : ExprTy} → Expr τ → String
  | _, .var x _ => x
  | _, .intLit n => intLit n
  | _, .boolLit b => if b then "true" else "false"
  | _, .ctorLit _ _ id _ => id
  | _, .mkRec n args =>
    match printArgs args with
    | [] => n
    | as => n ++ "(" ++ String.intercalate ", " as ++ ")"
  | _, .proj e f _ _ => f ++ "(" ++ printExpr e ++ ")"
  | _, .add a b => "(" ++ printExpr a ++ " + " ++ printExpr b ++ ")"
  | _, .sub a b => "(" ++ printExpr a ++ " - " ++ printExpr b ++ ")"
  | _, .mul a b => "(" ++ printExpr a ++ " * " ++ printExpr b ++ ")"
  | _, .eq a b => "(" ++ printExpr a ++ " == " ++ printExpr b ++ ")"
  | _, .le a b => "(" ++ printExpr a ++ " <= " ++ printExpr b ++ ")"
  | _, .lt a b => "(" ++ printExpr a ++ " < " ++ printExpr b ++ ")"
  | _, .and a b => "(" ++ printExpr a ++ " && " ++ printExpr b ++ ")"
  | _, .or a b => "(" ++ printExpr a ++ " || " ++ printExpr b ++ ")"
  | _, .not a => "(!" ++ printExpr a ++ ")"
  | _, .emptyBag _ => "{:}"
  | _, .single n e => "{" ++ printExpr e ++ ": " ++ toString n ++ "}"
  | _, .bagUnion a b => "(" ++ printExpr a ++ " + " ++ printExpr b ++ ")"
  | _, .bagDiff a b => "(" ++ printExpr a ++ " - " ++ printExpr b ++ ")"
  | _, .bagSubset a b => "(" ++ printExpr a ++ " <= " ++ printExpr b ++ ")"
  | _, .nilList _ => "[]"
  | _, .snoc l e =>
    match snocItems l with
    | some items => "[" ++ String.intercalate ", " (items ++ [printExpr e]) ++ "]"
    | none => "(" ++ printExpr l ++ " <| " ++ printExpr e ++ ")"
  | _, .appendList a b => "(" ++ printExpr a ++ " ++ " ++ printExpr b ++ ")"
  | _, @Expr.diffList c a b => diffName c ++ "(" ++ printExpr a ++ ", " ++ printExpr b ++ ")"
  | _, @Expr.subList c a b => subName c ++ "(" ++ printExpr a ++ ", " ++ printExpr b ++ ")"

/-- `printExpr`, one record field at a time. -/
def printArgs : {fs : ColorFields} → Args fs → List String
  | _, .nil => []
  | _, .cons e rest => printExpr e :: printArgs rest

/-- The elements of a list term built from `[]` by `<|`, so that it can be printed as mCRL2's
own list literal rather than as a chain of appends. `none` for anything else. -/
def snocItems : {c : Color} → Expr (.list c) → Option (List String)
  | _, .nilList _ => some []
  | _, .snoc l e => (snocItems l).map fun items => items ++ [printExpr e]
  | _, _ => none

end

/-! ### The specification -/

/-- The binder of a summand: `sum v : S, w : T .`, or nothing when `Var(t)` is empty. -/
def printBinder (binder : Ctx) : String :=
  match binder with
  | [] => ""
  | _ => "sum " ++ String.intercalate ", "
      (binder.map fun q => q.1 ++ " : " ++ sortRef q.2) ++ " . "

/-- The recursive call of a summand, with one argument per place in the order the process
declares them. -/
def printCall (params : List (String × Color)) (next : List (String × BagTerm)) : String :=
  match params with
  | [] => procName
  | _ =>
    let arg := fun (q : String × Color) =>
      match List.lookup q.1 next with
      | some bt => printExpr bt.term
      | none => q.1
    procName ++ "(" ++ String.intercalate ", " (params.map arg) ++ ")"

/-- One summand: `sum h : S . c -> a . Spec(g)`. -/
def printSummand (params : List (String × Color)) (S : Summand) : String :=
  printBinder S.binder ++ printExpr S.cond ++ " -> " ++ S.act ++ " . " ++
    printCall params S.next

/-- The whole specification: sort declarations, action declarations, the process equation and
the initial state.

The summand count and the parameter count are the structural check
`Implementation/docs/Target.md` §2 recommends running on every fixture:

> Summands after linearization must be exactly `|T| + 1`, and process parameters exactly `|P|`. -/
def printLpe (L : Lpe) : String :=
  let sorts := sortDecls (L.sorts ++ L.params.map Prod.snd)
  let sortBlock := if sorts.isEmpty then [] else [String.intercalate "\n" sorts, ""]
  let actBlock :=
    if L.acts.isEmpty then [] else ["act " ++ String.intercalate ", " L.acts ++ ";", ""]
  let paramDecl :=
    if L.params.isEmpty then ""
    else "(" ++ String.intercalate ", "
      (L.params.map fun q => q.1 ++ " : Bag(" ++ sortName q.2 ++ ")") ++ ")"
  let body :=
    match L.summands.map (printSummand L.params) with
    | [] => "    delta"
    | s :: ss =>
      String.intercalate "\n" (("    " ++ s) :: ss.map fun t => "  + " ++ t)
  let procBlock := ["proc " ++ procName ++ paramDecl ++ " =", body ++ ";", ""]
  let initArgs :=
    if L.params.isEmpty then procName
    else procName ++ "(" ++ String.intercalate ", " (L.params.map fun q =>
      match List.lookup q.1 L.init with
      | some bt => printExpr bt.term
      | none => "{:}") ++ ")"
  let initBlock := ["init " ++ initArgs ++ ";"]
  String.intercalate "\n" (sortBlock ++ actBlock ++ procBlock ++ initBlock) ++ "\n"

end Mcrl2

/-- The mCRL2 text of the LPE a CPN translates to: the whole pipeline of
`Implementation/docs/Plan.md` §2 from a validated `Net` to text. -/
def Net.toMcrl2 (N : Net) : String := Mcrl2.printLpe N.toLpe

end Cpn2mCrl2
