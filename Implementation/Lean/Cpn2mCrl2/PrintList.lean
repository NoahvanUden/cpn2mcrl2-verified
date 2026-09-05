/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Print
import Cpn2mCrl2.ListEncoding

/-!
# Printing the list encoding

The second backend's printer. `Cpn2mCrl2/Print.lean` says what a printer is here -- a total
function on a well-typed term, and the only part of the core nothing is proved about -- and
that applies unchanged.

## What it emits

A place becomes `List(C(p))`, one list sort per place at that place's own color, rather than
the single tagged-union `token` sort of `Implementation/docs/Target.md` §3. That is the second
of `Implementation/docs/Plan.md` §5's two refinements, and taking it this way discharges it by
construction; `Cpn2mCrl2/ListEncoding.lean` says why nothing is lost.

mCRL2 has no polymorphic user-defined maps, so the three multiset operations are declared once
per color: `rm` for removing one occurrence, `diff` for multiset difference, `sub` for multiset
inclusion. `rm` is the map `Implementation/docs/Target.md` §3 writes out by hand; `diff` and
`sub` are what a general arc expression needs, since it may move more than one token.

The one difference from `Target.md` §3 worth naming: that transcript writes `tok(h) in p1` and
`rm(tok(h), p1)` because every arc there moves exactly one token. Here the general form is
emitted -- `sub_Int([h], p1)` and `diff_Int(p1, [h])` -- and mCRL2's rewriter reduces those to
the same thing on a one-element list.
-/

namespace Cpn2mCrl2

namespace Mcrl2

/-- The three multiset maps for one color, with their defining equations.

The equation variables are named with a leading underscore so that they cannot shadow a
constructor of the user's own colors; nothing in the equations refers to anything but them and
mCRL2's own list operations. -/
def listOpsDecl (c : Color) : String :=
  let S := sortName c
  let LS := "List(" ++ S ++ ")"
  let rm := rmName c
  let df := diffName c
  let sb := subName c
  String.intercalate "\n"
    [ "map " ++ rm ++ " : " ++ S ++ " # " ++ LS ++ " -> " ++ LS ++ ";",
      "    " ++ df ++ " : " ++ LS ++ " # " ++ LS ++ " -> " ++ LS ++ ";",
      "    " ++ sb ++ " : " ++ LS ++ " # " ++ LS ++ " -> Bool;",
      "var _x, _y : " ++ S ++ ";",
      "    _l, _m : " ++ LS ++ ";",
      "eqn " ++ rm ++ "(_x, []) = [];",
      "    " ++ rm ++ "(_x, _y |> _l) = if(_x == _y, _l, _y |> " ++ rm ++ "(_x, _l));",
      "    " ++ df ++ "(_l, []) = _l;",
      "    " ++ df ++ "(_l, _y |> _m) = " ++ df ++ "(" ++ rm ++ "(_y, _l), _m);",
      "    " ++ sb ++ "([], _m) = true;",
      "    " ++ sb ++ "(_y |> _l, _m) = (_y in _m) && " ++ sb ++ "(_l, " ++ rm ++ "(_y, _m));" ]

/-- The recursive call of a list summand, one argument per place. -/
def printListCall (params : List (String × Color)) (next : List (String × ListTerm)) :
    String :=
  match params with
  | [] => procName
  | _ =>
    let arg := fun (q : String × Color) =>
      match List.lookup q.1 next with
      | some lt => printExpr lt.term
      | none => q.1
    procName ++ "(" ++ String.intercalate ", " (params.map arg) ++ ")"

/-- One summand of the list encoding. -/
def printListSummand (params : List (String × Color)) (S : ListSummand) : String :=
  printBinder S.binder ++ printExpr S.cond ++ " -> " ++ S.act ++ " . " ++
    printListCall params S.next

/-- The whole list-encoded specification.

The structural check of `Implementation/docs/Target.md` §2 applies to it unchanged: `|T| + 1`
summands and `|P|` process parameters after linearization. -/
def printListLpe (L : ListLpe) : String :=
  let sorts := sortDecls (L.sorts ++ L.params.map Prod.snd)
  let sortBlock := if sorts.isEmpty then [] else [String.intercalate "\n" sorts, ""]
  let opColors := (L.params.map Prod.snd).foldl
    (fun acc c => if acc.any (fun d => sortName d == sortName c) then acc else acc ++ [c]) []
  let opBlock :=
    if opColors.isEmpty then []
    else [String.intercalate "\n\n" (opColors.map listOpsDecl), ""]
  let actBlock :=
    if L.acts.isEmpty then [] else ["act " ++ String.intercalate ", " L.acts ++ ";", ""]
  let paramDecl :=
    if L.params.isEmpty then ""
    else "(" ++ String.intercalate ", "
      (L.params.map fun q => q.1 ++ " : List(" ++ sortName q.2 ++ ")") ++ ")"
  let body :=
    match L.summands.map (printListSummand L.params) with
    | [] => "    delta"
    | s :: ss =>
      String.intercalate "\n" (("    " ++ s) :: ss.map fun t => "  + " ++ t)
  let procBlock := ["proc " ++ procName ++ paramDecl ++ " =", body ++ ";", ""]
  let initArgs :=
    if L.params.isEmpty then procName
    else procName ++ "(" ++ String.intercalate ", " (L.params.map fun q =>
      match List.lookup q.1 L.init with
      | some lt => printExpr lt.term
      | none => "[]") ++ ")"
  String.intercalate "\n"
    (sortBlock ++ opBlock ++ actBlock ++ procBlock ++ ["init " ++ initArgs ++ ";"]) ++ "\n"

end Mcrl2

/-- The mCRL2 text of the list-encoded LPE: the fast backend of
`Implementation/docs/Plan.md` §5, whose refinement of the bag encoding
`Cpn2mCrl2/ListEncoding.lean` proves. -/
def Net.toMcrl2List (N : Net) : String := Mcrl2.printListLpe N.toLpeList

end Cpn2mCrl2
