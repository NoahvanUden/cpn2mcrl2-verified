/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Printing the list encoding
 *
 * The second backend's printer. `src/Print.dfy` says what a printer is here -- a total function
 * over the whole term datatype, and the only part of the core nothing is proved about -- and
 * that applies unchanged.
 *
 * ## What it emits
 *
 * A place becomes `List(C(p))`, one list sort per place at that place's own color, rather than
 * the single tagged-union `token` sort of `Implementation/docs/Target.md` 3. That is the second
 * of `Implementation/docs/Plan.md` 5's two refinements, and taking it this way discharges it by
 * construction; `src/ListEncoding.dfy` says why nothing is lost.
 *
 * mCRL2 has no polymorphic user-defined maps, so the three multiset operations are declared
 * once per color: `rm` for removing one occurrence, `diff` for multiset difference, `sub` for
 * multiset inclusion. `rm` is the map `Implementation/docs/Target.md` 3 writes out by hand;
 * `diff` and `sub` are what a general arc expression needs, since it may move more than one
 * token.
 *
 * The one difference from `Target.md` 3 worth naming: that transcript writes `tok(h) in p1` and
 * `rm(tok(h), p1)` because every arc there moves exactly one token. Here the general form is
 * emitted -- `sub_Int([h], p1)` and `diff_Int(p1, [h])` -- and mCRL2's rewriter reduces those to
 * the same thing on a one-element list.
 */
module PrintList {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag
  import opened ListOps
  import opened Expr
  import opened Net
  import opened Semantics
  import opened Lpe
  import opened Translate
  import opened Correct
  import opened ListEncoding
  import opened Print

  /** The three multiset maps for one color, with their defining equations.
    *
    * The equation variables are named with a leading underscore so that they cannot shadow a
    * constructor of the user's own colors; nothing in the equations refers to anything but them
    * and mCRL2's own list operations. */
  function ListOpsDecl(c: Color): string
  {
    var s := SortName(c);
    var ls := "List(" + s + ")";
    var rm := RmName(c);
    var df := DiffName(c);
    var sb := SubName(c);
    Join("\n",
      [ "map " + rm + " : " + s + " # " + ls + " -> " + ls + ";",
        "    " + df + " : " + ls + " # " + ls + " -> " + ls + ";",
        "    " + sb + " : " + ls + " # " + ls + " -> Bool;",
        "var _x, _y : " + s + ";",
        "    _l, _m : " + ls + ";",
        "eqn " + rm + "(_x, []) = [];",
        "    " + rm + "(_x, _y |> _l) = if(_x == _y, _l, _y |> " + rm + "(_x, _l));",
        "    " + df + "(_l, []) = _l;",
        "    " + df + "(_l, _y |> _m) = " + df + "(" + rm + "(_y, _l), _m);",
        "    " + sb + "([], _m) = true;",
        "    " + sb + "(_y |> _l, _m) = (_y in _m) && " + sb + "(_l, " + rm + "(_y, _m));" ])
  }

  function ListOpsDecls(cs: seq<Color>): seq<string>
  {
    if |cs| == 0 then [] else [ListOpsDecl(cs[0])] + ListOpsDecls(cs[1..])
  }

  function ListCallArgs(params: seq<(string, Color)>, next: seq<(string, ListTerm)>):
      seq<string>
  {
    if |params| == 0 then []
    else
      var a := match Lookup(next, params[0].0)
               case Some(lt) => PrintExpr(lt.ltterm)
               case None => params[0].0;
      [a] + ListCallArgs(params[1..], next)
  }

  /** The recursive call of a list summand, one argument per place. */
  function PrintListCall(params: seq<(string, Color)>, next: seq<(string, ListTerm)>): string
  {
    if |params| == 0 then ProcName
    else ProcName + "(" + Join(", ", ListCallArgs(params, next)) + ")"
  }

  /** One summand of the list encoding. */
  function PrintListSummand(params: seq<(string, Color)>, s: ListSummand): string
  {
    PrintBinder(s.lbinder) + PrintExpr(s.lcond) + " -> " + s.lact + " . "
      + PrintListCall(params, s.lnext)
  }

  function PrintListSummands(params: seq<(string, Color)>, ss: seq<ListSummand>): seq<string>
  {
    if |ss| == 0 then []
    else [PrintListSummand(params, ss[0])] + PrintListSummands(params, ss[1..])
  }

  function ListInitArgs(params: seq<(string, Color)>, init: seq<(string, ListTerm)>):
      seq<string>
  {
    if |params| == 0 then []
    else
      var a := match Lookup(init, params[0].0)
               case Some(lt) => PrintExpr(lt.ltterm)
               case None => "[]";
      [a] + ListInitArgs(params[1..], init)
  }

  /** The whole list-encoded specification.
    *
    * The structural check of `Implementation/docs/Target.md` 2 applies to it unchanged:
    * `|T| + 1` summands and `|P|` process parameters after linearization. */
  function PrintListLpe(l: ListLpe): string
  {
    var sorts := SortDecls(l.lsorts + ParamColors(l.lparams));
    var sortBlock := if |sorts| == 0 then [] else [Join("\n", sorts), ""];
    var opColors := DedupColors(ParamColors(l.lparams), []);
    var opBlock :=
      if |opColors| == 0 then [] else [Join("\n\n", ListOpsDecls(opColors)), ""];
    var actBlock := if |l.lacts| == 0 then [] else ["act " + Join(", ", l.lacts) + ";", ""];
    var paramDecl :=
      if |l.lparams| == 0 then ""
      else "(" + Join(", ", ParamDecls(l.lparams, "List")) + ")";
    var body := SummandBlock(PrintListSummands(l.lparams, l.lsummands));
    var procBlock := ["proc " + ProcName + paramDecl + " =", body + ";", ""];
    var initArgs :=
      if |l.lparams| == 0 then ProcName
      else ProcName + "(" + Join(", ", ListInitArgs(l.lparams, l.linit)) + ")";
    Join("\n", sortBlock + opBlock + actBlock + procBlock + ["init " + initArgs + ";"]) + "\n"
  }

  /** The mCRL2 text of the list-encoded LPE: the fast backend of
    * `Implementation/docs/Plan.md` 5, whose refinement of the bag encoding
    * `src/ListEncoding.dfy` proves. */
  function ToMcrl2List(n: Net): string
  {
    PrintListLpe(ToLpeList(n))
  }
}
