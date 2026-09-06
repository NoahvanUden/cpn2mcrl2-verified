/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Printing mCRL2
 *
 * The last link of the chain, and the only part of the verified core that nothing is proved
 * about. `Implementation/docs/Plan.md` 3 puts it this way:
 *
 * > The printer is the only unverifiable part of the core, and it is the smallest. Keeping the
 * > LPE term intrinsically typed means the printer is a total function on a well-typed AST,
 * > with no failure modes of its own beyond string formatting.
 *
 * The second sentence is the Lean shape of the argument and it does not transfer, because
 * `Expr` here is not intrinsically typed. What survives is the conclusion, and by an easier
 * route: `PrintExpr` is a structural recursion over a flat datatype, so it is total on *every*
 * `Expr`, well-sorted or not, and there is no case to reject and no proof obligation to
 * discharge before calling it. Printing is one of the few places where having no dependent
 * types costs nothing at all.
 *
 * What it cannot establish is tier T4 -- that `mcrl22lps` reads the text back as the term that
 * was printed -- which `Implementation/docs/Plan.md` 2 rules out of scope for want of a
 * formalized mCRL2 grammar, and which `scripts/check.sh` tests instead.
 *
 * ## The encoding
 *
 * `Implementation/docs/Target.md` 1 fixes it, having checked each operator against the toolset:
 *
 * | Definition 14 writes | printed as |
 * | --- | --- |
 * | `C(p)_MS`   | `Bag(C)`    |
 * | the empty bag | `{:}`     |
 * | `{n`e}`     | `{e: n}`    |
 * | `m1 union m2` | `m1 + m2` |
 * | `m1 \ m2`   | `m1 - m2`   |
 * | `m1 subseteq m2` | `m1 <= m2` |
 *
 * Colors become sorts: `Bool` and `Int` are mCRL2's own, an enumeration is
 * `struct id1 | id2 | ...`, and a record is `struct R(f1 : S1, ...)` whose field names are
 * mCRL2's projection functions, so `EProj` prints as `f(e)`. mCRL2 accepts a constructor with
 * the same name as its sort, which is what keeps the printed names the ones the CPN file used.
 *
 * Everything is fully parenthesized. That is uglier than `Implementation/docs/Target.md` 2
 * prints by hand, and it is deliberate: precedence is exactly the sort of thing a printer gets
 * wrong, and T4 is tested rather than proved.
 *
 * ## Identifiers
 *
 * `Implementation/docs/Target.md` 1 flags one hazard:
 *
 * > One implementation note that will bite a code generator: **`val` is a reserved keyword**,
 * > so record field names taken from a CPN's color definitions must be checked against mCRL2's
 * > keyword list and escaped.
 *
 * `IsSafeIdent` is that check. It is not escaping but rejection, done by the importer at the
 * boundary: a CPN whose names collide with mCRL2's is refused with a message, rather than
 * silently renamed into something the user did not write.
 */
module Print {

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

  /** The name the emitted process is given. Reserved along with the keywords, so that no place,
    * transition or variable can shadow it. */
  const ProcName: string := "Spec"

  /** The keywords of the mCRL2 language, which an identifier taken from a CPN file may not
    * be. */
  const Keywords: seq<string> :=
    ["sort", "cons", "map", "var", "eqn", "act", "proc", "init", "struct", "glob", "pbes",
     "Bool", "Pos", "Nat", "Int", "Real", "List", "Set", "Bag", "FSet", "FBag",
     "true", "false", "whr", "end", "lambda", "forall", "exists", "div", "mod", "in", "if",
     "delta", "tau", "sum", "block", "allow", "hide", "rename", "comm", "val", "yaled",
     "delay", "nu", "mu", "min", "max", "succ", "pred", "abs", "floor", "ceil", "round", "exp",
     "A2B", "head", "tail", "rhead", "rtail", "count", "Nat2Pos", "Pos2Nat", "Int2Nat",
     "Nat2Int", "Int2Real", "Real2Int", "Nat2Real", "Real2Nat", "Pos2Real", "Real2Pos",
     "Spec"]

  predicate IsIdentStart(ch: char)
  {
    ('a' <= ch <= 'z') || ('A' <= ch <= 'Z') || ch == '_'
  }

  predicate IsIdentChar(ch: char)
  {
    IsIdentStart(ch) || ('0' <= ch <= '9') || ch == '\''
  }

  predicate AllIdentChars(s: string)
  {
    |s| == 0 || (IsIdentChar(s[0]) && AllIdentChars(s[1..]))
  }

  /** Whether a name taken from a CPN file may be printed as an mCRL2 identifier: a letter or
    * underscore followed by letters, digits, underscores and primes, and not a keyword.
    *
    * `Cpn2mCrl2/Print.lean` uses Lean's `Char.isAlpha`, which is Unicode-aware; this is ASCII
    * only, which is stricter and is what the mCRL2 grammar actually admits.
    *
    * The importer refuses a net that fails this, rather than renaming behind the user's
    * back. */
  predicate IsSafeIdent(s: string)
  {
    |s| > 0 && IsIdentStart(s[0]) && AllIdentChars(s[1..]) && s !in Keywords
  }

  // ---------------------------------------------------------------------------------------
  // Sorts
  // ---------------------------------------------------------------------------------------

  /** The mCRL2 sort a color is printed as. */
  function SortName(c: Color): string
  {
    match c
    case CBool => "Bool"
    case CInt => "Int"
    case CEnum(n, _) => n
    case CRecord(n, _) => n
  }

  /** The mCRL2 sort an expression type is printed as. */
  function SortRef(t: ExprTy): string
  {
    match t
    case CT(c) => SortName(c)
    case BT(c) => "Bag(" + SortName(c) + ")"
    case LT(c) => "List(" + SortName(c) + ")"
  }

  /** The name of the `rm` map for a color. mCRL2 has no polymorphic user-defined maps, so the
    * three list operations the second backend needs are declared once per color. */
  function RmName(c: Color): string { "rm_" + SortName(c) }

  /** The name of the multiset-difference map for a color. */
  function DiffName(c: Color): string { "diff_" + SortName(c) }

  /** The name of the multiset-inclusion map for a color. */
  function SubName(c: Color): string { "sub_" + SortName(c) }

  /** The colors that need a `sort` declaration, including those reached through record
    * fields. */
  function NamedColors(c: Color): seq<Color>
    decreases c, 1
  {
    match c
    case CBool => []
    case CInt => []
    case CEnum(n, ids) => [CEnum(n, ids)]
    case CRecord(n, fs) => [CRecord(n, fs)] + NamedColorsFields(fs)
  }

  function NamedColorsFields(fs: ColorFields): seq<Color>
    decreases fs, 0
  {
    match fs
    case CFNil => []
    case CFCons(_, c, rest) => NamedColors(c) + NamedColorsFields(rest)
  }

  function AllNamedColors(cs: seq<Color>): seq<Color>
  {
    if |cs| == 0 then [] else NamedColors(cs[0]) + AllNamedColors(cs[1..])
  }

  /** One entry per distinct sort name, keeping the first mention. */
  function DedupColors(cs: seq<Color>, seen: seq<string>): seq<Color>
  {
    if |cs| == 0 then []
    else if SortName(cs[0]) in seen then DedupColors(cs[1..], seen)
    else [cs[0]] + DedupColors(cs[1..], seen + [SortName(cs[0])])
  }

  /** The field declarations of a record sort. */
  function FieldDecls(fs: ColorFields): seq<string>
  {
    match fs
    case CFNil => []
    case CFCons(n, c, rest) => [n + " : " + SortName(c)] + FieldDecls(rest)
  }

  /** The `sort` declaration of a color, if it needs one. */
  function SortDecl(c: Color): Option<string>
  {
    match c
    case CBool => None
    case CInt => None
    case CEnum(n, ids) => Some("sort " + n + " = struct " + Join(" | ", ids) + ";")
    case CRecord(n, fs) =>
      var ds := FieldDecls(fs);
      if |ds| == 0 then Some("sort " + n + " = struct " + n + ";")
      else Some("sort " + n + " = struct " + n + "(" + Join(", ", ds) + ");")
  }

  function SortDeclsOf(cs: seq<Color>): seq<string>
  {
    if |cs| == 0 then []
    else match SortDecl(cs[0])
         case Some(d) => [d] + SortDeclsOf(cs[1..])
         case None => SortDeclsOf(cs[1..])
  }

  /** The `sort` declarations of a sequence of colors, each emitted once. */
  function SortDecls(cs: seq<Color>): seq<string>
  {
    SortDeclsOf(DedupColors(AllNamedColors(cs), []))
  }

  // ---------------------------------------------------------------------------------------
  // Terms
  // ---------------------------------------------------------------------------------------

  /** An integer literal, parenthesized when negative so that `{-1: 1}` cannot be misread. */
  function IntLit(n: int): string
  {
    if n < 0 then "(" + IntToString(n) + ")" else IntToString(n)
  }

  /** An expression as mCRL2 text. Total on every `Expr`. */
  function PrintExpr(e: Expr): string
    decreases e, 1
  {
    match e
    case EVar(x, _) => x
    case EInt(n) => IntLit(n)
    case EBool(b) => if b then "true" else "false"
    case ECtor(_, id) => id
    case EMkRec(c, args) =>
      var as' := PrintArgs(args);
      if |as'| == 0 then SortName(c)
      else SortName(c) + "(" + Join(", ", as') + ")"
    case EProj(e0, f) => f + "(" + PrintExpr(e0) + ")"
    case EAdd(a, b) => "(" + PrintExpr(a) + " + " + PrintExpr(b) + ")"
    case ESub(a, b) => "(" + PrintExpr(a) + " - " + PrintExpr(b) + ")"
    case EMul(a, b) => "(" + PrintExpr(a) + " * " + PrintExpr(b) + ")"
    case EEq(a, b) => "(" + PrintExpr(a) + " == " + PrintExpr(b) + ")"
    case ELe(a, b) => "(" + PrintExpr(a) + " <= " + PrintExpr(b) + ")"
    case ELt(a, b) => "(" + PrintExpr(a) + " < " + PrintExpr(b) + ")"
    case EAnd(a, b) => "(" + PrintExpr(a) + " && " + PrintExpr(b) + ")"
    case EOr(a, b) => "(" + PrintExpr(a) + " || " + PrintExpr(b) + ")"
    case ENot(a) => "(!" + PrintExpr(a) + ")"
    case EEmptyBag(_) => "{:}"
    case ESingle(k, e0) => "{" + PrintExpr(e0) + ": " + NatToString(k) + "}"
    case EBagUnion(a, b) => "(" + PrintExpr(a) + " + " + PrintExpr(b) + ")"
    case EBagDiff(a, b) => "(" + PrintExpr(a) + " - " + PrintExpr(b) + ")"
    case EBagSubset(a, b) => "(" + PrintExpr(a) + " <= " + PrintExpr(b) + ")"
    case ENilList(_) => "[]"
    case ESnoc(l, e0) =>
      (match SnocItems(l)
       case Some(items) => "[" + Join(", ", items + [PrintExpr(e0)]) + "]"
       case None => "(" + PrintExpr(l) + " <| " + PrintExpr(e0) + ")")
    case EAppendList(a, b) => "(" + PrintExpr(a) + " ++ " + PrintExpr(b) + ")"
    case EDiffList(a, b) =>
      DiffName(ListColorOf(a)) + "(" + PrintExpr(a) + ", " + PrintExpr(b) + ")"
    case ESubList(a, b) =>
      SubName(ListColorOf(a)) + "(" + PrintExpr(a) + ", " + PrintExpr(b) + ")"
  }

  /** `PrintExpr`, one record field at a time. */
  function PrintArgs(args: Args): seq<string>
    decreases args, 0
  {
    match args
    case ANil => []
    case ACons(_, e, rest) => [PrintExpr(e)] + PrintArgs(rest)
  }

  /** The elements of a list term built from `[]` by `<|`, so that it can be printed as mCRL2's
    * own list literal rather than as a chain of appends. `None` for anything else. */
  function SnocItems(e: Expr): Option<seq<string>>
    decreases e, 0
  {
    match e
    case ENilList(_) => Some([])
    case ESnoc(l, e0) =>
      (match SnocItems(l)
       case Some(items) => Some(items + [PrintExpr(e0)])
       case None => None)
    case _ => None
  }

  /** The color a list-sorted term holds, for naming the per-color `diff` and `sub` maps.
    *
    * `Cpn2mCrl2/Print.lean` reads this off the index of `Expr.diffList`; here it comes from
    * `SortOf`, and falls back on `Bool` for a term that has no sort. The fallback is
    * unreachable for anything `src/ListEncoding.dfy` builds, and a wrong sort name here would
    * be caught by `mcrl22lps` -- which is tier T0, and is what `scripts/check.sh` runs. */
  function ListColorOf(e: Expr): Color
  {
    match SortOf(e)
    case Some(LT(c)) => c
    case _ => CBool
  }

  // ---------------------------------------------------------------------------------------
  // The specification
  // ---------------------------------------------------------------------------------------

  function BinderDecls(binder: Ctx): seq<string>
  {
    if |binder| == 0 then []
    else [binder[0].0 + " : " + SortRef(binder[0].1)] + BinderDecls(binder[1..])
  }

  /** The binder of a summand: `sum v : S, w : T .`, or nothing when `Var(t)` is empty. */
  function PrintBinder(binder: Ctx): string
  {
    if |binder| == 0 then ""
    else "sum " + Join(", ", BinderDecls(binder)) + " . "
  }

  function CallArgs(params: seq<(string, Color)>, next: seq<(string, BagTerm)>): seq<string>
  {
    if |params| == 0 then []
    else
      var a := match Lookup(next, params[0].0)
               case Some(bt) => PrintExpr(bt.btterm)
               case None => params[0].0;
      [a] + CallArgs(params[1..], next)
  }

  /** The recursive call of a summand, with one argument per place in the order the process
    * declares them. */
  function PrintCall(params: seq<(string, Color)>, next: seq<(string, BagTerm)>): string
  {
    if |params| == 0 then ProcName
    else ProcName + "(" + Join(", ", CallArgs(params, next)) + ")"
  }

  /** One summand: `sum h : S . c -> a . Spec(g)`. */
  function PrintSummand(params: seq<(string, Color)>, s: Summand): string
  {
    PrintBinder(s.binder) + PrintExpr(s.cond) + " -> " + s.act + " . "
      + PrintCall(params, s.next)
  }

  function PrintSummands(params: seq<(string, Color)>, ss: seq<Summand>): seq<string>
  {
    if |ss| == 0 then []
    else [PrintSummand(params, ss[0])] + PrintSummands(params, ss[1..])
  }

  /** The `+ ` prefixes that separate the summands of the process body. */
  function SummandBlock(printed: seq<string>): string
  {
    if |printed| == 0 then "    delta"
    else Join("\n", ["    " + printed[0]] + PrefixEach("  + ", printed[1..]))
  }

  function PrefixEach(p: string, ss: seq<string>): seq<string>
  {
    if |ss| == 0 then [] else [p + ss[0]] + PrefixEach(p, ss[1..])
  }

  function ParamDecls(params: seq<(string, Color)>, wrap: string): seq<string>
  {
    if |params| == 0 then []
    else [params[0].0 + " : " + wrap + "(" + SortName(params[0].1) + ")"]
         + ParamDecls(params[1..], wrap)
  }

  function InitArgs(params: seq<(string, Color)>, init: seq<(string, BagTerm)>): seq<string>
  {
    if |params| == 0 then []
    else
      var a := match Lookup(init, params[0].0)
               case Some(bt) => PrintExpr(bt.btterm)
               case None => "{:}";
      [a] + InitArgs(params[1..], init)
  }

  function ParamColors(params: seq<(string, Color)>): seq<Color>
  {
    if |params| == 0 then [] else [params[0].1] + ParamColors(params[1..])
  }

  /** The whole specification: sort declarations, action declarations, the process equation and
    * the initial state.
    *
    * The summand count and the parameter count are the structural check
    * `Implementation/docs/Target.md` 2 recommends running on every fixture:
    *
    * > Summands after linearization must be exactly `|T| + 1`, and process parameters exactly
    * > `|P|`. */
  function PrintLpe(l: Lpe): string
  {
    var sorts := SortDecls(l.sorts + ParamColors(l.params));
    var sortBlock := if |sorts| == 0 then [] else [Join("\n", sorts), ""];
    var actBlock := if |l.acts| == 0 then [] else ["act " + Join(", ", l.acts) + ";", ""];
    var paramDecl :=
      if |l.params| == 0 then ""
      else "(" + Join(", ", ParamDecls(l.params, "Bag")) + ")";
    var body := SummandBlock(PrintSummands(l.params, l.summands));
    var procBlock := ["proc " + ProcName + paramDecl + " =", body + ";", ""];
    var initArgs :=
      if |l.params| == 0 then ProcName
      else ProcName + "(" + Join(", ", InitArgs(l.params, l.init)) + ")";
    Join("\n", sortBlock + actBlock + procBlock + ["init " + initArgs + ";"]) + "\n"
  }

  /** The mCRL2 text of the LPE a CPN translates to: the whole pipeline of
    * `Implementation/docs/Plan.md` 2 from a validated `Net` to text. */
  function ToMcrl2(n: Net): string
  {
    PrintLpe(ToLpe(n))
  }
}
