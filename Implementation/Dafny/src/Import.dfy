/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # The importer
 *
 * Reading the native CPN format of `Implementation/docs/InputFormat.md` 4, and the T1
 * validation that turns it into a `Net`.
 *
 * This file is **outside the trust boundary**. `Implementation/docs/Plan.md` 3 draws the line:
 *
 * > The standard verified-compiler shape: a small verified core with unverified adapters
 * > outside the trust boundary.
 *
 * Nothing here is proved about. What it produces is a `Net` for which `Valid` has been
 * *decided*, and from that point on the core has the T1 hypotheses of
 * `Implementation/docs/InputFormat.md` 4.3 available, which is the whole purpose of doing the
 * validation at the boundary.
 *
 * ## Where this differs from the Lean importer, and why it matters
 *
 * `Cpn2mCrl2/Json.lean` type-checks into an intrinsically typed `Expr τ`, so once its checker
 * returns, checks 4 to 6 of `InputFormat.md` 4.3 hold *by construction* and `Net.Valid` does
 * not even mention them. Here the checker returns a plain `Expr` that it believes has the right
 * sort, and nothing about this file guarantees that belief.
 *
 * The guarantee is recovered a step later and is exactly as strong. `Valid` carries the four
 * `WellTyped` conjuncts, `NetOfJson` decides `Valid` before returning, and a net whose checker
 * went wrong is refused there. So both translators reach the core with the same hypotheses; one
 * gets them from the type of the checker's result and the other from a check on it. The cost of
 * having no dependent types is that the property is tested per net rather than held once for
 * all nets -- which for a program that runs the check anyway is no cost at all.
 *
 * ## Fuel
 *
 * `Cpn2mCrl2/Json.lean` writes its checker as four mutually recursive `partial def`s. It has to:
 * the inference direction calls the checking direction back on the *same* JSON node when it has
 * just learned the node's sort, so the recursion is not structural. Dafny has no `partial`, so
 * the same recursion is bounded by a fuel counter derived from the length of the input, which
 * is more than the number of nested calls the tree can produce. Running out of fuel is an error
 * message, not a loop.
 *
 * ## The grammar it accepts
 *
 * Exactly `Implementation/docs/InputFormat.md` 4.1, as JSON arrays whose head is the operator:
 *
 *     ["var", x] | ["int", n] | ["bool", b] | ["ctor", id]
 *     ["rec", C, [[field, e], ...]] | ["proj", e, field]
 *     ["+", a, b] | ["-", a, b] | ["*", a, b]
 *     ["=", a, b] | ["<=", a, b] | ["<", a, b]
 *     ["&&", a, b] | ["||", a, b] | ["!", a]
 *     ["bag", [[n, e], ...]] | ["emptyBag"] | ["union", a, b] | ["diff", a, b]
 *
 * `EBagSubset` is deliberately absent: it is the one operation Definition 14 assembles and a CPN
 * never contains, and `src/Expr.dfy` says so where it is declared.
 */
module Import {

  import opened Std.Wrappers
  import API = Std.JSON.API
  import opened Std.BoundedInts
  import J = Std.JSON.Values
  import opened Util
  import opened Colors
  import opened Bags
  import opened ListOps
  import opened Exprs
  import opened Nets
  import opened Semantics
  import opened Lpes
  import opened Translate
  import opened Print

  /** The importer's error monad. */
  type M<T> = Result<T, string>

  // ---------------------------------------------------------------------------------------
  // Reading JSON
  // ---------------------------------------------------------------------------------------

  function GetObj(j: J.JSON): M<seq<(string, J.JSON)>>
    ensures GetObj(j).Success? ==> j.Object? && GetObj(j).value == j.obj
  {
    if j.Object? then Success(j.obj) else Failure("expected an object")
  }

  function GetArr(j: J.JSON): M<seq<J.JSON>>
    ensures GetArr(j).Success? ==> j.Array? && GetArr(j).value == j.arr
  {
    if j.Array? then Success(j.arr) else Failure("expected an array")
  }

  function GetStr(j: J.JSON): M<string>
  {
    if j.String? then Success(j.str) else Failure("expected a string")
  }

  function GetBool(j: J.JSON): M<bool>
  {
    if j.Bool? then Success(j.b) else Failure("expected a boolean")
  }

  function Pow10(e: nat): nat
  {
    if e == 0 then 1 else 10 * Pow10(e - 1)
  }

  /** A JSON number as an integer. The standard library's `Decimal(n, e10)` carries a mantissa
    * and a power of ten, so `1e2` is accepted and `1.5` is refused. */
  function GetInt(j: J.JSON): M<int>
  {
    if !j.Number? then Failure("expected a number")
    else if j.num.e10 < 0 then Failure("expected a whole number")
    else Success(j.num.n * Pow10(j.num.e10))
  }

  function GetNat(j: J.JSON): M<nat>
  {
    var i :- GetInt(j);
    if i < 0 then Failure("expected a non-negative number") else Success(i)
  }

  /** The value of a field of a JSON object. */
  function Field(j: J.JSON, name: string): M<J.JSON>
  {
    var o :- GetObj(j);
    match Lookup(o, name)
    case Some(v) => Success(v)
    case None => Failure("missing field " + name)
  }

  /** The `i`th element of an array, by name so that a failure can say which. */
  function Idx(a: seq<J.JSON>, i: nat, what: string): M<J.JSON>
  {
    if i < |a| then Success(a[i]) else Failure(what + ": missing element " + NatToString(i))
  }

  /** The entries of a JSON object, sorted by key.
    *
    * Lean's `Json` holds an object as a balanced tree, so `toList` hands `Cpn2mCrl2/Json.lean`
    * its entries in key order. The standard library here keeps them in file order, so they are
    * sorted explicitly -- which makes the two translators emit places, transitions and
    * variables in the same order, and so makes their output comparable as text. */
  function Entries(j: J.JSON): M<seq<(string, J.JSON)>>
  {
    var o :- GetObj(j);
    Success(SortByKey(o))
  }

  function CheckIdent(kind: string, s: string): M<string>
  {
    if IsSafeIdent(s) then Success(s)
    else Failure(kind + " " + s
      + " is not usable as an mCRL2 identifier: it is a reserved keyword, or not a letter or"
      + " underscore followed by letters, digits, underscores and primes")
  }

  // ---------------------------------------------------------------------------------------
  // Colors
  // ---------------------------------------------------------------------------------------

  function CheckIdents(kind: string, ss: seq<J.JSON>): M<seq<string>>
  {
    if |ss| == 0 then Success([])
    else
      var s :- GetStr(ss[0]);
      var head :- CheckIdent(kind, s);
      var rest :- CheckIdents(kind, ss[1..]);
      Success([head] + rest)
  }

  /** Resolve a color *name* into the color tree `src/Color.dfy` holds.
    *
    * A record field names another color, so resolution recurses; `fuel` bounds the recursion by
    * the number of declarations, which turns a cyclic definition into an error instead of a
    * loop. */
  function ResolveColor(decls: seq<(string, J.JSON)>, fuel: nat, name: string): M<Color>
    decreases fuel, 1
  {
    if fuel == 0 then
      Failure("color " + name
        + " is defined cyclically, or nested deeper than there are colors")
    else
      match Lookup(decls, name)
      case None => Failure("undeclared color " + name)
      case Some(j) =>
        var kj :- Field(j, "kind");
        var kind :- GetStr(kj);
        if kind == "bool" then Success(CBool)
        else if kind == "int" then Success(CInt)
        else if kind == "enum" then
          var _ :- CheckIdent("color", name);
          var idsj :- Field(j, "ids");
          var arr :- GetArr(idsj);
          var ids :- CheckIdents("constructor", arr);
          if |ids| == 0 then
            Failure("enumeration " + name + " has no constructors, so it has no values")
          else Success(CEnum(name, ids))
        else if kind == "record" then
          var _ :- CheckIdent("color", name);
          var fsj :- Field(j, "fields");
          var arr :- GetArr(fsj);
          var fs :- ResolveFields(decls, fuel, arr);
          Success(CRecord(name, fs))
        else Failure("color " + name + " has unknown kind " + kind)
  }

  function ResolveFields(decls: seq<(string, J.JSON)>, fuel: nat, arr: seq<J.JSON>):
      M<ColorFields>
    requires fuel > 0
    decreases fuel, 0, |arr|
  {
    if |arr| == 0 then Success(CFNil)
    else
      var p :- GetArr(arr[0]);
      var f0 :- Idx(p, 0, "record field");
      var fname0 :- GetStr(f0);
      var fname :- CheckIdent("field", fname0);
      var c0 :- Idx(p, 1, "record field");
      var cname :- GetStr(c0);
      var c :- ResolveColor(decls, fuel - 1, cname);
      var rest :- ResolveFields(decls, fuel, arr[1..]);
      Success(CFCons(fname, c, rest))
  }

  // ---------------------------------------------------------------------------------------
  // Expressions
  //
  // Bidirectional type checking, in four mutually recursive functions.
  //
  // `CheckDirected` dispatches on the *expected sort*, which is what lets `["emptyBag"]`,
  // `["ctor", id]` and `["rec", ...]` be written without an annotation: their color comes from
  // the place or the guard they annotate. It answers `None` for a head the sort does not
  // settle, and `CheckExpr` then falls through `CoerceTo` to `InferExpr`.
  //
  // The fuel is what makes this a Dafny function at all: `InferExpr` calls `CheckDirected` back
  // on the same node once it has learned the node's sort, so the recursion is not structural.
  // ---------------------------------------------------------------------------------------

  function CheckExpr(vars: Ctx, colors: seq<Color>, fuel: nat, j: J.JSON, t: ExprTy): M<Expr>
    decreases fuel, 3
  {
    if fuel == 0 then Failure("expression is nested deeper than the input is long")
    else
      var direct :- CheckDirected(vars, colors, fuel - 1, j, t);
      match direct
      case Some(e) => Success(e)
      case None => CoerceTo(vars, colors, fuel - 1, j, t)
  }

  /** Infer the sort of an expression and require it to be the expected one. */
  function CoerceTo(vars: Ctx, colors: seq<Color>, fuel: nat, j: J.JSON, t: ExprTy): M<Expr>
    decreases fuel, 2
  {
    if fuel == 0 then Failure("expression is nested deeper than the input is long")
    else
      var s :- InferExpr(vars, colors, fuel - 1, j);
      if s.0 == t then Success(s.1)
      else Failure("expression has sort " + SortRef(s.0) + " where " + SortRef(t)
                   + " is expected")
  }

  /** The half of checking that the expected sort settles on its own. `None` means "this head is
    * not one the sort decides"; the caller falls through to inference. */
  function CheckDirected(vars: Ctx, colors: seq<Color>, fuel: nat, j: J.JSON, t: ExprTy):
      M<Option<Expr>>
    decreases fuel, 1
  {
    if fuel == 0 then Failure("expression is nested deeper than the input is long")
    else
      var a :- GetArr(j);
      var h0 :- Idx(a, 0, "expression");
      var hd :- GetStr(h0);
      match t
      case BT(c) =>
        if hd == "emptyBag" then Success(Some(EEmptyBag(c)))
        else if hd == "bag" then
          var itemsj :- Idx(a, 1, "bag literal");
          var items :- GetArr(itemsj);
          var terms :- CheckBagItems(vars, colors, fuel - 1, items, c);
          Success(Some(UnionAll(c, terms)))
        else if hd == "union" then
          var x :- Idx(a, 1, "union");
          var y :- Idx(a, 2, "union");
          var ex :- CheckExpr(vars, colors, fuel - 1, x, BT(c));
          var ey :- CheckExpr(vars, colors, fuel - 1, y, BT(c));
          Success(Some(EBagUnion(ex, ey)))
        else if hd == "diff" then
          var x :- Idx(a, 1, "diff");
          var y :- Idx(a, 2, "diff");
          var ex :- CheckExpr(vars, colors, fuel - 1, x, BT(c));
          var ey :- CheckExpr(vars, colors, fuel - 1, y, BT(c));
          Success(Some(EBagDiff(ex, ey)))
        else Success(None)
      case CT(CEnum(n, ids)) =>
        if hd == "ctor" then
          var idj :- Idx(a, 1, "constructor");
          var id :- GetStr(idj);
          if id in ids then Success(Some(ECtor(CEnum(n, ids), id)))
          else Failure(id + " is not a constructor of the enumeration " + n)
        else Success(None)
      case CT(CRecord(n, fs)) =>
        if hd == "rec" then
          var arrj :- Idx(a, 2, "record literal");
          var arr :- GetArr(arrj);
          var given :- RecordFields(arr);
          var _ :- CheckGivenFields(n, given, fs);
          var args :- CheckArgs(vars, colors, fuel - 1, n, given, fs);
          Success(Some(EMkRec(CRecord(n, fs), args)))
        else Success(None)
      case _ => Success(None)
  }

  function CheckBagItems(vars: Ctx, colors: seq<Color>, fuel: nat, items: seq<J.JSON>,
                         c: Color): M<seq<Expr>>
    decreases fuel, 4, |items|
  {
    if |items| == 0 then Success([])
    else
      var p :- GetArr(items[0]);
      var nj :- Idx(p, 0, "bag item");
      var k :- GetNat(nj);
      var ej :- Idx(p, 1, "bag item");
      var e :- CheckExpr(vars, colors, fuel, ej, CT(c));
      var rest :- CheckBagItems(vars, colors, fuel, items[1..], c);
      Success([ESingle(k, e)] + rest)
  }

  function RecordFields(arr: seq<J.JSON>): M<seq<(string, J.JSON)>>
  {
    if |arr| == 0 then Success([])
    else
      var p :- GetArr(arr[0]);
      var fj :- Idx(p, 0, "record field");
      var f :- GetStr(fj);
      var ej :- Idx(p, 1, "record field");
      var rest :- RecordFields(arr[1..]);
      Success([(f, ej)] + rest)
  }

  /** Every field the literal gives is a field the color has. */
  function CheckGivenFields(n: string, given: seq<(string, J.JSON)>, fs: ColorFields): M<bool>
  {
    if |given| == 0 then Success(true)
    else if FieldColor(fs, given[0].0).None? then
      Failure("record literal for " + n + " gives a field " + given[0].0
              + " that the color does not have")
    else CheckGivenFields(n, given[1..], fs)
  }

  /** One expression per field of a record color, taken from the literal by name so that the
    * file need not list the fields in declaration order. */
  function CheckArgs(vars: Ctx, colors: seq<Color>, fuel: nat, n: string,
                     given: seq<(string, J.JSON)>, fs: ColorFields): M<Args>
    decreases fuel, 4, fs
  {
    match fs
    case CFNil => Success(ANil)
    case CFCons(f, c, rest) =>
      match Lookup(given, f)
      case None => Failure("record literal for " + n + " is missing the field " + f)
      case Some(j) =>
        var e :- CheckExpr(vars, colors, fuel, j, CT(c));
        var restArgs :- CheckArgs(vars, colors, fuel, n, given, rest);
        Success(ACons(f, e, restArgs))
  }

  /** Bidirectional type checking, inferring half. */
  function InferExpr(vars: Ctx, colors: seq<Color>, fuel: nat, j: J.JSON): M<(ExprTy, Expr)>
    decreases fuel, 0
  {
    if fuel == 0 then Failure("expression is nested deeper than the input is long")
    else
      var a :- GetArr(j);
      var h0 :- Idx(a, 0, "expression");
      var hd :- GetStr(h0);
      if hd == "var" then
        var xj :- Idx(a, 1, "variable");
        var x :- GetStr(xj);
        match Lookup(vars, x)
        case None => Failure(x + " is not a variable of the net")
        case Some(t) => Success((t, EVar(x, t)))
      else if hd == "int" then
        var nj :- Idx(a, 1, "integer literal");
        var n :- GetInt(nj);
        Success((CT(CInt), EInt(n)))
      else if hd == "bool" then
        var bj :- Idx(a, 1, "boolean literal");
        var b :- GetBool(bj);
        Success((CT(CBool), EBool(b)))
      else if hd in ["+", "-", "*", "<=", "<"] then
        var xj :- Idx(a, 1, hd);
        var yj :- Idx(a, 2, hd);
        var x :- CheckExpr(vars, colors, fuel - 1, xj, CT(CInt));
        var y :- CheckExpr(vars, colors, fuel - 1, yj, CT(CInt));
        if hd == "+" then Success((CT(CInt), EAdd(x, y)))
        else if hd == "-" then Success((CT(CInt), ESub(x, y)))
        else if hd == "*" then Success((CT(CInt), EMul(x, y)))
        else if hd == "<=" then Success((CT(CBool), ELe(x, y)))
        else Success((CT(CBool), ELt(x, y)))
      else if hd in ["&&", "||"] then
        var xj :- Idx(a, 1, hd);
        var yj :- Idx(a, 2, hd);
        var x :- CheckExpr(vars, colors, fuel - 1, xj, CT(CBool));
        var y :- CheckExpr(vars, colors, fuel - 1, yj, CT(CBool));
        Success((CT(CBool), if hd == "&&" then EAnd(x, y) else EOr(x, y)))
      else if hd == "!" then
        var xj :- Idx(a, 1, "not");
        var x :- CheckExpr(vars, colors, fuel - 1, xj, CT(CBool));
        Success((CT(CBool), ENot(x)))
      else if hd == "=" then
        var xj :- Idx(a, 1, "equality");
        var yj :- Idx(a, 2, "equality");
        var s :- InferExpr(vars, colors, fuel - 1, xj);
        if !s.0.CT? then Failure("equality compares values, not bags or lists")
        else
          var y :- CheckExpr(vars, colors, fuel - 1, yj, s.0);
          Success((CT(CBool), EEq(s.1, y)))
      else if hd == "proj" then
        var ej :- Idx(a, 1, "projection");
        var fj :- Idx(a, 2, "projection");
        var f :- GetStr(fj);
        var s :- InferExpr(vars, colors, fuel - 1, ej);
        if !(s.0.CT? && s.0.c.CRecord?) then
          Failure(f + " is projected out of something that is not a record")
        else
          match FieldColor(s.0.c.fields, f)
          case None => Failure("the record " + s.0.c.name + " has no field " + f)
          case Some(c) => Success((CT(c), EProj(s.1, f)))
      else if hd == "rec" then
        var nj :- Idx(a, 1, "record literal");
        var n :- GetStr(nj);
        match FindColorNamed(colors, n)
        case None => Failure("undeclared color " + n)
        case Some(c) =>
          if !c.CRecord? then Failure(n + " is not a record color")
          else
            var got :- CheckDirected(vars, colors, fuel - 1, j, CT(c));
            match got
            case Some(e) => Success((CT(c), e))
            case None => Failure("malformed record literal for " + n)
      else if hd == "ctor" then
        var idj :- Idx(a, 1, "constructor");
        var id :- GetStr(idj);
        var owners := EnumsWith(colors, id);
        if |owners| == 0 then
          Failure(id + " is not a constructor of any declared enumeration")
        else if |owners| > 1 then
          Failure(id + " is a constructor of more than one enumeration, so its color cannot"
                  + " be inferred here")
        else Success((CT(owners[0]), ECtor(owners[0], id)))
      else if hd == "bag" then
        var itemsj :- Idx(a, 1, "bag literal");
        var items :- GetArr(itemsj);
        if |items| == 0 then
          Failure("an empty bag literal needs a known color; write it where the sort is"
                  + " expected")
        else
          var p :- GetArr(items[0]);
          var ej :- Idx(p, 1, "bag item");
          var s :- InferExpr(vars, colors, fuel - 1, ej);
          if !s.0.CT? then Failure("a bag cannot hold bags or lists")
          else
            var got :- CheckDirected(vars, colors, fuel - 1, j, BT(s.0.c));
            match got
            case Some(e) => Success((BT(s.0.c), e))
            case None => Failure("malformed bag literal")
      else if hd in ["union", "diff"] then
        var xj :- Idx(a, 1, hd);
        var s :- InferExpr(vars, colors, fuel - 1, xj);
        if !s.0.BT? then Failure(hd + " takes bags")
        else
          var got :- CheckDirected(vars, colors, fuel - 1, j, BT(s.0.c));
          match got
          case Some(e) => Success((BT(s.0.c), e))
          case None => Failure("malformed " + hd)
      else if hd == "emptyBag" then
        Failure("the empty bag needs a known color; write it where the sort is expected")
      else Failure("unknown expression form " + hd)
  }

  function FindColorNamed(colors: seq<Color>, n: string): Option<Color>
  {
    if |colors| == 0 then None
    else if SortName(colors[0]) == n then Some(colors[0])
    else FindColorNamed(colors[1..], n)
  }

  function EnumsWith(colors: seq<Color>, id: string): seq<Color>
  {
    if |colors| == 0 then []
    else if colors[0].CEnum? && id in colors[0].ids then
      [colors[0]] + EnumsWith(colors[1..], id)
    else EnumsWith(colors[1..], id)
  }

  // ---------------------------------------------------------------------------------------
  // The net
  // ---------------------------------------------------------------------------------------

  function ResolveAll(decls: seq<(string, J.JSON)>, fuel: nat, names: seq<(string, J.JSON)>):
      M<seq<Color>>
  {
    if |names| == 0 then Success([])
    else
      var c :- ResolveColor(decls, fuel, names[0].0);
      var rest :- ResolveAll(decls, fuel, names[1..]);
      Success([c] + rest)
  }

  function ColorNamed(colors: seq<Color>, n: string): M<Color>
  {
    match FindColorNamed(colors, n)
    case Some(c) => Success(c)
    case None => Failure("undeclared color " + n)
  }

  function ReadVars(colors: seq<Color>, es: seq<(string, J.JSON)>): M<Ctx>
  {
    if |es| == 0 then Success([])
    else
      var _ :- CheckIdent("variable", es[0].0);
      var cn :- GetStr(es[0].1);
      var c :- ColorNamed(colors, cn);
      var rest :- ReadVars(colors, es[1..]);
      Success([(es[0].0, CT(c))] + rest)
  }

  function ReadPlaces(colors: seq<Color>, fuel: nat, es: seq<(string, J.JSON)>):
      M<seq<PlaceDecl>>
  {
    if |es| == 0 then Success([])
    else
      var _ :- CheckIdent("place", es[0].0);
      var cj :- Field(es[0].1, "color");
      var cn :- GetStr(cj);
      var c :- ColorNamed(colors, cn);
      var ij :- Field(es[0].1, "init");
      var init :- CheckExpr([], colors, fuel, ij, BT(c));
      var rest :- ReadPlaces(colors, fuel, es[1..]);
      Success([PlaceDecl(es[0].0, c, init)] + rest)
  }

  function ReadTransitions(vars: Ctx, colors: seq<Color>, fuel: nat,
                           es: seq<(string, J.JSON)>): M<seq<TransDecl>>
  {
    if |es| == 0 then Success([])
    else
      var _ :- CheckIdent("transition", es[0].0);
      var gj :- Field(es[0].1, "guard");
      var g :- CheckExpr(vars, colors, fuel, gj, CT(CBool));
      var rest :- ReadTransitions(vars, colors, fuel, es[1..]);
      Success([TransDecl(es[0].0, g)] + rest)
  }

  function ReadArcs(vars: Ctx, colors: seq<Color>, places: seq<PlaceDecl>, fuel: nat,
                    js: seq<J.JSON>): M<seq<ArcDecl>>
  {
    if |js| == 0 then Success([])
    else
      var pj :- Field(js[0], "place");
      var p :- GetStr(pj);
      var tj :- Field(js[0], "transition");
      var t :- GetStr(tj);
      match FindPlace(places, p)
      case None => Failure("an arc names a place " + p + " that the net does not have")
      case Some(d) =>
        var ej :- Field(js[0], "expr");
        var e :- CheckExpr(vars, colors, fuel, ej, BT(d.pcolor));
        var rest :- ReadArcs(vars, colors, places, fuel, js[1..]);
        Success([ArcDecl(p, t, d.pcolor, e)] + rest)
  }

  /** Read a `Net` from the JSON of `Implementation/docs/InputFormat.md` 4.2.
    *
    * Nothing here checks `Valid`; `NetOfBytes` does that afterwards, so that a failure can name
    * the condition that failed. */
  function NetOfJson(j: J.JSON, fuel: nat): M<Net>
  {
    var colorsj :- Field(j, "colors");
    var colorDecls :- Entries(colorsj);
    var colors :- ResolveAll(colorDecls, |colorDecls| + 1, colorDecls);
    var varsj :- Field(j, "variables");
    var varEntries :- Entries(varsj);
    var vars :- ReadVars(colors, varEntries);
    var placesj :- Field(j, "places");
    var placeEntries :- Entries(placesj);
    var places :- ReadPlaces(colors, fuel, placeEntries);
    var transj :- Field(j, "transitions");
    var transEntries :- Entries(transj);
    var transitions :- ReadTransitions(vars, colors, fuel, transEntries);
    var inj :- Field(j, "inArcs");
    var inArr :- GetArr(inj);
    var inArcs :- ReadArcs(vars, colors, places, fuel, inArr);
    var outj :- Field(j, "outArcs");
    var outArr :- GetArr(outj);
    var outArcs :- ReadArcs(vars, colors, places, fuel, outArr);
    Success(Net(if CBool in colors then colors else colors + [CBool],
                vars, places, transitions, inArcs, outArcs))
  }

  /** The T1 checks that fail, by name, so that a rejection can say what is wrong rather than
    * only that something is.
    *
    * This mirrors `Valid` conjunct for conjunct. It is a convenience for the error message and
    * nothing depends on it: `NetOfBytes` decides `Valid` itself, and that decision is what the
    * core receives. */
  function ExplainInvalid(n: Net): seq<string>
  {
      No(CtorsNoDup(n),
         "two colors declare a constructor of the same name, which mCRL2 refuses")
    + No(PlacesNoDup(n), "two places share a name")
    + No(TransNoDup(n), "two transitions share a name")
    + No(VarsNoDup(n), "two variables share a name")
    + No(NamesDisjoint(n), "a place shares its name with a transition or a variable")
    + No(TransVarsDisjoint(n), "a transition shares its name with a variable")
    + No(BoolMem(n), "Bool is not among the colors")
    + No(ColorMem(n), "a place has an undeclared color")
    + No(VarsAreColors(n), "a variable is not typed by a color")
    + No(VarTypeMem(n), "a variable has an undeclared color")
    + No(InArcPlace(n), "an in-arc expression is not of the color of its place")
    + No(OutArcPlace(n), "an out-arc expression is not of the color of its place")
    + No(InArcTrans(n), "an in-arc names a transition the net does not have")
    + No(OutArcTrans(n), "an out-arc names a transition the net does not have")
    + No(InArcsNoDup(n), "two in-arcs connect the same place and transition")
    + No(OutArcsNoDup(n), "two out-arcs connect the same transition and place")
    + No(InitClosed(n), "an initialization expression is not closed")
    + No(GuardScoped(n), "a guard mentions a variable outside V")
    + No(InArcScoped(n), "an in-arc expression mentions a variable outside V")
    + No(OutArcScoped(n), "an out-arc expression mentions a variable outside V")
    + No(InitTyped(n), "an initialization expression is not a bag of its place's color")
    + No(GuardTyped(n), "a guard is not a boolean expression")
    + No(InArcTyped(n), "an in-arc expression is not a bag of its place's color")
    + No(OutArcTyped(n), "an out-arc expression is not a bag of its place's color")
  }

  function No(b: bool, msg: string): seq<string>
  {
    if b then [] else [msg]
  }

  /** Read a CPN from the bytes of a native CPN file, validated.
    *
    * The `Valid(n)` in the postcondition is what the core runs on: from here inwards the T1
    * checks of `Implementation/docs/InputFormat.md` 4.3 are hypotheses, not assumptions. */
  function NetOfBytes(bs: seq<bv8>): (r: M<Net>)
    ensures r.Success? ==> Valid(r.value)
  {
    var j :- MapFailure(API.Deserialize(BytesOfBv(bs)));
    var n :- NetOfJson(j, 4 * |bs| + 16);
    if Valid(n) then Success(n)
    else Failure("the input is not a CPN:\n  - " + Join("\n  - ", ExplainInvalid(n)))
  }

  function MapFailure<T, E>(r: Result<T, E>): M<T>
  {
    match r
    case Success(v) => Success(v)
    case Failure(_) => Failure("the input is not well-formed JSON")
  }

  /** `Std.FileIO` hands back `bv8` and `Std.JSON` wants `uint8`; the two are the same byte
    * under two of Dafny's numeric types. */
  function BytesOfBv(bs: seq<bv8>): seq<uint8>
  {
    if |bs| == 0 then [] else [bs[0] as int as uint8] + BytesOfBv(bs[1..])
  }
}
