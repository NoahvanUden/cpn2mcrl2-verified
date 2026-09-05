/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # The expression language
 *
 * `EXPR` of Chapter 2, fixed concretely by `Implementation/docs/InputFormat.md` 4.1, plus the
 * two things Definition 14 needs that a CPN file never contains: bag inclusion, and variables
 * of bag sort.
 *
 * ## The one structural difference from the Lean translator
 *
 * `Cpn2mCrl2/Expr.lean` makes `Expr` an inductive *family* indexed by `ExprTy`, so that a
 * guard is a boolean expression and an arc expression is a bag expression by construction, and
 * checks 4 to 6 of `Implementation/docs/InputFormat.md` 4.3 hold for every term that exists.
 * Dafny has no dependent types, so that is not available. Here `Expr` is one flat datatype and
 * `SortOf` is a total inference function into `Option<ExprTy>`; `WellTyped(e, t)` is
 * `SortOf(e) == Some(t)`, and the three checks become *hypotheses* -- fields of `Net.Valid` in
 * `src/Net.dfy` -- rather than consequences of a term existing.
 *
 * This is the difference `Implementation/docs/Languages.md` 3 predicts when it says Dafny will
 * hurt on C4, and it is worth being precise about where the cost actually lands. It is not in
 * the translation: `src/Translate.dfy` assembles terms without ever needing a typing
 * derivation, exactly as the Lean does. It is not in obligation 4 either, for the reason
 * below. It lands in two narrower places: `Net.Valid` grows the well-typedness conjuncts that
 * Lean gets free, and `src/Typing.dfy` has to prove that a `SortOf` derivation is preserved by
 * `Eval`, where in Lean the corresponding statement is about `Value` alone.
 *
 * `SortOf` is context-free, because a variable carries its own sort -- which is what the Lean
 * does too. So inference needs no environment and `WellTyped` is a property of a term rather
 * than of a term-in-a-context.
 *
 * ## Typing is inferred, scoping is separate
 *
 * As in Lean, and this is the decision that makes obligation 4 of
 * `Implementation/docs/Plan.md` 4 cheap. Variables carry their name and sort and nothing else;
 * `FreeVars` reports which they are, and being in scope is the separate predicate `ScopedIn`,
 * which is check 7. Definition 14 builds terms in a *different* context from the one a CPN's
 * expressions live in -- one place parameter per place together with `Var(t)` -- and with
 * scoping extrinsic the translation moves a term between contexts by doing nothing to it at
 * all. Obligation 4 is then `EvalCongr` below: the value of an expression depends only on its
 * free variables, by one structural induction.
 *
 * ## Evaluation is ghost
 *
 * `Eval` is a `ghost function`, and so is everything built on it. The translator computes
 * terms and prints them; it never evaluates one. Marking that in the language rather than in a
 * comment is worth doing, because it is exactly the line `Implementation/docs/Plan.md` 2 draws
 * between the program and the theorems about it: `Eval` exists so that T2 has something to be
 * about.
 *
 * ## Main definitions
 *
 * * `Expr`, `SortOf`, `WellTyped` : `EXPR`, with typing inferred rather than intrinsic.
 * * `Eval` : evaluation under a binding, the thesis's `e<b>`.
 * * `FreeVars`, `ScopedIn` : `VAR[e]`, and check 7 of `InputFormat.md` 4.3.
 * * `EvalCongr` : obligation 4 of `Plan.md` 4.
 */
module Expr {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag
  import opened ListOps

  /** The type of an expression: a color `c`, the bag of a color -- written `c_MS` in the
    * thesis -- or the *list* of a color.
    *
    * The first two are the constructors of `Proof/CommonDefinitions.lean`'s `ExprTy`,
    * unchanged. `Thesis/docs/LeanFormalization.md` 5.1 predicts a third, a product former,
    * because `D` and `H_t` of Definition 13 are tuple-sorted; it is not needed here, for the
    * reason `src/Lpe.dfy` gives. The third constructor below is not that one: `LT` is not part
    * of any CPN and exists only for the list backend of `src/ListEncoding.dfy`. */
  datatype ExprTy = CT(c: Color) | BT(c: Color) | LT(c: Color)

  /** A typing context: the variables in scope, with their sorts. `V` of Definition 5 together
    * with `Type[.]` is one of these, in which every entry is a `CT`. */
  type Ctx = seq<(string, ExprTy)>

  /** Whether a sort is a color rather than a bag or a list.
    *
    * Definition 5 types every variable of `V` by a color; `Net.Valid` says so with this rather
    * than with an existential over `Color`, because the importer has to be able to check it. */
  predicate IsColorSort(t: ExprTy)
  {
    t.CT?
  }

  /** One expression per field of a record color, in declaration order, each tagged with the
    * field name. */
  datatype Args = ANil | ACons(aname: string, ae: Expr, arest: Args)

  /** `EXPR` of `Implementation/docs/InputFormat.md` 4.1.
    *
    * Four constructors depart from that grammar and are worth naming.
    *
    * `EVar` may have bag sort. A CPN file never produces one; Definition 14's place parameters
    * are the only bag-sorted variables that occur, and `src/Net.dfy` records that a net's own
    * variables are all color-sorted.
    *
    * `EBagSubset` is the operation Definition 14 uses and a CPN never contains. It is here so
    * that *one* language serves both as the annotation language of a CPN and as the mCRL2 data
    * language the translation emits into, which is obligation 2 of
    * `Implementation/docs/Plan.md` 4. `src/Import.dfy` does not parse it.
    *
    * `ESingle` replaces the grammar's `bag([(n, e), ...])`. A bag literal with several items is
    * the union of its singletons, which is how Definition 1 builds it anyway.
    *
    * The five list constructors are not part of any CPN either; `src/ListEncoding.dfy` is what
    * they are for. */
  datatype Expr =
    | EVar(x: string, ty: ExprTy)
    | EInt(n: int)
    | EBool(bv: bool)
    | ECtor(ec: Color, id: string)
    | EMkRec(rc: Color, args: Args)
    | EProj(e: Expr, f: string)
    | EAdd(a: Expr, b: Expr)
    | ESub(a: Expr, b: Expr)
    | EMul(a: Expr, b: Expr)
    | EEq(a: Expr, b: Expr)
    | ELe(a: Expr, b: Expr)
    | ELt(a: Expr, b: Expr)
    | EAnd(a: Expr, b: Expr)
    | EOr(a: Expr, b: Expr)
    | ENot(a: Expr)
    | EEmptyBag(bc: Color)
    | ESingle(k: nat, e: Expr)
    | EBagUnion(a: Expr, b: Expr)
    | EBagDiff(a: Expr, b: Expr)
    | EBagSubset(a: Expr, b: Expr)
    | ENilList(bc: Color)
    | ESnoc(a: Expr, b: Expr)
    | EAppendList(a: Expr, b: Expr)
    | EDiffList(a: Expr, b: Expr)
    | ESubList(a: Expr, b: Expr)

  // ---------------------------------------------------------------------------------------
  // Sort inference
  // ---------------------------------------------------------------------------------------

  /** The sort of an expression, or `None` when it has none.
    *
    * This is the whole of checks 4 to 6 of `Implementation/docs/InputFormat.md` 4.3, as one
    * total function. In Lean the same content is the *index* of `Expr` and there is nothing to
    * compute; here it is computed once, by the importer, and then carried as a hypothesis. */
  function SortOf(e: Expr): Option<ExprTy>
    decreases e, 1
  {
    match e
    case EVar(_, t) => Some(t)
    case EInt(_) => Some(CT(CInt))
    case EBool(_) => Some(CT(CBool))
    case ECtor(c, id) => if c.CEnum? && id in c.ids then Some(CT(c)) else None
    case EMkRec(c, args) =>
      if c.CRecord? && ArgsMatch(args, c.fields) then Some(CT(c)) else None
    case EProj(e0, f) =>
      (match SortOf(e0)
       case Some(CT(CRecord(_, fs))) =>
         (match FieldColor(fs, f) case Some(c) => Some(CT(c)) case None => None)
       case _ => None)
    case EAdd(a, b) => IntPair(SortOf(a), SortOf(b), CT(CInt))
    case ESub(a, b) => IntPair(SortOf(a), SortOf(b), CT(CInt))
    case EMul(a, b) => IntPair(SortOf(a), SortOf(b), CT(CInt))
    case ELe(a, b) => IntPair(SortOf(a), SortOf(b), CT(CBool))
    case ELt(a, b) => IntPair(SortOf(a), SortOf(b), CT(CBool))
    case EEq(a, b) => SameColorPair(SortOf(a), SortOf(b))
    case EAnd(a, b) => BoolPair(SortOf(a), SortOf(b))
    case EOr(a, b) => BoolPair(SortOf(a), SortOf(b))
    case ENot(a) => if SortOf(a) == Some(CT(CBool)) then Some(CT(CBool)) else None
    case EEmptyBag(c) => Some(BT(c))
    case ESingle(_, e0) =>
      (match SortOf(e0) case Some(CT(c)) => Some(BT(c)) case _ => None)
    case EBagUnion(a, b) => BagPair(SortOf(a), SortOf(b), true)
    case EBagDiff(a, b) => BagPair(SortOf(a), SortOf(b), true)
    case EBagSubset(a, b) => BagPair(SortOf(a), SortOf(b), false)
    case ENilList(c) => Some(LT(c))
    case ESnoc(l, e0) => SnocPair(SortOf(l), SortOf(e0))
    case EAppendList(a, b) => ListPair(SortOf(a), SortOf(b), true)
    case EDiffList(a, b) => ListPair(SortOf(a), SortOf(b), true)
    case ESubList(a, b) => ListPair(SortOf(a), SortOf(b), false)
  }

  /* The five helpers below take the *sorts* of the operands rather than the operands, so that
     they need no recursion of their own and so stay out of `SortOf`'s termination argument.
     Dafny orders the components of a datatype below the datatype but gives a freshly built
     `EAdd(a, b)` no relation to the `ESub(a, b)` a caller was matching on, so a helper phrased
     over expressions would need one `decreases` witness per operator. */

  function IntPair(sa: Option<ExprTy>, sb: Option<ExprTy>, result: ExprTy): Option<ExprTy>
  {
    if sa == Some(CT(CInt)) && sb == Some(CT(CInt)) then Some(result) else None
  }

  function BoolPair(sa: Option<ExprTy>, sb: Option<ExprTy>): Option<ExprTy>
  {
    if sa == Some(CT(CBool)) && sb == Some(CT(CBool)) then Some(CT(CBool)) else None
  }

  function SameColorPair(sa: Option<ExprTy>, sb: Option<ExprTy>): Option<ExprTy>
  {
    match (sa, sb)
    case (Some(CT(c1)), Some(CT(c2))) => (if c1 == c2 then Some(CT(CBool)) else None)
    case _ => None
  }

  /** The sort of a binary bag operation: `same` says whether the result is the bag sort itself
    * (union, difference) or `Bool` (inclusion). */
  function BagPair(sa: Option<ExprTy>, sb: Option<ExprTy>, same: bool): Option<ExprTy>
  {
    match (sa, sb)
    case (Some(BT(c1)), Some(BT(c2))) =>
      (if c1 == c2 then Some(if same then BT(c1) else CT(CBool)) else None)
    case _ => None
  }

  function ListPair(sa: Option<ExprTy>, sb: Option<ExprTy>, same: bool): Option<ExprTy>
  {
    match (sa, sb)
    case (Some(LT(c1)), Some(LT(c2))) =>
      (if c1 == c2 then Some(if same then LT(c1) else CT(CBool)) else None)
    case _ => None
  }

  function SnocPair(sl: Option<ExprTy>, se: Option<ExprTy>): Option<ExprTy>
  {
    match (sl, se)
    case (Some(LT(c1)), Some(CT(c2))) => (if c1 == c2 then Some(LT(c1)) else None)
    case _ => None
  }

  /** The arguments of a record literal line up with the fields of its color: same names, same
    * order, each of the declared sort. */
  predicate ArgsMatch(args: Args, fs: ColorFields)
    decreases args, 0
  {
    match (args, fs)
    case (ANil, CFNil) => true
    case (ACons(n, e, rest), CFCons(n', c, frest)) =>
      n == n' && SortOf(e) == Some(CT(c)) && ArgsMatch(rest, frest)
    case _ => false
  }

  /** `e` has sort `t`. The form every hypothesis in `src/Net.dfy` is stated in. */
  predicate WellTyped(e: Expr, t: ExprTy)
  {
    SortOf(e) == Some(t)
  }

  // ---------------------------------------------------------------------------------------
  // Values, environments
  // ---------------------------------------------------------------------------------------

  /** What an expression evaluates to: a value, a bag of values, or a list of values.
    *
    * `Cpn2mCrl2/Expr.lean` has `ExprTy.Denot`, a *function* from the sort to the type of its
    * values, so that `eval` returns a `Value` at color sort and a `Bag` at bag sort. Without
    * dependent types the three collapse into one datatype and the sort discipline moves into
    * `DenotHasSort`. */
  datatype Denot = DVal(v: Value) | DBag(m: Bag) | DList(l: seq<Value>)

  predicate SeqOfColor(l: seq<Value>, c: Color)
  {
    |l| == 0 || (ValueOfColor(l[0], c) && SeqOfColor(l[1..], c))
  }

  lemma SeqOfColorMem(l: seq<Value>, c: Color)
    ensures SeqOfColor(l, c) <==> forall v :: v in l ==> ValueOfColor(v, c)
  {
    if |l| != 0 {
      SeqOfColorMem(l[1..], c);
      assert forall v :: v in l <==> (v == l[0] || v in l[1..]);
    }
  }

  lemma SeqOfColorAppend(a: seq<Value>, b: seq<Value>, c: Color)
    ensures SeqOfColor(a + b, c) <==> (SeqOfColor(a, c) && SeqOfColor(b, c))
  {
    SeqOfColorMem(a, c);
    SeqOfColorMem(b, c);
    SeqOfColorMem(a + b, c);
    assert forall v :: v in a + b <==> (v in a || v in b);
  }

  /** A denotation of the right shape for the sort `t`. */
  predicate DenotHasSort(d: Denot, t: ExprTy)
  {
    match t
    case CT(c) => d.DVal? && ValueOfColor(d.v, c)
    case BT(c) => d.DBag? && BagOfColor(d.m, c)
    case LT(c) => d.DList? && SeqOfColor(d.l, c)
  }

  /** A binding: a denotation for every sort and name.
    *
    * Definition 2's `B[V]` is the restriction of this to the variables of `V`; `EvalCongr` says
    * an expression cannot tell the difference between two environments that agree on its free
    * variables, which is what makes the restriction harmless. */
  type Env = (ExprTy, string) -> Denot

  /** The environment binding every variable to junk. */
  ghost function JunkEnv(): Env
  {
    (t: ExprTy, x: string) =>
      match t
      case CT(c) => DVal(Junk(c))
      case BT(_) => DBag(EmptyBag())
      case LT(_) => DList([])
  }

  /** An environment is well-typed *on `G`* when every variable of `G` holds a denotation of
    * the sort `G` gives it.
    *
    * This, and not well-typedness at every sort and name, is Definition 2's `B[V]`: a binding
    * assigns a value of `Type[v]` to each `v in V` and says nothing about anything else. It is
    * also the only form that is usable, because `Env` is total and an enumeration with no
    * constructors has no value at all for a junk environment to hold. */
  ghost predicate EnvWfOn(g: Ctx, env: Env)
  {
    forall q :: q in g ==> DenotHasSort(env(q.1, q.0), q.1)
  }

  lemma EnvWfOnMono(g: Ctx, d: Ctx, env: Env)
    requires forall q :: q in g ==> q in d
    requires EnvWfOn(d, env)
    ensures EnvWfOn(g, env)
  {
  }

  // ---------------------------------------------------------------------------------------
  // Reading a denotation at a shape
  //
  // `Denot` is untyped, so evaluation of `1 + e` has to do something when `e` is not an
  // integer. These give the value a well-typed environment guarantees, and junk otherwise.
  // ---------------------------------------------------------------------------------------

  function AsInt(d: Denot): int
  {
    if d.DVal? && d.v.VInt? then d.v.i else 0
  }

  function AsBool(d: Denot): bool
  {
    if d.DVal? && d.v.VBool? then d.v.b else false
  }

  function AsRecord(d: Denot): ValueFields
  {
    if d.DVal? && d.v.VRecord? then d.v.vfields else VFNil
  }

  function AsBag(d: Denot): Bag
  {
    if d.DBag? then d.m else EmptyBag()
  }

  function AsSeq(d: Denot): seq<Value>
  {
    if d.DList? then d.l else []
  }

  // ---------------------------------------------------------------------------------------
  // Evaluation
  // ---------------------------------------------------------------------------------------

  /** The value of an expression under a binding, written `e<b>` in the thesis. */
  ghost function Eval(e: Expr, env: Env): Denot
    decreases e, 1
  {
    match e
    case EVar(x, t) => env(t, x)
    case EInt(n) => DVal(VInt(n))
    case EBool(b) => DVal(VBool(b))
    case ECtor(_, id) => DVal(VCtor(id))
    case EMkRec(_, args) => DVal(VRecord(EvalArgs(args, env)))
    case EProj(e0, f) =>
      var got := FieldValue(AsRecord(Eval(e0, env)), f);
      DVal(if got.Some? then got.value else VBool(false))
    case EAdd(a, b) => DVal(VInt(AsInt(Eval(a, env)) + AsInt(Eval(b, env))))
    case ESub(a, b) => DVal(VInt(AsInt(Eval(a, env)) - AsInt(Eval(b, env))))
    case EMul(a, b) => DVal(VInt(AsInt(Eval(a, env)) * AsInt(Eval(b, env))))
    case EEq(a, b) => DVal(VBool(Eval(a, env) == Eval(b, env)))
    case ELe(a, b) => DVal(VBool(AsInt(Eval(a, env)) <= AsInt(Eval(b, env))))
    case ELt(a, b) => DVal(VBool(AsInt(Eval(a, env)) < AsInt(Eval(b, env))))
    case EAnd(a, b) => DVal(VBool(AsBool(Eval(a, env)) && AsBool(Eval(b, env))))
    case EOr(a, b) => DVal(VBool(AsBool(Eval(a, env)) || AsBool(Eval(b, env))))
    case ENot(a) => DVal(VBool(!AsBool(Eval(a, env))))
    case EEmptyBag(_) => DBag(EmptyBag())
    case ESingle(k, e0) => DBag(Single(k, AsValue(Eval(e0, env))))
    case EBagUnion(a, b) => DBag(Union(AsBag(Eval(a, env)), AsBag(Eval(b, env))))
    case EBagDiff(a, b) => DBag(Diff(AsBag(Eval(a, env)), AsBag(Eval(b, env))))
    case EBagSubset(a, b) => DVal(VBool(SubsetB(AsBag(Eval(a, env)), AsBag(Eval(b, env)))))
    case ENilList(_) => DList([])
    case ESnoc(l, e0) => DList(AsSeq(Eval(l, env)) + [AsValue(Eval(e0, env))])
    case EAppendList(a, b) => DList(AsSeq(Eval(a, env)) + AsSeq(Eval(b, env)))
    case EDiffList(a, b) => DList(ListDiff(AsSeq(Eval(a, env)), AsSeq(Eval(b, env))))
    case ESubList(a, b) => DVal(VBool(SubMultiset(AsSeq(Eval(a, env)), AsSeq(Eval(b, env)))))
  }

  /** `Eval`, one record field at a time. */
  ghost function EvalArgs(args: Args, env: Env): ValueFields
    decreases args, 0
  {
    match args
    case ANil => VFNil
    case ACons(n, e, rest) => VFCons(n, AsValue(Eval(e, env)), EvalArgs(rest, env))
  }

  function AsValue(d: Denot): Value
  {
    if d.DVal? then d.v else VBool(false)
  }

  /** A boolean expression holds under a binding. This is `Type[e] = Bool` together with
    * `e<b> = True`, as Definitions 6 and 14 use it. */
  ghost predicate Holds(e: Expr, env: Env)
  {
    AsBool(Eval(e, env))
  }

  // ---------------------------------------------------------------------------------------
  // Free variables
  //
  // `VAR[e]` of Chapter 2. The sequence may repeat a variable; only membership is ever used.
  // ---------------------------------------------------------------------------------------

  /** The variables occurring in an expression, with their sorts. */
  function FreeVars(e: Expr): Ctx
    decreases e, 1
  {
    match e
    case EVar(x, t) => [(x, t)]
    case EInt(_) => []
    case EBool(_) => []
    case ECtor(_, _) => []
    case EMkRec(_, args) => ArgsFreeVars(args)
    case EProj(e0, _) => FreeVars(e0)
    case EAdd(a, b) => FreeVars(a) + FreeVars(b)
    case ESub(a, b) => FreeVars(a) + FreeVars(b)
    case EMul(a, b) => FreeVars(a) + FreeVars(b)
    case EEq(a, b) => FreeVars(a) + FreeVars(b)
    case ELe(a, b) => FreeVars(a) + FreeVars(b)
    case ELt(a, b) => FreeVars(a) + FreeVars(b)
    case EAnd(a, b) => FreeVars(a) + FreeVars(b)
    case EOr(a, b) => FreeVars(a) + FreeVars(b)
    case ENot(a) => FreeVars(a)
    case EEmptyBag(_) => []
    case ESingle(_, e0) => FreeVars(e0)
    case EBagUnion(a, b) => FreeVars(a) + FreeVars(b)
    case EBagDiff(a, b) => FreeVars(a) + FreeVars(b)
    case EBagSubset(a, b) => FreeVars(a) + FreeVars(b)
    case ENilList(_) => []
    case ESnoc(a, b) => FreeVars(a) + FreeVars(b)
    case EAppendList(a, b) => FreeVars(a) + FreeVars(b)
    case EDiffList(a, b) => FreeVars(a) + FreeVars(b)
    case ESubList(a, b) => FreeVars(a) + FreeVars(b)
  }

  function ArgsFreeVars(args: Args): Ctx
    decreases args, 0
  {
    match args
    case ANil => []
    case ACons(_, e, rest) => FreeVars(e) + ArgsFreeVars(rest)
  }

  /** An expression is scoped in `g` when every variable it mentions is a variable of `g` at the
    * sort `g` gives it.
    *
    * This is check 7 of `Implementation/docs/InputFormat.md` 4.3, `Var(t) subseteq V`, which
    * `Thesis/docs/LeanFormalization.md` 4.6 records as provable from the typing but not stated
    * in `Proof/`. Here it is neither: it is checked at the boundary and then used. */
  predicate ScopedIn(g: Ctx, e: Expr)
  {
    forall q :: q in FreeVars(e) ==> q in g
  }

  lemma ScopedInMono(g: Ctx, d: Ctx, e: Expr)
    requires forall q :: q in g ==> q in d
    requires ScopedIn(g, e)
    ensures ScopedIn(d, e)
  {
  }

  // ---------------------------------------------------------------------------------------
  // Obligation 4: an expression sees only its free variables
  //
  // `Implementation/docs/Plan.md` 4 obligation 4 asks for the lemma relating "`E(p,t)`
  // evaluated under a binding `b` of the transition" to "the translated term evaluated under
  // `d |-> M` and `h |-> b`". Because the translation moves an expression between contexts
  // without changing it, that lemma is exactly this congruence.
  //
  // `Thesis/docs/LeanFormalization.md` 5.1 calls it "the one genuinely new proof obligation"
  // and `Plan.md` 7 rates it the project's high risk. In Lean it was one structural induction
  // with no casts; in Dafny it is the same induction, and the SMT solver closes every case
  // without a hint. Neither language pays what the plan expected, and for the same reason:
  // scoping is extrinsic on both sides.
  // ---------------------------------------------------------------------------------------

  /** Two environments agreeing on the free variables of `e` give it the same value. */
  lemma EvalCongr(e: Expr, env1: Env, env2: Env)
    requires forall q :: q in FreeVars(e) ==> env1(q.1, q.0) == env2(q.1, q.0)
    ensures Eval(e, env1) == Eval(e, env2)
    decreases e, 1
  {
    match e
    case EVar(x, t) => assert (x, t) in FreeVars(e);
    case EInt(_) =>
    case EBool(_) =>
    case ECtor(_, _) =>
    case EMkRec(_, args) => ArgsEvalCongr(args, env1, env2);
    case EProj(e0, _) => EvalCongr(e0, env1, env2);
    case ENot(a) => EvalCongr(a, env1, env2);
    case ESingle(_, e0) => EvalCongr(e0, env1, env2);
    case EEmptyBag(_) =>
    case ENilList(_) =>
    case EAdd(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case ESub(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EMul(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EEq(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case ELe(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case ELt(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EAnd(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EOr(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EBagUnion(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EBagDiff(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EBagSubset(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case ESnoc(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EAppendList(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case EDiffList(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
    case ESubList(a, b) => EvalCongr(a, env1, env2); EvalCongr(b, env1, env2);
  }

  lemma ArgsEvalCongr(args: Args, env1: Env, env2: Env)
    requires forall q :: q in ArgsFreeVars(args) ==> env1(q.1, q.0) == env2(q.1, q.0)
    ensures EvalArgs(args, env1) == EvalArgs(args, env2)
    decreases args, 0
  {
    match args
    case ANil =>
    case ACons(_, e, rest) =>
      EvalCongr(e, env1, env2);
      ArgsEvalCongr(rest, env1, env2);
  }

  /** The form obligation 4 is used in: an expression scoped in `g` is evaluated the same by any
    * two environments that agree on `g`. */
  lemma EvalCongrScoped(g: Ctx, e: Expr, env1: Env, env2: Env)
    requires ScopedIn(g, e)
    requires forall q :: q in g ==> env1(q.1, q.0) == env2(q.1, q.0)
    ensures Eval(e, env1) == Eval(e, env2)
  {
    EvalCongr(e, env1, env2);
  }

  // ---------------------------------------------------------------------------------------
  // Folds
  // ---------------------------------------------------------------------------------------

  /** The conjunction of a sequence of boolean expressions, which is how the bounded
    * `forall p in pre(t)` of Definition 14 is emitted: obligation 3 of
    * `Implementation/docs/Plan.md` 4 unfolds it at translation time, so the data language needs
    * no quantifier. */
  function AndAll(es: seq<Expr>): Expr
  {
    if |es| == 0 then EBool(true)
    else if |es| == 1 then es[0]
    else EAnd(es[0], AndAll(es[1..]))
  }

  /** `AndAll` holds exactly when every conjunct does. */
  lemma HoldsAndAll(es: seq<Expr>, env: Env)
    ensures Holds(AndAll(es), env) <==> forall e :: e in es ==> Holds(e, env)
  {
    if |es| > 1 {
      assert forall e :: e in es <==> (e == es[0] || e in es[1..]);
      HoldsAndAll(es[1..], env);
      assert AndAll(es) == EAnd(es[0], AndAll(es[1..]));
      assert Holds(AndAll(es), env) <==> (Holds(es[0], env) && Holds(AndAll(es[1..]), env));
    } else if |es| == 1 {
      assert es == [es[0]];
    }
  }

  /** `AndAll` of well-typed conjuncts is well-typed, which is what lets `src/Print.dfy` emit
    * it and `src/Net.dfy` state the condition's sort. */
  lemma SortOfAndAll(es: seq<Expr>)
    requires forall e :: e in es ==> WellTyped(e, CT(CBool))
    ensures WellTyped(AndAll(es), CT(CBool))
  {
    if |es| > 1 {
      assert forall e :: e in es[1..] ==> e in es;
      SortOfAndAll(es[1..]);
      assert es[0] in es;
      assert AndAll(es) == EAnd(es[0], AndAll(es[1..]));
    } else if |es| == 1 {
      assert es[0] in es;
    }
  }

  lemma ScopedInAndAll(g: Ctx, es: seq<Expr>)
    requires forall e :: e in es ==> ScopedIn(g, e)
    ensures ScopedIn(g, AndAll(es))
  {
    if |es| > 1 {
      assert forall e :: e in es[1..] ==> e in es;
      ScopedInAndAll(g, es[1..]);
      assert es[0] in es;
      assert AndAll(es) == EAnd(es[0], AndAll(es[1..]));
      assert FreeVars(AndAll(es)) == FreeVars(es[0]) + FreeVars(AndAll(es[1..]));
    } else if |es| == 1 {
      assert es[0] in es;
    }
  }

  /** The union of a sequence of bag expressions. */
  function UnionAll(c: Color, es: seq<Expr>): Expr
  {
    if |es| == 0 then EEmptyBag(c)
    else if |es| == 1 then es[0]
    else EBagUnion(es[0], UnionAll(c, es[1..]))
  }

  lemma SortOfUnionAll(c: Color, es: seq<Expr>)
    requires forall e :: e in es ==> WellTyped(e, BT(c))
    ensures WellTyped(UnionAll(c, es), BT(c))
  {
    if |es| > 1 {
      assert forall e :: e in es[1..] ==> e in es;
      SortOfUnionAll(c, es[1..]);
      assert es[0] in es;
      assert UnionAll(c, es) == EBagUnion(es[0], UnionAll(c, es[1..]));
    } else if |es| == 1 {
      assert es[0] in es;
    }
  }

  lemma FreeVarsUnionAll(c: Color, es: seq<Expr>, q: (string, ExprTy))
    requires q in FreeVars(UnionAll(c, es))
    ensures exists e :: e in es && q in FreeVars(e)
  {
    if |es| > 1 {
      if q !in FreeVars(es[0]) {
        FreeVarsUnionAll(c, es[1..], q);
        var e :| e in es[1..] && q in FreeVars(e);
        assert e in es;
      }
    }
  }
}
