/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Type soundness
 *
 * `SortOf` of `src/Expr.dfy` decides whether a term has a sort. That is a statement about the
 * *term*, and so far nothing connects it to the value the term evaluates to: `Eval` has cases
 * that a well-sorted term cannot reach -- `AsInt` of something that is not an integer, and the
 * projection of a field a record value does not carry, which falls back on `VBool(false)`.
 *
 * This file closes that. `EvalWf` says that under an environment well-typed on the term's free
 * variables, a term of sort `t` evaluates to a denotation of sort `t`, so the fallbacks are
 * never reached and `AsInt`, `AsBool` and `AsRecord` always read a denotation that is really of
 * that shape.
 *
 * Nothing in `src/Correct.dfy` depends on it. The T2 theorems compare two uses of the same
 * `Eval`, so junk on one side is junk on the other and the identity holds either way. What this
 * adds is the reason to believe `Eval` is the semantics it is meant to be, rather than a
 * function that happens to satisfy an equation.
 *
 * ## Where the extrinsic typing is actually paid for
 *
 * `Cpn2mCrl2/Typing.lean` proves the same statement, and the two proofs are the same length.
 * The difference is in what each case has to *do*. In Lean the sort of a subterm is the index
 * of its type, so it arrives with the term; here each case has to take `SortOf(e)` apart to
 * learn the sorts of the operands, and the closure properties of the bag operations -- that a
 * union of two well-typed bags is well-typed, that a difference of a well-typed bag is --
 * have to be proved separately in `src/Bag.dfy` rather than being read off an index. That is
 * six short lemmas, and it is the whole of the cost `Implementation/docs/Languages.md` 3
 * expects from having no dependent types.
 *
 * ## Main results
 *
 * * `EvalWf` : evaluation preserves sorts.
 */
module Typing {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag
  import opened ListOps
  import opened Expr

  /** Under an environment well-typed on its free variables, a term of sort `t` evaluates to a
    * denotation of sort `t`.
    *
    * The hypothesis is `EnvWfOn(FreeVars(e), env)` rather than well-typedness at every sort and
    * name, because the latter is too strong to be satisfiable: `Env` is total, and an
    * enumeration with no constructors has no value for a junk environment to hold. A binding of
    * Definition 2 gives exactly this form. */
  lemma EvalWf(e: Expr, env: Env, t: ExprTy)
    requires WellTyped(e, t)
    requires EnvWfOn(FreeVars(e), env)
    ensures DenotHasSort(Eval(e, env), t)
    decreases e, 1
  {
    match e
    case EVar(x, t0) =>
      assert (x, t0) in FreeVars(e);
    case EInt(_) =>
    case EBool(_) =>
    case ECtor(_, _) =>
    case EMkRec(c, args) =>
      ArgsEvalWf(args, env, c.fields);
    case EProj(e0, f) =>
      var s0 := SortOf(e0);
      assert s0.Some? && s0.value.CT? && s0.value.c.CRecord?;
      var fs := s0.value.c.fields;
      EvalWf(e0, env, s0.value);
      var d0 := Eval(e0, env);
      assert d0.DVal? && ValueOfColor(d0.v, s0.value.c);
      ValueIsRecord(d0.v, s0.value.c.name, fs);
      assert AsRecord(d0) == d0.v.vfields;
      FieldValueOfColorFields(d0.v.vfields, fs, f, t.c);
    case EAdd(_, _) =>
    case ESub(_, _) =>
    case EMul(_, _) =>
    case EEq(_, _) =>
    case ELe(_, _) =>
    case ELt(_, _) =>
    case EAnd(_, _) =>
    case EOr(_, _) =>
    case ENot(_) =>
    case EBagSubset(_, _) =>
    case ESubList(_, _) =>
    case EEmptyBag(c) =>
      BagOfColorEmpty(c);
    case ENilList(_) =>
    case ESingle(k, e0) =>
      EvalWf(e0, env, CT(t.c));
      BagOfColorSingle(k, AsValue(Eval(e0, env)), t.c);
    case EBagUnion(a, b) =>
      EvalWf(a, env, BT(t.c));
      EvalWf(b, env, BT(t.c));
      BagOfColorUnion(AsBag(Eval(a, env)), AsBag(Eval(b, env)), t.c);
    case EBagDiff(a, b) =>
      EvalWf(a, env, BT(t.c));
      BagOfColorDiff(AsBag(Eval(a, env)), AsBag(Eval(b, env)), t.c);
    case ESnoc(l, e0) =>
      EvalWf(l, env, LT(t.c));
      EvalWf(e0, env, CT(t.c));
      SeqOfColorAppend(AsSeq(Eval(l, env)), [AsValue(Eval(e0, env))], t.c);
    case EAppendList(a, b) =>
      EvalWf(a, env, LT(t.c));
      EvalWf(b, env, LT(t.c));
      SeqOfColorAppend(AsSeq(Eval(a, env)), AsSeq(Eval(b, env)), t.c);
    case EDiffList(a, b) =>
      EvalWf(a, env, LT(t.c));
      var la := AsSeq(Eval(a, env));
      var lb := AsSeq(Eval(b, env));
      SeqOfColorMem(la, t.c);
      forall v | v in ListDiff(la, lb) ensures ValueOfColor(v, t.c) {
        MemOfMemListDiff(la, lb, v);
      }
      SeqOfColorMem(ListDiff(la, lb), t.c);
  }

  lemma ArgsEvalWf(args: Args, env: Env, fs: ColorFields)
    requires ArgsMatch(args, fs)
    requires EnvWfOn(ArgsFreeVars(args), env)
    ensures ValueFieldsOfColorFields(EvalArgs(args, env), fs)
    decreases args, 0
  {
    match (args, fs)
    case (ANil, CFNil) =>
    case (ACons(n, e, rest), CFCons(_, c, frest)) =>
      EvalWf(e, env, CT(c));
      ArgsEvalWf(rest, env, frest);
  }
}
