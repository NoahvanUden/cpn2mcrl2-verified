/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Colors and values
 *
 * The color universe `Sigma` of Definition 5, fixed concretely, and the values that inhabit
 * it. `Implementation/docs/InputFormat.md` 4.1 fixes the grammar:
 *
 *     color ::= Bool | Int | enum(name, [id, ...]) | record(name, [(field, color), ...])
 *
 * ## Why the fields are a cons list and not a `seq`
 *
 * `Cpn2mCrl2/Color.lean` splits the fields of a record into a separate `ColorFields`
 * inductive because Lean derives neither `DecidableEq` nor a usable recursor for the nested
 * inductive `List (String x Color)`. Dafny has the opposite half of that problem and it lands
 * in the same place. Equality is free -- `seq<(string, Color)>` has structural equality
 * without a deriving clause -- but *termination* is not: Dafny gives the elements of a bare
 * `seq` no rank below the sequence, so a function recursing from `fs` into `fs[0].1` is
 * rejected, and only a function that keeps the enclosing `Color` in scope and recurses by
 * index is accepted.
 *
 * Recursion by index would make every lemma below an induction on `|fields| - i` rather than
 * on the structure. `ColorFields` buys ordinary structural recursion back, at the cost of one
 * datatype, which is the same trade `Cpn2mCrl2/Color.lean` makes for a different reason.
 *
 * ## Values are untyped, with typing as a separate predicate
 *
 * As in Lean, and for the same reason: the translator never evaluates, so values appear only
 * in the *statement* of the T2 theorems. `ValueOfColor` is the typing judgement.
 */
module Colors {

  import opened Std.Wrappers
  import opened Util

  /** A color: `Bool`, `Int`, a finite enumeration, or a record. This is `Sigma` of
    * Definition 5. */
  datatype Color =
    | CBool
    | CInt
    | CEnum(name: string, ids: seq<string>)
    | CRecord(name: string, fields: ColorFields)

  /** The fields of a record color, as an association list of field name to color. */
  datatype ColorFields =
    | CFNil
    | CFCons(fname: string, fcolor: Color, frest: ColorFields)

  /** The color of the field `f`, if there is one. */
  function FieldColor(fs: ColorFields, f: string): Option<Color>
  {
    match fs
    case CFNil => None
    case CFCons(n, c, rest) => if n == f then Some(c) else FieldColor(rest, f)
  }

  /** The field names, in declaration order. */
  function FieldNames(fs: ColorFields): seq<string>
  {
    match fs
    case CFNil => []
    case CFCons(n, _, rest) => [n] + FieldNames(rest)
  }

  /** The fields as an ordinary sequence. */
  function FieldsToSeq(fs: ColorFields): seq<(string, Color)>
  {
    match fs
    case CFNil => []
    case CFCons(n, c, rest) => [(n, c)] + FieldsToSeq(rest)
  }

  /** The fields of an ordinary sequence. */
  function FieldsOfSeq(l: seq<(string, Color)>): ColorFields
  {
    if |l| == 0 then CFNil else CFCons(l[0].0, l[0].1, FieldsOfSeq(l[1..]))
  }

  lemma FieldsToSeqOfSeq(l: seq<(string, Color)>)
    ensures FieldsToSeq(FieldsOfSeq(l)) == l
  {
    if |l| != 0 {
      FieldsToSeqOfSeq(l[1..]);
      assert [l[0]] + l[1..] == l;
    }
  }

  /** A value of some color. Untyped; `ValueOfColor` is the typing judgement. */
  datatype Value =
    | VBool(b: bool)
    | VInt(i: int)
    | VCtor(id: string)
    | VRecord(vfields: ValueFields)

  /** The fields of a record value. */
  datatype ValueFields =
    | VFNil
    | VFCons(vname: string, vvalue: Value, vrest: ValueFields)

  /** The value of the field `f`, if there is one. */
  function FieldValue(vs: ValueFields, f: string): Option<Value>
  {
    match vs
    case VFNil => None
    case VFCons(n, v, rest) => if n == f then Some(v) else FieldValue(rest, f)
  }

  /** The typing judgement `v : c`, as a decision procedure.
    *
    * A record value has to list exactly the fields of its color, in order, with each value of
    * the declared color. */
  predicate ValueOfColor(v: Value, c: Color)
    decreases c, 1
  {
    match (v, c)
    case (VBool(_), CBool) => true
    case (VInt(_), CInt) => true
    case (VCtor(id), CEnum(_, ids)) => id in ids
    case (VRecord(vs), CRecord(_, fs)) => ValueFieldsOfColorFields(vs, fs)
    case _ => false
  }

  /** `ValueOfColor`, lifted to the fields of a record. */
  predicate ValueFieldsOfColorFields(vs: ValueFields, fs: ColorFields)
    decreases fs, 0
  {
    match (vs, fs)
    case (VFNil, CFNil) => true
    case (VFCons(n, v, vrest), CFCons(n', c, frest)) =>
      n == n' && ValueOfColor(v, c) && ValueFieldsOfColorFields(vrest, frest)
    case _ => false
  }

  /** Looking a field up in a well-typed record value finds it, at the color the record's own
    * type gives it.
    *
    * This is what `src/Typing.dfy` needs to show that `Proj` never reaches `Junk`. */
  lemma FieldValueOfColorFields(vs: ValueFields, fs: ColorFields, f: string, c: Color)
    requires ValueFieldsOfColorFields(vs, fs)
    requires FieldColor(fs, f) == Some(c)
    ensures FieldValue(vs, f).Some? && ValueOfColor(FieldValue(vs, f).value, c)
  {
    match (vs, fs)
    case (VFCons(n, v, vrest), CFCons(n', c', frest)) =>
      if n != f {
        FieldValueOfColorFields(vrest, frest, f, c);
      }
    case _ =>
  }

  /** A well-typed value of a record color is a record value whose fields are well-typed. */
  lemma ValueIsRecord(v: Value, n: string, fs: ColorFields)
    requires ValueOfColor(v, CRecord(n, fs))
    ensures v.VRecord? && ValueFieldsOfColorFields(v.vfields, fs)
  {
  }

  /** A value of the color `c`, used as the result of an evaluation that typing rules out.
    *
    * `Eval` is total, so the projection of a field that a value does not carry has to return
    * something; `EvalWf` of `src/Typing.dfy` proves the case never arises for a well-typed
    * environment. */
  function Junk(c: Color): Value
  {
    match c
    case CBool => VBool(false)
    case CInt => VInt(0)
    case CEnum(_, ids) => VCtor(if |ids| == 0 then "" else ids[0])
    case CRecord(_, _) => VRecord(VFNil)
  }
}
