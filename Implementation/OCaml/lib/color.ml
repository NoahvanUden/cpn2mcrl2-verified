(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Colors and values.

    The color universe [Sigma] of Definition 5, fixed concretely, and the values that inhabit
    it. [Implementation/docs/InputFormat.md] §4.1 fixes the grammar:

    {v color ::= Bool | Int | enum(name, [id, ...]) | record(name, [(field, color), ...]) v}

    {2 The fields are a list, and in the other two translators they are not}

    Both [Cpn2mCrl2/Color.lean] and [src/Color.dfy] split a record's fields into a separate
    inductive type, [ColorFields], and both do it for a reason that has nothing to do with
    modelling. Lean derives neither [DecidableEq] nor a usable recursor for the nested
    inductive [List (String x Color)]. Dafny has the opposite half of that problem — equality
    on [seq<(string, Color)>] is free — but gives the elements of a bare [seq] no rank below
    the sequence, so a function recursing from [fs] into [fs[0].1] is rejected. Two different
    obstacles, one workaround, one extra datatype and its two conversion functions each.

    Here the fields are [(string * color) list] and the recursion is written the way anyone
    would write it. That also deletes [FieldsToSeq], [FieldsOfSeq] and the lemma relating
    them, and turns [FieldColor] and [FieldValue] into [Util.lookup]. Whether the proof tool
    accepts the recursion is a separate question from whether the compiler does; see the
    README on what Why3 made of it. *)

(** A color: [Bool], [Int], a finite enumeration, or a record. This is [Sigma] of
    Definition 5. *)
type color =
  | CBool
  | CInt
  | CEnum of string * string list
  | CRecord of string * (string * color) list

(** A value of some color. Untyped; [value_of_color] is the typing judgement.

    Untyped for the same reason as in the other two: the translator never evaluates, so values
    appear only in the {i statement} of the T2 theorems. *)
type value =
  | VBool of bool
  | VInt of int
  | VCtor of string
  | VRecord of (string * value) list

(** The color of the field [f], if the record color declares one. *)
let field_color fs f = Util.lookup fs f

(** The field names, in declaration order. *)
let field_names fs = List.map fst fs

(** The value of the field [f], if the record value carries one. *)
let field_value vs f = Util.lookup vs f

(** The typing judgement [v : c], as a decision procedure.

    A record value has to list exactly the fields of its color, in order, with each value of
    the declared color. *)
let rec value_of_color v c =
  match (v, c) with
  | VBool _, CBool -> true
  | VInt _, CInt -> true
  | VCtor id, CEnum (_, ids) -> List.mem id ids
  | VRecord vs, CRecord (_, fs) -> value_fields_of_color_fields vs fs
  | _ -> false

(** [value_of_color], lifted to the fields of a record. *)
and value_fields_of_color_fields vs fs =
  match (vs, fs) with
  | [], [] -> true
  | (n, v) :: vrest, (n', c) :: frest ->
      n = n' && value_of_color v c && value_fields_of_color_fields vrest frest
  | _ -> false

(** A value of the color [c], used as the result of an evaluation that typing rules out.

    Evaluation is total, so projecting a field that a value does not carry has to return
    something; [Typing] proves the case never arises for a well-typed environment. *)
let junk = function
  | CBool -> VBool false
  | CInt -> VInt 0
  | CEnum (_, ids) -> VCtor (match ids with [] -> "" | id :: _ -> id)
  | CRecord (_, _) -> VRecord []
