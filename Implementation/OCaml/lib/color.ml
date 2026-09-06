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
    would write it. That deletes [FieldsToSeq], [FieldsOfSeq] and the lemma relating them, and
    turns [FieldColor] and [FieldValue] into [Util.lookup].

    {2 What it costs instead}

    The equality Lean fails to derive and Dafny gives away has to be written out here, twice,
    because Cameleer's [=] on program values is [int] equality. [color_eq] and [value_eq] are
    that. They are the same shape as the type, so the nested list costs nothing extra — but
    they exist at all only because the verifier has no structural equality. *)

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

let bool_eq (a : bool) (b : bool) : bool = if a then b else not b

let rec string_list_eq (a : string list) (b : string list) : bool =
  match (a, b) with
  | [], [] -> true
  | x :: r, y :: s -> Util.string_eq x y && string_list_eq r s
  | _ -> false

(** Decidable equality on colors. *)
let rec color_eq (c1 : color) (c2 : color) : bool =
  match (c1, c2) with
  | CBool, CBool -> true
  | CInt, CInt -> true
  | CEnum (n1, i1), CEnum (n2, i2) ->
      Util.string_eq n1 n2 && string_list_eq i1 i2
  | CRecord (n1, f1), CRecord (n2, f2) ->
      Util.string_eq n1 n2 && color_fields_eq f1 f2
  | _ -> false

and color_fields_eq (f1 : (string * color) list) (f2 : (string * color) list) :
    bool =
  match (f1, f2) with
  | [], [] -> true
  | (n1, c1) :: r1, (n2, c2) :: r2 ->
      Util.string_eq n1 n2 && color_eq c1 c2 && color_fields_eq r1 r2
  | _ -> false

(** Decidable equality on values. *)
let rec value_eq (v1 : value) (v2 : value) : bool =
  match (v1, v2) with
  | VBool a, VBool b -> bool_eq a b
  | VInt a, VInt b -> a = b
  | VCtor a, VCtor b -> Util.string_eq a b
  | VRecord a, VRecord b -> value_fields_eq a b
  | _ -> false

and value_fields_eq (a : (string * value) list) (b : (string * value) list) :
    bool =
  match (a, b) with
  | [], [] -> true
  | (n1, v1) :: r1, (n2, v2) :: r2 ->
      Util.string_eq n1 n2 && value_eq v1 v2 && value_fields_eq r1 r2
  | _ -> false

let color_opt_eq (o1 : color option) (o2 : color option) : bool =
  match (o1, o2) with
  | None, None -> true
  | Some a, Some b -> color_eq a b
  | _ -> false

(** Whether the list of colors contains [c]. *)
let rec mem_color (c : color) (l : color list) : bool =
  match l with [] -> false | d :: rest -> color_eq c d || mem_color c rest

(** The color of the field [f], if the record color declares one. *)
let field_color (fs : (string * color) list) (f : string) = Util.lookup fs f

(** The field names, in declaration order. *)
let field_names (fs : (string * color) list) = List.map fst fs

(** The value of the field [f], if the record value carries one. *)
let field_value (vs : (string * value) list) (f : string) = Util.lookup vs f

(** Whether the enumeration [ids] contains [id]. [List.mem] would do, and Cameleer even knows
    it — but it would compare with the equality Cameleer cannot see on other types, so the
    explicit form is used throughout for consistency. *)
let rec mem_string (x : string) (l : string list) : bool =
  match l with [] -> false | y :: rest -> Util.string_eq x y || mem_string x rest

(** The typing judgement [v : c], as a decision procedure.

    A record value has to list exactly the fields of its color, in order, with each value of
    the declared color. *)
let rec value_of_color (v : value) (c : color) : bool =
  match (v, c) with
  | VBool _, CBool -> true
  | VInt _, CInt -> true
  | VCtor id, CEnum (_, ids) -> mem_string id ids
  | VRecord vs, CRecord (_, fs) -> value_fields_of_color_fields vs fs
  | _ -> false

(** [value_of_color], lifted to the fields of a record. *)
and value_fields_of_color_fields (vs : (string * value) list)
    (fs : (string * color) list) : bool =
  match (vs, fs) with
  | [], [] -> true
  | (n, v) :: vrest, (n', c) :: frest ->
      Util.string_eq n n' && value_of_color v c
      && value_fields_of_color_fields vrest frest
  | _ -> false

(** A value of the color [c], used as the result of an evaluation that typing rules out.

    Evaluation is total, so projecting a field that a value does not carry has to return
    something; [Typing] proves the case never arises for a well-typed environment. *)
let junk (c : color) : value =
  match c with
  | CBool -> VBool false
  | CInt -> VInt 0
  | CEnum (_, ids) -> VCtor (match ids with [] -> "" | id :: _ -> id)
  | CRecord (_, _) -> VRecord []
