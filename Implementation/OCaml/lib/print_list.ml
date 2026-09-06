(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** The mCRL2 text of the list-encoded LPE.

    Everything about the shape of the specification is shared with [Print]; what is different is
    the parameter sorts, the per-color multiset maps that mCRL2 does not provide, and the empty
    list where the bag encoding writes [{:}]. *)

open Print
open List_encoding

(** The three multiset maps for one color, with their defining equations.

    mCRL2 has no polymorphic user-defined maps, so these are declared once per color. The
    equation variables carry a leading underscore so that they cannot shadow a constructor of
    the user's own colors; nothing in the equations refers to anything but them and mCRL2's own
    list operations. *)
let list_ops_decl c =
  let s = sort_name c in
  let ls = "List(" ^ s ^ ")" in
  let rm = rm_name c and df = diff_name c and sb = sub_name c in
  String.concat "\n"
    [
      "map " ^ rm ^ " : " ^ s ^ " # " ^ ls ^ " -> " ^ ls ^ ";";
      "    " ^ df ^ " : " ^ ls ^ " # " ^ ls ^ " -> " ^ ls ^ ";";
      "    " ^ sb ^ " : " ^ ls ^ " # " ^ ls ^ " -> Bool;";
      "var _x, _y : " ^ s ^ ";";
      "    _l, _m : " ^ ls ^ ";";
      "eqn " ^ rm ^ "(_x, []) = [];";
      "    " ^ rm ^ "(_x, _y |> _l) = if(_x == _y, _l, _y |> " ^ rm ^ "(_x, _l));";
      "    " ^ df ^ "(_l, []) = _l;";
      "    " ^ df ^ "(_l, _y |> _m) = " ^ df ^ "(" ^ rm ^ "(_y, _l), _m);";
      "    " ^ sb ^ "([], _m) = true;";
      "    " ^ sb ^ "(_y |> _l, _m) = (_y in _m) && " ^ sb ^ "(_l, " ^ rm ^ "(_y, _m));";
    ]

let list_call_args params next =
  List.map
    (fun (x, _) ->
      match Util.lookup next x with
      | Some lt -> print_expr lt.ltterm
      | None -> x)
    params

(** The recursive call of a list summand, one argument per place. *)
let print_list_call params next =
  if params = [] then proc_name
  else proc_name ^ "(" ^ String.concat ", " (list_call_args params next) ^ ")"

(** One summand of the list encoding. *)
let print_list_summand params s =
  print_binder s.lbinder ^ print_expr s.lcond ^ " -> " ^ s.lact ^ " . "
  ^ print_list_call params s.lnext

let list_init_args params init =
  List.map
    (fun (x, _) ->
      match Util.lookup init x with
      | Some lt -> print_expr lt.ltterm
      | None -> "[]")
    params

(** The whole list-encoded specification.

    The structural check of [Implementation/docs/Target.md] §2 applies to it unchanged:
    [|T| + 1] summands and [|P|] process parameters after linearization. *)
let print_list_lpe l =
  let sorts = sort_decls (l.lsorts @ List.map snd l.lparams) in
  let sort_block = if sorts = [] then [] else [ String.concat "\n" sorts; "" ] in
  let op_colors = Util.dedup_by sort_name (List.map snd l.lparams) in
  let op_block =
    if op_colors = [] then []
    else [ String.concat "\n\n" (List.map list_ops_decl op_colors); "" ]
  in
  let act_block =
    if l.lacts = [] then []
    else [ "act " ^ String.concat ", " l.lacts ^ ";"; "" ]
  in
  let param_decl =
    if l.lparams = [] then ""
    else "(" ^ String.concat ", " (param_decls l.lparams "List") ^ ")"
  in
  let body =
    summand_block (List.map (print_list_summand l.lparams) l.lsummands)
  in
  let proc_block = [ "proc " ^ proc_name ^ param_decl ^ " ="; body ^ ";"; "" ] in
  let init_call =
    if l.lparams = [] then proc_name
    else proc_name ^ "(" ^ String.concat ", " (list_init_args l.lparams l.linit) ^ ")"
  in
  String.concat "\n"
    (sort_block @ op_block @ act_block @ proc_block @ [ "init " ^ init_call ^ ";" ])
  ^ "\n"

(** The mCRL2 text of the list-encoded LPE: the fast backend of
    [Implementation/docs/Plan.md] §5. *)
let to_mcrl2_list n = print_list_lpe (to_lpe_list n)
