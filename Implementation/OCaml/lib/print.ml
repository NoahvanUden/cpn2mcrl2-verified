(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** The mCRL2 encoding of [Implementation/docs/Target.md] §1.

    One [Bag] per place over that place's own color, which is Definition 14 literally.
    [Print_list] is the second backend.

    This is the only part of the core that cannot be verified — the printer is where terms
    become text, and [Implementation/docs/Plan.md] §2 calls T0 and T4 the honest ceiling. It is
    also the smallest part, and [scripts/check.sh] runs [mcrl22lps] over its output on every
    fixture. *)

open Color
open Expr
open Lpe

(** The name the emitted process is given. Reserved along with the keywords, so that no place,
    transition or variable can shadow it. *)
let proc_name = "Spec"

(** The keywords of the mCRL2 language, which an identifier taken from a CPN file may not be. *)
let keywords =
  [
    "sort"; "cons"; "map"; "var"; "eqn"; "act"; "proc"; "init"; "struct";
    "glob"; "pbes"; "Bool"; "Pos"; "Nat"; "Int"; "Real"; "List"; "Set"; "Bag";
    "FSet"; "FBag"; "true"; "false"; "whr"; "end"; "lambda"; "forall"; "exists";
    "div"; "mod"; "in"; "if"; "delta"; "tau"; "sum"; "block"; "allow"; "hide";
    "rename"; "comm"; "val"; "yaled"; "delay"; "nu"; "mu"; "min"; "max"; "succ";
    "pred"; "abs"; "floor"; "ceil"; "round"; "exp"; "A2B"; "head"; "tail";
    "rhead"; "rtail"; "count"; "Nat2Pos"; "Pos2Nat"; "Int2Nat"; "Nat2Int";
    "Int2Real"; "Real2Int"; "Nat2Real"; "Real2Nat"; "Pos2Real"; "Real2Pos";
    "Spec";
  ]

let is_ident_start ch =
  (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch = '_'

let is_ident_char ch =
  is_ident_start ch || (ch >= '0' && ch <= '9') || ch = '\''

(** Whether a name taken from a CPN file may be printed as an mCRL2 identifier: a letter or
    underscore followed by letters, digits, underscores and primes, and not a keyword.

    [Cpn2mCrl2/Print.lean] uses Lean's [Char.isAlpha], which is Unicode-aware; this is ASCII
    only, as [src/Print.dfy] is, which is stricter and is what the mCRL2 grammar admits. The
    importer refuses a net that fails this rather than renaming behind the user's back. *)
let is_safe_ident s =
  String.length s > 0
  && is_ident_start s.[0]
  && (let ok = ref true in
      String.iteri (fun i ch -> if i > 0 && not (is_ident_char ch) then ok := false) s;
      !ok)
  && not (List.mem s keywords)

(* Sorts. *)

(** The mCRL2 sort a color is printed as. *)
let sort_name = function
  | CBool -> "Bool"
  | CInt -> "Int"
  | CEnum (n, _) -> n
  | CRecord (n, _) -> n

(** The mCRL2 sort an expression type is printed as. *)
let sort_ref = function
  | CT c -> sort_name c
  | BT c -> "Bag(" ^ sort_name c ^ ")"
  | LT c -> "List(" ^ sort_name c ^ ")"

(** The name of the [rm] map for a color. mCRL2 has no polymorphic user-defined maps, so the
    three list operations the second backend needs are declared once per color. *)
let rm_name c = "rm_" ^ sort_name c

(** The name of the multiset-difference map for a color. *)
let diff_name c = "diff_" ^ sort_name c

(** The name of the multiset-inclusion map for a color. *)
let sub_name c = "sub_" ^ sort_name c

(** The colors that need a [sort] declaration, including those reached through record
    fields. *)
let rec named_colors c =
  match c with
  | CBool | CInt -> []
  | CEnum (n, ids) -> [ CEnum (n, ids) ]
  | CRecord (n, fs) ->
      CRecord (n, fs) :: List.concat_map (fun (_, c0) -> named_colors c0) fs

(** The field declarations of a record sort. *)
let field_decls fs = List.map (fun (n, c) -> n ^ " : " ^ sort_name c) fs

(** The [sort] declaration of a color, if it needs one. *)
let sort_decl = function
  | CBool | CInt -> None
  | CEnum (n, ids) -> Some ("sort " ^ n ^ " = struct " ^ String.concat " | " ids ^ ";")
  | CRecord (n, fs) ->
      let ds = field_decls fs in
      if ds = [] then Some ("sort " ^ n ^ " = struct " ^ n ^ ";")
      else
        Some ("sort " ^ n ^ " = struct " ^ n ^ "(" ^ String.concat ", " ds ^ ");")

(** The [sort] declarations of a list of colors, each emitted once. *)
let sort_decls cs =
  List.filter_map sort_decl
    (Util.dedup_by sort_name (List.concat_map named_colors cs))

(* Terms. *)

(** An integer literal, parenthesized when negative so that [{-1: 1}] cannot be misread. *)
let int_lit n =
  if n < 0 then "(" ^ string_of_int n ^ ")" else string_of_int n

(** The color a list-sorted term holds, for naming the per-color [diff] and [sub] maps.

    [Cpn2mCrl2/Print.lean] reads this off the index of [Expr.diffList]; here it comes from
    [sort_of], and falls back on [Bool] for a term that has no sort. The fallback is
    unreachable for anything [List_encoding] builds, and a wrong sort name here would be caught
    by [mcrl22lps] — which is tier T0, and is what [scripts/check.sh] runs. *)
let list_color_of e = match sort_of e with Some (LT c) -> c | _ -> CBool

(** An expression as mCRL2 text. Total on every [expr]. *)
let rec print_expr e =
  match e with
  | EVar (x, _) -> x
  | EInt n -> int_lit n
  | EBool b -> if b then "true" else "false"
  | ECtor (_, id) -> id
  | EMkRec (c, args) ->
      let printed = List.map (fun (_, e0) -> print_expr e0) args in
      if printed = [] then sort_name c
      else sort_name c ^ "(" ^ String.concat ", " printed ^ ")"
  | EProj (e0, f) -> f ^ "(" ^ print_expr e0 ^ ")"
  | EAdd (a, b) -> "(" ^ print_expr a ^ " + " ^ print_expr b ^ ")"
  | ESub (a, b) -> "(" ^ print_expr a ^ " - " ^ print_expr b ^ ")"
  | EMul (a, b) -> "(" ^ print_expr a ^ " * " ^ print_expr b ^ ")"
  | EEq (a, b) -> "(" ^ print_expr a ^ " == " ^ print_expr b ^ ")"
  | ELe (a, b) -> "(" ^ print_expr a ^ " <= " ^ print_expr b ^ ")"
  | ELt (a, b) -> "(" ^ print_expr a ^ " < " ^ print_expr b ^ ")"
  | EAnd (a, b) -> "(" ^ print_expr a ^ " && " ^ print_expr b ^ ")"
  | EOr (a, b) -> "(" ^ print_expr a ^ " || " ^ print_expr b ^ ")"
  | ENot a -> "(!" ^ print_expr a ^ ")"
  | EEmptyBag _ -> "{:}"
  | ESingle (k, e0) -> "{" ^ print_expr e0 ^ ": " ^ string_of_int k ^ "}"
  | EBagUnion (a, b) -> "(" ^ print_expr a ^ " + " ^ print_expr b ^ ")"
  | EBagDiff (a, b) -> "(" ^ print_expr a ^ " - " ^ print_expr b ^ ")"
  | EBagSubset (a, b) -> "(" ^ print_expr a ^ " <= " ^ print_expr b ^ ")"
  | ENilList _ -> "[]"
  | ESnoc (l, e0) -> (
      match snoc_items l with
      | Some items -> "[" ^ String.concat ", " (items @ [ print_expr e0 ]) ^ "]"
      | None -> "(" ^ print_expr l ^ " <| " ^ print_expr e0 ^ ")")
  | EAppendList (a, b) -> "(" ^ print_expr a ^ " ++ " ^ print_expr b ^ ")"
  | EDiffList (a, b) ->
      diff_name (list_color_of a) ^ "(" ^ print_expr a ^ ", " ^ print_expr b ^ ")"
  | ESubList (a, b) ->
      sub_name (list_color_of a) ^ "(" ^ print_expr a ^ ", " ^ print_expr b ^ ")"

(** The elements of a list term built from [[]] by [<|], so that it can be printed as mCRL2's
    own list literal rather than as a chain of appends. [None] for anything else. *)
and snoc_items e =
  match e with
  | ENilList _ -> Some []
  | ESnoc (l, e0) -> (
      match snoc_items l with
      | Some items -> Some (items @ [ print_expr e0 ])
      | None -> None)
  | _ -> None

(* The specification. *)

let binder_decls (binder : ctx) =
  List.map (fun (x, t) -> x ^ " : " ^ sort_ref t) binder

(** The binder of a summand: [sum v : S, w : T .], or nothing when [Var(t)] is empty. *)
let print_binder binder =
  if binder = [] then ""
  else "sum " ^ String.concat ", " (binder_decls binder) ^ " . "

let call_args params next =
  List.map
    (fun (x, _) ->
      match Util.lookup next x with
      | Some bt -> print_expr bt.btterm
      | None -> x)
    params

(** The recursive call of a summand, with one argument per place in the order the process
    declares them. *)
let print_call params next =
  if params = [] then proc_name
  else proc_name ^ "(" ^ String.concat ", " (call_args params next) ^ ")"

(** One summand: [sum h : S . c -> a . Spec(g)]. *)
let print_summand params s =
  print_binder s.binder ^ print_expr s.cond ^ " -> " ^ s.act ^ " . "
  ^ print_call params s.next

(** The [+ ] prefixes that separate the summands of the process body. *)
let summand_block printed =
  match printed with
  | [] -> "    delta"
  | first :: rest ->
      String.concat "\n" (("    " ^ first) :: List.map (fun s -> "  + " ^ s) rest)

let param_decls params wrap =
  List.map (fun (x, c) -> x ^ " : " ^ wrap ^ "(" ^ sort_name c ^ ")") params

let init_args params init =
  List.map
    (fun (x, _) ->
      match Util.lookup init x with
      | Some bt -> print_expr bt.btterm
      | None -> "{:}")
    params

(** The whole specification: sort declarations, action declarations, the process equation and
    the initial state.

    The summand count and the parameter count are the structural check
    [Implementation/docs/Target.md] §2 recommends running on every fixture: summands after
    linearization must be exactly [|T| + 1], and process parameters exactly [|P|]. *)
let print_lpe l =
  let sorts = sort_decls (l.sorts @ List.map snd l.params) in
  let sort_block = if sorts = [] then [] else [ String.concat "\n" sorts; "" ] in
  let act_block =
    if l.acts = [] then [] else [ "act " ^ String.concat ", " l.acts ^ ";"; "" ]
  in
  let param_decl =
    if l.params = [] then ""
    else "(" ^ String.concat ", " (param_decls l.params "Bag") ^ ")"
  in
  let body = summand_block (List.map (print_summand l.params) l.summands) in
  let proc_block =
    [ "proc " ^ proc_name ^ param_decl ^ " ="; body ^ ";"; "" ]
  in
  let init_call =
    if l.params = [] then proc_name
    else proc_name ^ "(" ^ String.concat ", " (init_args l.params l.init) ^ ")"
  in
  String.concat "\n"
    (sort_block @ act_block @ proc_block @ [ "init " ^ init_call ^ ";" ])
  ^ "\n"

(** The mCRL2 text of the LPE a CPN translates to: the whole pipeline of
    [Implementation/docs/Plan.md] §2, from a validated [net] to text. *)
let to_mcrl2 n = print_lpe (Translate.to_lpe n)
