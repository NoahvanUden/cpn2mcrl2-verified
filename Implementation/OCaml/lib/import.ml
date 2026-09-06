(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** The importer, {b outside the trust boundary}.

    Reads the native CPN JSON of [Implementation/docs/InputFormat.md] §4.2 and decides the T1
    validation of §4.3. Nothing downstream trusts it: [net_of_string] returns a [net] only
    after [Net.valid] has said yes, so from there inwards the checks are hypotheses.

    {2 Only one fuel counter survives}

    [src/Import.dfy] threads a fuel counter through four mutually recursive checking functions
    and through colour resolution, because Dafny needs a termination argument for every
    function, verified or not, and the bidirectional checker's recursion is not structural —
    [infer_expr] calls [check_directed] back on the {i same} node once it has learned that
    node's sort. [Cpn2mCrl2/Json.lean] sidesteps the same problem with [partial def].

    OCaml needs neither. What remains is [resolve_color]'s fuel, and that one is not
    bookkeeping: a record field names another colour, so a cyclic declaration would genuinely
    loop, and the bound turns it into an error message. The distinction is worth the note —
    two of the three translators carry a counter that exists only to satisfy the tool, and the
    third carries only the one that is about the input. *)

open Color
open Expr
open Net

(** Failure carries a message. [let*] is [Result.bind], which is what Dafny writes [:-]. *)
type 'a m = ('a, string) result

let ( let* ) = Result.bind
let ok = Result.ok
let err msg = Error msg

(** An association list sorted by its key, so that a JSON object is presented in a canonical
    order.

    This lives here and not in [Util] because it is the one utility the verified core does not
    use, and [List.stable_sort] is outside the fragment Cameleer reads. A JSON object cannot
    have two members of the same name, so stability is not observable; it is what makes this
    agree with the insertion sort the other two translators use. *)
let sort_by_key l = List.stable_sort (fun (a, _) (b, _) -> String.compare a b) l

(* Reading JSON. *)

let get_obj = function
  | `Assoc o -> ok o
  | _ -> err "expected an object"

let get_arr = function `List a -> ok a | _ -> err "expected an array"
let get_str = function `String s -> ok s | _ -> err "expected a string"
let get_bool = function `Bool b -> ok b | _ -> err "expected a boolean"

let get_int = function
  | `Int n -> ok n
  | `Intlit s -> ( try ok (int_of_string s) with _ -> err "integer out of range")
  | _ -> err "expected an integer"

let get_nat j =
  let* n = get_int j in
  if n >= 0 then ok n else err "expected a non-negative integer"

let field j name =
  let* o = get_obj j in
  match Util.lookup o name with
  | Some v -> ok v
  | None -> err ("missing field " ^ name)

(** The [i]th element of an array, named so that a failure can say which. *)
let idx a i what =
  match List.nth_opt a i with
  | Some v -> ok v
  | None -> err (what ^ ": missing element " ^ string_of_int i)

(** The members of a JSON object, sorted by key.

    Lean's [Json] holds an object as a balanced tree, so its entries arrive in key order.
    Yojson keeps them in file order, as Dafny's standard library does, so they are sorted
    explicitly — which makes all three translators emit places, transitions and variables in
    the same order, and so makes their output comparable as text. *)
let entries j =
  let* o = get_obj j in
  ok (sort_by_key o)

let check_ident kind s =
  if Print.is_safe_ident s then ok s
  else
    err
      (kind ^ " " ^ s
     ^ " is not usable as an mCRL2 identifier: it is a reserved keyword, or not a letter or \
        underscore followed by letters, digits, underscores and primes")

let rec check_idents kind = function
  | [] -> ok []
  | j :: rest ->
      let* s = get_str j in
      let* head = check_ident kind s in
      let* tail = check_idents kind rest in
      ok (head :: tail)

(* Colours. *)

(** Resolve a colour {i name} into the colour tree [Color] holds.

    A record field names another colour, so resolution recurses; [fuel] bounds it by the number
    of declarations, which turns a cyclic definition into an error instead of a loop. *)
let rec resolve_color decls fuel name =
  if fuel = 0 then
    err
      ("color " ^ name
     ^ " is defined cyclically, or nested deeper than there are colors")
  else
    match Util.lookup decls name with
    | None -> err ("undeclared color " ^ name)
    | Some j -> (
        let* kj = field j "kind" in
        let* kind = get_str kj in
        match kind with
        | "bool" -> ok CBool
        | "int" -> ok CInt
        | "enum" ->
            let* _ = check_ident "color" name in
            let* idsj = field j "ids" in
            let* arr = get_arr idsj in
            let* ids = check_idents "constructor" arr in
            if ids = [] then
              err
                ("enumeration " ^ name
               ^ " has no constructors, so it has no values")
            else ok (CEnum (name, ids))
        | "record" ->
            let* _ = check_ident "color" name in
            let* fsj = field j "fields" in
            let* arr = get_arr fsj in
            let* fs = resolve_fields decls fuel arr in
            ok (CRecord (name, fs))
        | _ -> err ("color " ^ name ^ " has unknown kind " ^ kind))

and resolve_fields decls fuel = function
  | [] -> ok []
  | j :: rest ->
      let* p = get_arr j in
      let* f0 = idx p 0 "record field" in
      let* fname0 = get_str f0 in
      let* fname = check_ident "field" fname0 in
      let* c0 = idx p 1 "record field" in
      let* cname = get_str c0 in
      let* c = resolve_color decls (fuel - 1) cname in
      let* tail = resolve_fields decls fuel rest in
      ok ((fname, c) :: tail)

let find_color_named colors n =
  List.find_opt (fun c -> Print.sort_name c = n) colors

let color_named colors n =
  match find_color_named colors n with
  | Some c -> ok c
  | None -> err ("undeclared color " ^ n)

let enums_with colors id =
  List.filter
    (function CEnum (_, ids) -> List.mem id ids | _ -> false)
    colors

(* Expressions: bidirectional type checking, in four mutually recursive functions.

   [check_directed] dispatches on the *expected sort*, which is what lets ["emptyBag"],
   ["ctor", id] and ["rec", ...] be written without an annotation: their colour comes from the
   place or the guard they annotate. It answers [None] for a head the sort does not settle, and
   [check_expr] then falls through [coerce_to] to [infer_expr]. *)

let rec check_expr vars colors j t =
  let* direct = check_directed vars colors j t in
  match direct with Some e -> ok e | None -> coerce_to vars colors j t

(** Infer the sort of an expression and require it to be the expected one. *)
and coerce_to vars colors j t =
  let* s, e = infer_expr vars colors j in
  if s = t then ok e
  else
    err
      ("expression has sort " ^ Print.sort_ref s ^ " where " ^ Print.sort_ref t
     ^ " is expected")

(** The half of checking that the expected sort settles on its own. [None] means "this head is
    not one the sort decides"; the caller falls through to inference. *)
and check_directed vars colors j t =
  let* a = get_arr j in
  let* h0 = idx a 0 "expression" in
  let* hd = get_str h0 in
  match t with
  | BT c -> (
      match hd with
      | "emptyBag" -> ok (Some (EEmptyBag c))
      | "bag" ->
          let* itemsj = idx a 1 "bag literal" in
          let* items = get_arr itemsj in
          let* terms = check_bag_items vars colors items c in
          ok (Some (union_all c terms))
      | "union" ->
          let* x = idx a 1 "union" in
          let* y = idx a 2 "union" in
          let* ex = check_expr vars colors x (BT c) in
          let* ey = check_expr vars colors y (BT c) in
          ok (Some (EBagUnion (ex, ey)))
      | "diff" ->
          let* x = idx a 1 "diff" in
          let* y = idx a 2 "diff" in
          let* ex = check_expr vars colors x (BT c) in
          let* ey = check_expr vars colors y (BT c) in
          ok (Some (EBagDiff (ex, ey)))
      | _ -> ok None)
  | CT (CEnum (n, ids)) ->
      if hd = "ctor" then
        let* idj = idx a 1 "constructor" in
        let* id = get_str idj in
        if List.mem id ids then ok (Some (ECtor (CEnum (n, ids), id)))
        else err (id ^ " is not a constructor of the enumeration " ^ n)
      else ok None
  | CT (CRecord (n, fs)) ->
      if hd = "rec" then
        let* arrj = idx a 2 "record literal" in
        let* arr = get_arr arrj in
        let* given = record_fields arr in
        let* _ = check_given_fields n given fs in
        let* args = check_args vars colors n given fs in
        ok (Some (EMkRec (CRecord (n, fs), args)))
      else ok None
  | _ -> ok None

and check_bag_items vars colors items c =
  match items with
  | [] -> ok []
  | j :: rest ->
      let* p = get_arr j in
      let* nj = idx p 0 "bag item" in
      let* k = get_nat nj in
      let* ej = idx p 1 "bag item" in
      let* e = check_expr vars colors ej (CT c) in
      let* tail = check_bag_items vars colors rest c in
      ok (ESingle (k, e) :: tail)

and record_fields = function
  | [] -> ok []
  | j :: rest ->
      let* p = get_arr j in
      let* fj = idx p 0 "record field" in
      let* f = get_str fj in
      let* ej = idx p 1 "record field" in
      let* tail = record_fields rest in
      ok ((f, ej) :: tail)

(** Every field the literal gives is a field the colour has. *)
and check_given_fields n given fs =
  match given with
  | [] -> ok true
  | (f, _) :: rest ->
      if field_color fs f = None then
        err
          ("record literal for " ^ n ^ " gives a field " ^ f
         ^ " that the color does not have")
      else check_given_fields n rest fs

(** One expression per field of a record colour, taken from the literal by name so that the
    file need not list the fields in declaration order. *)
and check_args vars colors n given fs =
  match fs with
  | [] -> ok []
  | (f, c) :: rest -> (
      match Util.lookup given f with
      | None -> err ("record literal for " ^ n ^ " is missing the field " ^ f)
      | Some j ->
          let* e = check_expr vars colors j (CT c) in
          let* tail = check_args vars colors n given rest in
          ok ((f, e) :: tail))

(** Bidirectional type checking, inferring half. *)
and infer_expr vars colors j =
  let* a = get_arr j in
  let* h0 = idx a 0 "expression" in
  let* hd = get_str h0 in
  match hd with
  | "var" -> (
      let* xj = idx a 1 "variable" in
      let* x = get_str xj in
      match Util.lookup vars x with
      | None -> err (x ^ " is not a variable of the net")
      | Some t -> ok (t, EVar (x, t)))
  | "int" ->
      let* nj = idx a 1 "integer literal" in
      let* n = get_int nj in
      ok (CT CInt, EInt n)
  | "bool" ->
      let* bj = idx a 1 "boolean literal" in
      let* b = get_bool bj in
      ok (CT CBool, EBool b)
  | "+" | "-" | "*" | "<=" | "<" ->
      let* xj = idx a 1 hd in
      let* yj = idx a 2 hd in
      let* x = check_expr vars colors xj (CT CInt) in
      let* y = check_expr vars colors yj (CT CInt) in
      ok
        (match hd with
        | "+" -> (CT CInt, EAdd (x, y))
        | "-" -> (CT CInt, ESub (x, y))
        | "*" -> (CT CInt, EMul (x, y))
        | "<=" -> (CT CBool, ELe (x, y))
        | _ -> (CT CBool, ELt (x, y)))
  | "&&" | "||" ->
      let* xj = idx a 1 hd in
      let* yj = idx a 2 hd in
      let* x = check_expr vars colors xj (CT CBool) in
      let* y = check_expr vars colors yj (CT CBool) in
      ok (CT CBool, if hd = "&&" then EAnd (x, y) else EOr (x, y))
  | "!" ->
      let* xj = idx a 1 "not" in
      let* x = check_expr vars colors xj (CT CBool) in
      ok (CT CBool, ENot x)
  | "=" -> (
      let* xj = idx a 1 "equality" in
      let* yj = idx a 2 "equality" in
      let* s, ex = infer_expr vars colors xj in
      match s with
      | CT _ ->
          let* y = check_expr vars colors yj s in
          ok (CT CBool, EEq (ex, y))
      | _ -> err "equality compares values, not bags or lists")
  | "proj" -> (
      let* ej = idx a 1 "projection" in
      let* fj = idx a 2 "projection" in
      let* f = get_str fj in
      let* s, e = infer_expr vars colors ej in
      match s with
      | CT (CRecord (rn, fs)) -> (
          match field_color fs f with
          | None -> err ("the record " ^ rn ^ " has no field " ^ f)
          | Some c -> ok (CT c, EProj (e, f)))
      | _ -> err (f ^ " is projected out of something that is not a record"))
  | "rec" -> (
      let* nj = idx a 1 "record literal" in
      let* n = get_str nj in
      match find_color_named colors n with
      | None -> err ("undeclared color " ^ n)
      | Some (CRecord _ as c) -> (
          let* got = check_directed vars colors j (CT c) in
          match got with
          | Some e -> ok (CT c, e)
          | None -> err ("malformed record literal for " ^ n))
      | Some _ -> err (n ^ " is not a record color"))
  | "ctor" -> (
      let* idj = idx a 1 "constructor" in
      let* id = get_str idj in
      match enums_with colors id with
      | [] -> err (id ^ " is not a constructor of any declared enumeration")
      | [ c ] -> ok (CT c, ECtor (c, id))
      | _ ->
          err
            (id
           ^ " is a constructor of more than one enumeration, so its color cannot be inferred \
              here"))
  | "bag" -> (
      let* itemsj = idx a 1 "bag literal" in
      let* items = get_arr itemsj in
      match items with
      | [] ->
          err
            "an empty bag literal needs a known color; write it where the sort is expected"
      | first :: _ -> (
          let* p = get_arr first in
          let* ej = idx p 1 "bag item" in
          let* s, _ = infer_expr vars colors ej in
          match s with
          | CT c -> (
              let* got = check_directed vars colors j (BT c) in
              match got with
              | Some e -> ok (BT c, e)
              | None -> err "malformed bag literal")
          | _ -> err "a bag cannot hold bags or lists"))
  | "union" | "diff" -> (
      let* xj = idx a 1 hd in
      let* s, _ = infer_expr vars colors xj in
      match s with
      | BT c -> (
          let* got = check_directed vars colors j (BT c) in
          match got with
          | Some e -> ok (BT c, e)
          | None -> err ("malformed " ^ hd))
      | _ -> err (hd ^ " takes bags"))
  | "emptyBag" ->
      err "the empty bag needs a known color; write it where the sort is expected"
  | _ -> err ("unknown expression form " ^ hd)

(* The net. *)

let rec resolve_all decls fuel = function
  | [] -> ok []
  | (name, _) :: rest ->
      let* c = resolve_color decls fuel name in
      let* tail = resolve_all decls fuel rest in
      ok (c :: tail)

let rec read_vars colors = function
  | [] -> ok []
  | (name, j) :: rest ->
      let* _ = check_ident "variable" name in
      let* cn = get_str j in
      let* c = color_named colors cn in
      let* tail = read_vars colors rest in
      ok ((name, CT c) :: tail)

let rec read_places colors = function
  | [] -> ok []
  | (name, j) :: rest ->
      let* _ = check_ident "place" name in
      let* cj = field j "color" in
      let* cn = get_str cj in
      let* c = color_named colors cn in
      let* ij = field j "init" in
      let* init = check_expr [] colors ij (BT c) in
      let* tail = read_places colors rest in
      ok ({ pname = name; pcolor = c; pinit = init } :: tail)

let rec read_transitions vars colors = function
  | [] -> ok []
  | (name, j) :: rest ->
      let* _ = check_ident "transition" name in
      let* gj = field j "guard" in
      let* g = check_expr vars colors gj (CT CBool) in
      let* tail = read_transitions vars colors rest in
      ok ({ tname = name; guard = g } :: tail)

let rec read_arcs vars colors places = function
  | [] -> ok []
  | j :: rest -> (
      let* pj = field j "place" in
      let* p = get_str pj in
      let* tj = field j "transition" in
      let* t = get_str tj in
      match find_place places p with
      | None -> err ("an arc names a place " ^ p ^ " that the net does not have")
      | Some d ->
          let* ej = field j "expr" in
          let* e = check_expr vars colors ej (BT d.pcolor) in
          let* tail = read_arcs vars colors places rest in
          ok ({ aplace = p; atrans = t; acolor = d.pcolor; aexpr = e } :: tail))

(** Read a [net] from the JSON of [Implementation/docs/InputFormat.md] §4.2.

    Nothing here checks [Net.valid]; [net_of_string] does that afterwards, so that a failure can
    name the condition that failed. *)
let net_of_json j =
  let* colorsj = field j "colors" in
  let* color_decls = entries colorsj in
  let* colors = resolve_all color_decls (List.length color_decls + 1) color_decls in
  let* varsj = field j "variables" in
  let* var_entries = entries varsj in
  let* vars = read_vars colors var_entries in
  let* placesj = field j "places" in
  let* place_entries = entries placesj in
  let* places = read_places colors place_entries in
  let* transj = field j "transitions" in
  let* trans_entries = entries transj in
  let* transitions = read_transitions vars colors trans_entries in
  let* inj = field j "inArcs" in
  let* in_arr = get_arr inj in
  let* in_arcs = read_arcs vars colors places in_arr in
  let* outj = field j "outArcs" in
  let* out_arr = get_arr outj in
  let* out_arcs = read_arcs vars colors places out_arr in
  ok
    {
      colors = (if List.mem CBool colors then colors else colors @ [ CBool ]);
      vars;
      places;
      transitions;
      in_arcs;
      out_arcs;
    }

let no b msg = if b then [] else [ msg ]

(** The T1 checks that fail, by name, so that a rejection can say what is wrong rather than only
    that something is.

    This mirrors [Net.valid] conjunct for conjunct. Nothing depends on it: [net_of_string]
    decides [Net.valid] itself, and that decision is what the core receives. *)
let explain_invalid n =
  no (places_no_dup n) "two places share a name"
  @ no (trans_no_dup n) "two transitions share a name"
  @ no (vars_no_dup n) "two variables share a name"
  @ no (names_disjoint n) "a place shares its name with a transition or a variable"
  @ no (trans_vars_disjoint n) "a transition shares its name with a variable"
  @ no (bool_mem n) "Bool is not among the colors"
  @ no (color_mem n) "a place has an undeclared color"
  @ no (vars_are_colors n) "a variable is not typed by a color"
  @ no (var_type_mem n) "a variable has an undeclared color"
  @ no (in_arc_place n) "an in-arc expression is not of the color of its place"
  @ no (out_arc_place n) "an out-arc expression is not of the color of its place"
  @ no (in_arc_trans n) "an in-arc names a transition the net does not have"
  @ no (out_arc_trans n) "an out-arc names a transition the net does not have"
  @ no (in_arcs_no_dup n) "two in-arcs connect the same place and transition"
  @ no (out_arcs_no_dup n) "two out-arcs connect the same transition and place"
  @ no (init_closed n) "an initialization expression is not closed"
  @ no (guard_scoped n) "a guard mentions a variable outside V"
  @ no (in_arc_scoped n) "an in-arc expression mentions a variable outside V"
  @ no (out_arc_scoped n) "an out-arc expression mentions a variable outside V"
  @ no (init_typed n) "an initialization expression is not a bag of its place's color"
  @ no (guard_typed n) "a guard is not a boolean expression"
  @ no (in_arc_typed n) "an in-arc expression is not a bag of its place's color"
  @ no (out_arc_typed n) "an out-arc expression is not a bag of its place's color"

(** Read a CPN from the text of a native CPN file, validated.

    From here inwards the T1 checks of [Implementation/docs/InputFormat.md] §4.3 are
    hypotheses, not assumptions. *)
let net_of_string s =
  let* j =
    try ok (Yojson.Safe.from_string s)
    with Yojson.Json_error m -> err ("the input is not JSON: " ^ m)
  in
  let* n = net_of_json j in
  if valid n then ok n
  else
    err
      ("the input is not a CPN:\n  - "
      ^ String.concat "\n  - " (explain_invalid n))
