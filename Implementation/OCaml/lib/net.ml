(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Definitions 4 and 5, as data, and the T1 validation.

    The tuple [(P, T, A, Sigma, V, C, E, G, I)], component for component: [places] carries [P],
    [C] and [I]; [transitions] carries [T] and [G]; [in_arcs] and [out_arcs] carry the two
    sides of [A] together with [E]; [colors] is [Sigma] and [vars] is [V] with [Type[.]].

    [var_of] and [pre]/[post] are derived, never stored, as
    [Implementation/docs/InputFormat.md] §1 says they must be. *)

open Color
open Expr

(** A place, with its color [C(p)] and its initial marking [I(p)]. *)
type place_decl = { pname : string; pcolor : color; pinit : expr }

(** A transition, with its guard [G(t)]. *)
type trans_decl = { tname : string; guard : expr }

(** An arc together with its expression [E(a)].

    One type serves both sides of [A ⊆ (P × T) ∪ (T × P)]; which side an arc is on is recorded
    by the field of [net] it appears in, exactly as [Proof/ColoredPetriNets.lean] splits
    [inArc] from [outArc]. *)
type arc_decl = {
  aplace : string;
  atrans : string;
  acolor : color;
  aexpr : expr;
}

(** {b Definition 5 (Colored Petri Net)}, as data. *)
type net = {
  colors : color list;
  vars : ctx;
  places : place_decl list;
  transitions : trans_decl list;
  in_arcs : arc_decl list;
  out_arcs : arc_decl list;
}

(** The expression of an arc read at the color [c], or the empty bag if the arc is not at that
    color.

    The fallback never happens for a valid net — [in_arc_place] and [out_arc_place] are exactly
    the statement that it does not — but having it lets the translation be a total function
    from [net] to [Lpe.t] that needs no proof to run, with the proof appearing where
    [Implementation/docs/Plan.md] §2 puts it: in T2, not in the program.

    [Cpn2mCrl2/Net.lean] cannot do this. There [ArcDecl.expr] is indexed by the arc's color, so
    reading it at [c] means transporting along a proof of [a.color = c], and three lemmas exist
    only to push evaluation, free variables and scoping through that transport. This is the
    same trade as [src/Net.dfy] makes, and for the same reason: typing is not indexed here. *)
let expr_at a c = if color_eq a.acolor c then a.aexpr else EEmptyBag c

(* Lookups. These read as standard-library calls and half of them are: [List.map] and
   [List.filter] are inside the fragment Cameleer reads, [List.for_all] and [List.find_opt]
   are not. The corresponding block of [src/Net.dfy] is about sixty lines of hand-written
   recursion, for a different reason again -- a proof there has to induct on the definition
   rather than on a library lemma. *)

let place_names n = List.map (fun d -> d.pname) n.places
let trans_names n = List.map (fun t -> t.tname) n.transitions
let var_names (vs : ctx) = List.map fst vs

(** The [(place, transition)] pairs of a set of arcs, which is what [A] being a set means. *)
let arc_keys arcs = List.map (fun a -> (a.aplace, a.atrans)) arcs

let find_place ps p = Util.find (fun d -> Util.string_eq d.pname p) ps

(** [C(p)], if [p] is a place of the net. *)
let place_color n p =
  match find_place n.places p with Some d -> Some d.pcolor | None -> None

let find_arc arcs p t =
  Util.find (fun a -> Util.string_eq a.aplace p && Util.string_eq a.atrans t) arcs

(** The arc [(p, t)], if there is one. *)
let in_arc n p t = find_arc n.in_arcs p t

(** The arc [(t, p)], if there is one. *)
let out_arc n t p = find_arc n.out_arcs p t

let arcs_of arcs t = List.filter (fun a -> Util.string_eq a.atrans t) arcs

(** [pre(t)], as the arcs into [t] rather than as the places — the same data, and it carries
    [E(p, t)] with it. *)
let pre n t = arcs_of n.in_arcs t

(** [post(t)], as the arcs out of [t]. *)
let post n t = arcs_of n.out_arcs t

let arc_vars arcs = Util.flat_map (fun a -> free_vars a.aexpr) arcs

(** [Var(t)], the variables appearing in the guard of [t] and in the arc expressions of the
    arcs connected to it.

    Duplicates are removed so that the emitted [sum] binds each variable once, and
    [Util.dedup] keeps the last occurrence so that all three translators bind them in the same
    order. *)
let var_of n t =
  Util.dedup
    (free_vars t.guard @ arc_vars (pre n t.tname) @ arc_vars (post n t.tname))

(* The T1 validation of [Implementation/docs/InputFormat.md] §4.3, one named predicate per
   check, so that [Import.explain_invalid] can say which one failed. *)

(** The places have distinct names: [P] is a set. *)
let places_no_dup n = Util.no_dup (place_names n)

(** The transitions have distinct names: [T] is a set. *)
let trans_no_dup n = Util.no_dup (trans_names n)

(** The variables have distinct names: [V] is a set. *)
let vars_no_dup n = Util.no_dup (var_names n.vars)

(** No name is used twice across [P], [T] and [V]. The [P ∩ T = ∅] of Definition 4, extended to
    [V] because the emitted specification binds a place and a variable in one scope. *)
let names_disjoint n =
  Util.all
    (fun x ->
      (not (mem_string x (trans_names n)))
      && not (mem_string x (var_names n.vars)))
    (place_names n)

(** No transition shares a name with a variable. *)
let trans_vars_disjoint n =
  Util.all (fun x -> not (mem_string x (var_names n.vars))) (trans_names n)

(** [Bool ∈ Sigma], as Definition 5 requires. *)
let bool_mem n = mem_color CBool n.colors

(** [C(p) ∈ Sigma] for every place. *)
let color_mem n = Util.all (fun d -> mem_color d.pcolor n.colors) n.places

(** Every variable of [V] is typed by a color, not by a bag or a list. *)
let vars_are_colors n = Util.all (fun q -> is_color_sort (snd q)) n.vars

(** [Type[v] ∈ Sigma] for every variable of [V]. *)
let var_type_mem n =
  Util.all
    (fun q -> match snd q with CT c -> mem_color c n.colors | _ -> false)
    n.vars

(** Every in-arc names a place of the net, at that place's color. *)
let in_arc_place n =
  Util.all (fun a -> color_opt_eq (place_color n a.aplace) (Some a.acolor)) n.in_arcs

(** Every out-arc names a place of the net, at that place's color. *)
let out_arc_place n =
  Util.all (fun a -> color_opt_eq (place_color n a.aplace) (Some a.acolor)) n.out_arcs

(** Every in-arc names a transition of the net. *)
let in_arc_trans n =
  Util.all (fun a -> mem_string a.atrans (trans_names n)) n.in_arcs

(** Every out-arc names a transition of the net. *)
let out_arc_trans n =
  Util.all (fun a -> mem_string a.atrans (trans_names n)) n.out_arcs

(** [A] is a set: at most one arc from a given place to a given transition. *)
let in_arcs_no_dup n = Util.no_dup (arc_keys n.in_arcs)

(** [A] is a set: at most one arc from a given transition to a given place. *)
let out_arcs_no_dup n = Util.no_dup (arc_keys n.out_arcs)

(** [I(p)] is closed, so that [M0] is well-defined without a binding. *)
let init_closed n =
  Util.all
    (fun d -> match free_vars d.pinit with [] -> true | _ -> false)
    n.places

(** [Var(t) ⊆ V] for the guard. *)
let guard_scoped n = Util.all (fun t -> scoped_in n.vars t.guard) n.transitions

(** [Var(t) ⊆ V] for the in-arc expressions. *)
let in_arc_scoped n = Util.all (fun a -> scoped_in n.vars a.aexpr) n.in_arcs

(** [Var(t) ⊆ V] for the out-arc expressions. *)
let out_arc_scoped n = Util.all (fun a -> scoped_in n.vars a.aexpr) n.out_arcs

(** [Type[I(p)] = C(p)_MS]. Free in Lean, where [PlaceDecl.init] is an [Expr (.bag color)]. *)
let init_typed n = Util.all (fun d -> well_typed d.pinit (BT d.pcolor)) n.places

(** [Type[G(t)] = Bool], check 4 of [InputFormat.md] §4.3. Free in Lean. *)
let guard_typed n = Util.all (fun t -> well_typed t.guard (CT CBool)) n.transitions

(** [Type[E(a)] = C(p)_MS] for an in-arc, the rest of check 5. Free in Lean. *)
let in_arc_typed n = Util.all (fun a -> well_typed a.aexpr (BT a.acolor)) n.in_arcs

(** The same for an out-arc. *)
let out_arc_typed n = Util.all (fun a -> well_typed a.aexpr (BT a.acolor)) n.out_arcs

(** The T1 validation of [Implementation/docs/InputFormat.md] §4.3.

    The last four conjuncts are the ones Lean gets for nothing, because there an arc expression
    {i is} an [Expr (.bag color)] and a guard {i is} an [Expr (.color bool)]. Here, as in
    Dafny, they are checks — decided by the importer along with every other conjunct, so that
    all three translators reach the core with the same hypotheses. *)
let valid n =
  places_no_dup n && trans_no_dup n && vars_no_dup n && names_disjoint n
  && trans_vars_disjoint n && bool_mem n && color_mem n && vars_are_colors n
  && var_type_mem n && in_arc_place n && out_arc_place n && in_arc_trans n
  && out_arc_trans n && in_arcs_no_dup n && out_arcs_no_dup n && init_closed n
  && guard_scoped n && in_arc_scoped n && out_arc_scoped n && init_typed n
  && guard_typed n && in_arc_typed n && out_arc_typed n
