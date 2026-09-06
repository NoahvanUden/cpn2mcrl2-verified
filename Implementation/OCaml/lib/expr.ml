(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** The expression language, its sorts, and its evaluation.

    [EXPR] of [Implementation/docs/InputFormat.md] §4.1, together with the operations
    Definition 14 needs. One language serves both as the annotation language of a CPN and as
    the mCRL2 data language the translation emits into, which is obligation 2 of
    [Implementation/docs/Plan.md] §4.

    {2 Typing is inferred, not indexed}

    [Cpn2mCrl2/Expr.lean] makes [Expr] an inductive family indexed by [ExprTy], so a guard is
    a boolean expression and an arc expression is a bag expression {i by construction}.
    OCaml can express that — it has GADTs — but Cameleer cannot read one, so [expr] is a flat
    variant and [sort_of] infers. That puts this translator on Dafny's side of the divide, and
    it is worth being precise about why: Dafny lacks the feature, OCaml has it and the proof
    tool does not support it.

    {2 Scoping is extrinsic}

    [expr] is not indexed by a typing context either; a variable carries its name and sort and
    [scoped_in] is a separate predicate. That is the decision that made obligation 4 free in
    all three of the developments that have finished, and [Thesis/docs/LeanFormalization.md]
    §5.2 is where the three agree on why. *)

open Color

(** A sort: a color, a bag of a color, or a list of a color. *)
type expr_ty = CT of color | BT of color | LT of color

(** A typing context: the variables in scope, with their sorts. [V] of Definition 5 together
    with [Type[.]] is one of these, in which every entry is a [CT]. *)
type ctx = (string * expr_ty) list

(** Whether a sort is a color rather than a bag or a list.

    Definition 5 types every variable of [V] by a color. [Net.valid] says so with this rather
    than with an existential over [color], because the importer has to be able to check it. *)
let is_color_sort = function CT _ -> true | _ -> false

(** Decidable equality on sorts, and on an optional sort.

    [sort_of] answers an [expr_ty option] and almost every use of it is a comparison, so these
    two are the most-used functions in the file. In Lean the comparison is [DecidableEq],
    derived; in Dafny it is [==]. *)
let expr_ty_eq (t1 : expr_ty) (t2 : expr_ty) : bool =
  match (t1, t2) with
  | CT a, CT b -> color_eq a b
  | BT a, BT b -> color_eq a b
  | LT a, LT b -> color_eq a b
  | _ -> false

let expr_ty_opt_eq (o1 : expr_ty option) (o2 : expr_ty option) : bool =
  match (o1, o2) with
  | None, None -> true
  | Some a, Some b -> expr_ty_eq a b
  | _ -> false

(** [EXPR], with four departures from the grammar of [InputFormat.md] §4.1.

    [EVar] may have bag sort. A CPN file never produces one; Definition 14's place parameters
    are the only bag-sorted variables that occur.

    [EBagSubset] is the operation Definition 14 uses and a CPN never contains. [Import] does
    not parse it.

    [ESingle] replaces the grammar's [bag([(n, e), ...])]. A bag literal with several items is
    the union of its singletons, which is how Definition 1 builds it anyway.

    The five list constructors are not part of any CPN either; [List_encoding] is what they
    are for.

    A record literal's arguments are a [(string * expr) list] and not a separate datatype, for
    the reason [Color] gives about a record color's fields. *)
type expr =
  | EVar of string * expr_ty
  | EInt of int
  | EBool of bool
  | ECtor of color * string
  | EMkRec of color * (string * expr) list
  | EProj of expr * string
  | EAdd of expr * expr
  | ESub of expr * expr
  | EMul of expr * expr
  | EEq of expr * expr
  | ELe of expr * expr
  | ELt of expr * expr
  | EAnd of expr * expr
  | EOr of expr * expr
  | ENot of expr
  | EEmptyBag of color
  | ESingle of int * expr
  | EBagUnion of expr * expr
  | EBagDiff of expr * expr
  | EBagSubset of expr * expr
  | ENilList of color
  | ESnoc of expr * expr
  | EAppendList of expr * expr
  | EDiffList of expr * expr
  | ESubList of expr * expr

(* The five helpers below take the *sorts* of the operands rather than the operands. In
   [src/Expr.dfy] that is forced: Dafny gives a freshly built [EAdd(a, b)] no relation to the
   [ESub(a, b)] a caller was matching on, so a helper phrased over expressions would need one
   termination witness per operator. Nothing forces it here, but the shape is kept so the two
   can be read side by side. *)

let int_pair sa sb result =
  if expr_ty_opt_eq sa (Some (CT CInt)) && expr_ty_opt_eq sb (Some (CT CInt))
  then Some result
  else None

let bool_pair sa sb =
  if expr_ty_opt_eq sa (Some (CT CBool)) && expr_ty_opt_eq sb (Some (CT CBool))
  then Some (CT CBool)
  else None

let same_color_pair sa sb =
  match (sa, sb) with
  | Some (CT c1), Some (CT c2) -> if color_eq c1 c2 then Some (CT CBool) else None
  | _ -> None

(** The sort of a binary bag operation: [same] says whether the result is the bag sort itself
    (union, difference) or [Bool] (inclusion). *)
let bag_pair sa sb same =
  match (sa, sb) with
  | Some (BT c1), Some (BT c2) ->
      if color_eq c1 c2 then Some (if same then BT c1 else CT CBool) else None
  | _ -> None

let list_pair sa sb same =
  match (sa, sb) with
  | Some (LT c1), Some (LT c2) ->
      if color_eq c1 c2 then Some (if same then LT c1 else CT CBool) else None
  | _ -> None

let snoc_pair sl se =
  match (sl, se) with
  | Some (LT c1), Some (CT c2) -> if color_eq c1 c2 then Some (LT c1) else None
  | _ -> None

(** The sort of an expression, if it has one. *)
let rec sort_of e =
  match e with
  | EVar (_, t) -> Some t
  | EInt _ -> Some (CT CInt)
  | EBool _ -> Some (CT CBool)
  | ECtor (c, id) -> (
      match c with
      | CEnum (_, ids) -> if mem_string id ids then Some (CT c) else None
      | _ -> None)
  | EMkRec (c, args) -> (
      match c with
      | CRecord (_, fs) -> if args_match args fs then Some (CT c) else None
      | _ -> None)
  | EProj (e0, f) -> (
      match sort_of e0 with
      | Some (CT (CRecord (_, fs))) -> (
          match field_color fs f with Some c -> Some (CT c) | None -> None)
      | _ -> None)
  | EAdd (a, b) -> int_pair (sort_of a) (sort_of b) (CT CInt)
  | ESub (a, b) -> int_pair (sort_of a) (sort_of b) (CT CInt)
  | EMul (a, b) -> int_pair (sort_of a) (sort_of b) (CT CInt)
  | ELe (a, b) -> int_pair (sort_of a) (sort_of b) (CT CBool)
  | ELt (a, b) -> int_pair (sort_of a) (sort_of b) (CT CBool)
  | EEq (a, b) -> same_color_pair (sort_of a) (sort_of b)
  | EAnd (a, b) -> bool_pair (sort_of a) (sort_of b)
  | EOr (a, b) -> bool_pair (sort_of a) (sort_of b)
  | ENot a ->
      if expr_ty_opt_eq (sort_of a) (Some (CT CBool)) then Some (CT CBool)
      else None
  | EEmptyBag c -> Some (BT c)
  | ESingle (_, e0) -> (
      match sort_of e0 with Some (CT c) -> Some (BT c) | _ -> None)
  | EBagUnion (a, b) -> bag_pair (sort_of a) (sort_of b) true
  | EBagDiff (a, b) -> bag_pair (sort_of a) (sort_of b) true
  | EBagSubset (a, b) -> bag_pair (sort_of a) (sort_of b) false
  | ENilList c -> Some (LT c)
  | ESnoc (l, e0) -> snoc_pair (sort_of l) (sort_of e0)
  | EAppendList (a, b) -> list_pair (sort_of a) (sort_of b) true
  | EDiffList (a, b) -> list_pair (sort_of a) (sort_of b) true
  | ESubList (a, b) -> list_pair (sort_of a) (sort_of b) false

(** The arguments of a record literal line up with the fields of its color: same names, same
    order, each of the declared sort. *)
and args_match args fs =
  match (args, fs) with
  | [], [] -> true
  | (n, e) :: arest, (n', c) :: frest ->
      Util.string_eq n n'
      && expr_ty_opt_eq (sort_of e) (Some (CT c))
      && args_match arest frest
  | _ -> false

(** [e] has the sort [t]. *)
let well_typed e t = expr_ty_opt_eq (sort_of e) (Some t)

(** What an expression evaluates to. *)
type denot = DVal of value | DBag of Bag.t | DList of value list

(** Every element of the list has the color [c]. *)
let seq_of_color l c = Util.all (fun v -> value_of_color v c) l

(** Structural equality on denotations, which an equality test evaluates with. *)
let rec value_list_eq (a : value list) (b : value list) : bool =
  match (a, b) with
  | [], [] -> true
  | x :: r, y :: s -> value_eq x y && value_list_eq r s
  | _ -> false

let denot_eq (d1 : denot) (d2 : denot) : bool =
  match (d1, d2) with
  | DVal a, DVal b -> value_eq a b
  | DBag a, DBag b -> Bag.bag_eq a b
  | DList a, DList b -> value_list_eq a b
  | _ -> false

(** A denotation of the right shape for the sort [t]. *)
let denot_has_sort d t =
  match (d, t) with
  | DVal v, CT c -> value_of_color v c
  | DBag m, BT c -> Bag.of_color m c
  | DList l, LT c -> seq_of_color l c
  | _ -> false

(** A binding: a denotation for every sort and name.

    Definition 2's [B[V]] is the restriction of this to the variables of [V]. [eval_congr] of
    [Correct] says an expression cannot tell two environments apart when they agree on its free
    variables, which is what makes the restriction harmless — and is obligation 4. *)
type env = expr_ty -> string -> denot

(** The environment binding every variable to junk. *)
let junk_env : env =
 fun t _ ->
  match t with
  | CT c -> DVal (junk c)
  | BT _ -> DBag Bag.empty
  | LT _ -> DList []

(** An environment is well-typed {i on [g]} when every variable of [g] holds a denotation of
    the sort [g] gives it.

    This, and not well-typedness at every sort and name, is Definition 2's [B[V]]: a binding
    assigns a value of [Type[v]] to each [v] in [V] and says nothing about anything else. It
    is also the only form that is usable, because [env] is total and an enumeration with no
    constructors has no value at all for a junk environment to hold. *)
let env_wf_on (g : ctx) (env : env) =
  Util.all (fun q -> denot_has_sort (env (snd q) (fst q)) (snd q)) g

(* Reading a denotation at a shape. [denot] is untyped, so evaluating [1 + e] has to do
   something when [e] is not an integer. These give the value a well-typed environment
   guarantees, and junk otherwise; [Typing] proves the junk branches are unreachable. *)

let as_int = function DVal (VInt i) -> i | _ -> 0
let as_bool = function DVal (VBool b) -> b | _ -> false
let as_record = function DVal (VRecord fs) -> fs | _ -> []
let as_bag = function DBag m -> m | _ -> Bag.empty
let as_seq = function DList l -> l | _ -> []
let as_value = function DVal v -> v | _ -> VBool false

(** The value of an expression under a binding.

    In [src/Semantics.dfy] and [src/Expr.dfy] the corresponding function is [ghost], so Dafny
    guarantees it is absent from the compiled artifact. OCaml has no such marker: this is
    ordinary code that the translator never calls. *)
let rec eval e (env : env) =
  match e with
  | EVar (x, t) -> env t x
  | EInt n -> DVal (VInt n)
  | EBool b -> DVal (VBool b)
  | ECtor (_, id) -> DVal (VCtor id)
  | EMkRec (_, args) -> DVal (VRecord (eval_args args env))
  | EProj (e0, f) -> (
      match field_value (as_record (eval e0 env)) f with
      | Some v -> DVal v
      | None -> DVal (VBool false))
  | EAdd (a, b) -> DVal (VInt (as_int (eval a env) + as_int (eval b env)))
  | ESub (a, b) -> DVal (VInt (as_int (eval a env) - as_int (eval b env)))
  | EMul (a, b) -> DVal (VInt (as_int (eval a env) * as_int (eval b env)))
  | EEq (a, b) -> DVal (VBool (denot_eq (eval a env) (eval b env)))
  | ELe (a, b) -> DVal (VBool (as_int (eval a env) <= as_int (eval b env)))
  | ELt (a, b) -> DVal (VBool (as_int (eval a env) < as_int (eval b env)))
  | EAnd (a, b) -> DVal (VBool (as_bool (eval a env) && as_bool (eval b env)))
  | EOr (a, b) -> DVal (VBool (as_bool (eval a env) || as_bool (eval b env)))
  | ENot a -> DVal (VBool (not (as_bool (eval a env))))
  | EEmptyBag _ -> DBag Bag.empty
  | ESingle (k, e0) -> DBag (Bag.single k (as_value (eval e0 env)))
  | EBagUnion (a, b) -> DBag (Bag.union (as_bag (eval a env)) (as_bag (eval b env)))
  | EBagDiff (a, b) -> DBag (Bag.diff (as_bag (eval a env)) (as_bag (eval b env)))
  | EBagSubset (a, b) ->
      DVal (VBool (Bag.subset (as_bag (eval a env)) (as_bag (eval b env))))
  | ENilList _ -> DList []
  | ESnoc (l, e0) -> DList (as_seq (eval l env) @ [ as_value (eval e0 env) ])
  | EAppendList (a, b) -> DList (as_seq (eval a env) @ as_seq (eval b env))
  | EDiffList (a, b) ->
      DList (List_ops.list_diff (as_seq (eval a env)) (as_seq (eval b env)))
  | ESubList (a, b) ->
      DVal (VBool (List_ops.sub_multiset (as_seq (eval a env)) (as_seq (eval b env))))

(** [eval], one record field at a time. *)
and eval_args args env =
  List.map (fun (n, e) -> (n, as_value (eval e env))) args

(** A boolean expression holds under a binding. This is [Type[e] = Bool] together with
    [e<b> = True], as Definitions 6 and 14 use it. *)
let holds e env = as_bool (eval e env)

(** [VAR[e]] of Chapter 2. The list may repeat a variable; only membership is ever used. *)
let rec free_vars e : ctx =
  match e with
  | EVar (x, t) -> [ (x, t) ]
  | EInt _ | EBool _ | ECtor _ | EEmptyBag _ | ENilList _ -> []
  | EMkRec (_, args) -> Util.flat_map (fun q -> free_vars (snd q)) args
  | EProj (e0, _) -> free_vars e0
  | ENot a | ESingle (_, a) -> free_vars a
  | EAdd (a, b)
  | ESub (a, b)
  | EMul (a, b)
  | EEq (a, b)
  | ELe (a, b)
  | ELt (a, b)
  | EAnd (a, b)
  | EOr (a, b)
  | EBagUnion (a, b)
  | EBagDiff (a, b)
  | EBagSubset (a, b)
  | ESnoc (a, b)
  | EAppendList (a, b)
  | EDiffList (a, b)
  | ESubList (a, b) ->
      free_vars a @ free_vars b

(** Decidable equality on a context entry, and membership in a context. *)
let ctx_entry_eq (q1 : string * expr_ty) (q2 : string * expr_ty) : bool =
  Util.string_eq (fst q1) (fst q2) && expr_ty_eq (snd q1) (snd q2)

let rec mem_ctx (q : string * expr_ty) (g : ctx) : bool =
  match g with [] -> false | e :: rest -> ctx_entry_eq q e || mem_ctx q rest

(** An expression is scoped in [g] when every variable it mentions is a variable of [g] at the
    sort [g] gives it.

    This is check 7 of [Implementation/docs/InputFormat.md] §4.3, [Var(t) ⊆ V], which
    [Thesis/docs/LeanFormalization.md] §4.6 records as provable from the typing but not stated
    in [Proof/]. Here it is neither: it is checked at the boundary and then used. *)
let scoped_in (g : ctx) e = Util.all (fun q -> mem_ctx q g) (free_vars e)

(** The conjunction of a list of boolean expressions, right-nested.

    The empty conjunction is [true] and a one-element one is that element, so the emitted text
    carries no redundant [&& true]. Obligation 3 of [Implementation/docs/Plan.md] §4 is this
    fold: Definition 14's bounded [forall p in pre(t)] becomes a finite conjunction when the
    translation runs, and the term language needs no quantifier. *)
let rec and_all = function
  | [] -> EBool true
  | [ e ] -> e
  | e :: rest -> EAnd (e, and_all rest)

(** The union of a list of bag expressions of the color [c], right-nested. *)
let rec union_all c = function
  | [] -> EEmptyBag c
  | [ e ] -> e
  | e :: rest -> EBagUnion (e, union_all c rest)
