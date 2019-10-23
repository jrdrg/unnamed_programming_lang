open Base
open Ast.Syntax

open Result.Let_syntax

module StringMap = Map.M (String)
module StringSet = Set.M (String)

module rec Substitution: sig 
  type t = Type.t StringMap.t
  val null: t
  val singleton: string -> Type.t -> t
  val to_string: t -> string
  val compose: t -> t -> t
end = struct
  type t = Type.t StringMap.t

  let null : t = Map.empty (module String)
  let singleton s t : t = Map.singleton (module String) s t

  let to_string (s: t) =
    Map.to_alist s
    |> List.map ~f:(fun (v, t) -> Printf.sprintf "%s = %s" v (Type.to_string t))
    |> String.concat ~sep:", "


  (** Given two substitutions, merge them and try to apply any possible substitutions *)
  let compose (s1: t) (s2: t) =
    Map.merge
      ~f:(fun ~key:_ x -> match x with `Left v | `Right v | `Both (_, v) -> Some v)
      (Map.map ~f:(Type.apply s1) s2)
      s1

end

and Scheme: sig 
  type t = Forall of string list * Type.t
  val apply: Substitution.t -> t -> t
  val free_type_vars: t -> StringSet.t
end = struct
  type t = Forall of string list * Type.t

  let apply (subs: Substitution.t) (scheme: t) =
    match scheme with
    | Forall (vars, t) ->
      let subs_ = vars |> List.fold ~init:subs ~f:Map.remove in
      Forall (vars, Type.apply subs_ t)
  
  let free_type_vars (scheme: t): StringSet.t =
    match scheme with
    | Forall (vars, t) -> 
      let ftv_s = Set.of_list (module String) vars in
      let ftv_t = Type.free_type_vars t in
      Set.diff ftv_s ftv_t
end

and Env: sig 
  type t = Scheme.t StringMap.t
  val empty: t
  val set: t -> string -> Scheme.t -> t
  val find: t -> string -> Scheme.t option 
  val remove: t -> string -> t
  val apply: Substitution.t -> t -> t
  val free_type_vars: t -> StringSet.t
end = struct
  type t = Scheme.t StringMap.t

  let empty: t = Map.empty (module String)
  let set (m: t) (k: String.t) (v: Scheme.t): t = Map.set m ~key:k ~data:v
  let find (m: t) (k: String.t): Scheme.t Option.t = Map.find m k
  let remove (m: t) (k: String.t): t = Map.remove m k

  let apply (subs: Substitution.t) (env: t): t =
    env |> Map.map ~f:(Scheme.apply subs)

  let free_type_vars (env: t): StringSet.t =
    Map.data env 
    |> List.fold ~f:(fun set scheme -> Set.union set (Scheme.free_type_vars scheme)) ~init:(Set.empty (module String))
end

and Type: sig 
  type t = type_signature
  val apply: Substitution.t -> t -> t
  val free_type_vars: t -> StringSet.t
  val to_string: t -> string
end = struct
  type t = type_signature

  (** Apply substitutions to a type *)
  let rec apply (subst: Substitution.t) (t: t) =
    match t.item with
    | TypeVar v ->
      Map.find subst v |> Option.value ~default:t
    | TypeArrow (t1, t2) -> {
        item = TypeArrow (apply subst t1, apply subst t2);
        location = t.location
      }
    | TypeTuple ts -> {
        item = TypeTuple (List.map ~f:(apply subst) ts);
        location = t.location;
      }
    | TypeConstructor (n, ts) -> {
        item = TypeConstructor (n, List.map ~f:(apply subst) ts);
        location = t.location;
      }
    | _ -> t

  let rec free_type_vars (t: t): StringSet.t =
    match t.item with
    | TypeVar a -> Set.singleton (module String) a
    | TypeArrow (t1, t2) ->
        Set.union (free_type_vars t1) (free_type_vars t2)
    | TypeTuple ts ->
        ts |> List.map ~f:free_type_vars |> Set.union_list (module String)
    | _ -> Set.empty (module String)

  let to_string = type_signature_to_string

end

type location = Lexing.position * Lexing.position

type err =
  | VariableNotFound of { id: string; location: location }
  | InfiniteType
  | UnequalLengths
  | TypeMismatch of Type.t * Type.t
  | Unimplemented of string

let err_to_string e =
  match e with
  | VariableNotFound { id; _ } -> Printf.sprintf "Variable '%s' not found" id
  | InfiniteType -> "Infinite Type"
  | UnequalLengths -> "Unequal Lengths"
  | TypeMismatch (a, b) ->
      Printf.sprintf "Cannot unify '%s' with '%s'"
        (Type.to_string a)
        (Type.to_string b)
  | Unimplemented s -> Printf.sprintf "Unimplemented: %s" s

let locate (p: 'a) : 'a located = { item = p; location = (Lexing.dummy_pos, Lexing.dummy_pos) }

(* This is used to keep track of which type is which *)
let last_id = ref 0
let next_id () =
  let id = !last_id in
  last_id := id + 1;
  id

(** Create a new type variable with dummy position *)
let new_type_var () : Type.t =
  TypeVar (Printf.sprintf "t%d" (next_id ())) |> locate

let generalise (env: Env.t) (t: Type.t) =
  let ftv_e = Env.free_type_vars env in
  let ftv_t = Type.free_type_vars t in
  let vars = Set.diff ftv_t ftv_e |> Set.to_list in
  Scheme.Forall (vars, t)

let instantiate (scheme: Scheme.t) =
  match scheme with
  | Forall (_, ({ item = TypeIdent _ } as t)) -> Ok t
  | _ -> Error (Unimplemented "instantiate")

(** Given a type variable's name, and another type, get the substitutions *)
let var_bind name t =
  match (name, t.item) with
  (* If name is the same as a TypeVar then we don't know any substitutions *)
  | name, TypeVar m when String.equal name m ->
      Ok Substitution.null

  (* If name is found in the free type variables of t, then it fails the occurs check *)
  | name, _ when Set.mem (Type.free_type_vars t) name ->
      Error InfiniteType

  (* Otherwise substitute name with the type *)
  | _ -> Ok (Substitution.singleton name t)

let locate p = { item = p; location = (Lexing.dummy_pos, Lexing.dummy_pos) }

let%test_module "var_bind" = (module struct
  let%expect_test "name and type var are equal" =
    var_bind "x" (locate (TypeVar "x"))
    |> Result.map ~f:(Map.length)
    |> Result.iter ~f:(Stdio.printf "%i");
    [%expect {| 0 |}]

  let%expect_test "free type variables return error" =
    let t = TypeArrow (locate (TypeVar "x"), locate (TypeVar "y")) |> locate in
    var_bind "x" t
    |> Result.iter_error ~f:(fun _ -> Stdio.printf "Error");
    [%expect {| Error |}]

  let%expect_test "x can be substitued" =
    var_bind "x" (locate (TypeIdent "Int"))
    |> Result.ok
    |> Option.bind ~f:(fun subs -> Map.find subs "x")
    |> Option.map ~f:Type.to_string
    |> Option.iter ~f:(Stdio.print_endline);
    [%expect {| Int |}]
end)

(** Given two types, determine if they can unify and return any possible
    type variable substitutions *)
let rec unify (t1: Type.t) (t2: Type.t) =
  match (t1.item, t2.item) with
  | TypeArrow (arg1, ret1), TypeArrow (arg2, ret2) ->
      unify_lists [arg1; ret1] [arg2; ret2]

  | _, TypeVar n -> var_bind n t1
  | TypeVar n, _ -> var_bind n t2

  | TypeIdent x, TypeIdent y when String.equal x y ->
      Ok Substitution.null

  | TypeConstructor (x, x_args), TypeConstructor (y, y_args)
    when String.equal x y ->
      unify_lists x_args y_args

  | TypeTuple xs, TypeTuple ys -> unify_lists xs ys

  | _ -> Error (TypeMismatch (t1, t2))

(** Given two lists of types, attempt to unify each element pairwise and
    aggregate the substitution mapping *)
and unify_lists xs ys =
  let folder acc x y =
    let%bind s1 = acc in
    let%map s2 = unify (Type.apply s1 x) (Type.apply s1 y) in
    Substitution.compose s2 s1
  in
  match List.fold2 ~f:folder ~init:(Ok Substitution.null) xs ys with
  | Ok x -> x
  | _ -> Error UnequalLengths

let%test_module "unify" = (module struct
  let%expect_test "Can unify ident with var" =
    let t1 = locate (TypeIdent "Test") in
    let t2 = locate (TypeVar "x") in
    unify t1 t2
    |> Result.ok
    |> Option.bind ~f:(fun subs -> Map.find subs "x")
    |> Option.map ~f:Type.to_string
    |> Option.iter ~f:(Stdio.print_endline);
    [%expect {| Test |}]

  let%expect_test "Can unify two arrows that are the same" =
    let t1 = locate (TypeArrow (locate (TypeIdent "Int"), locate (TypeIdent "String"))) in
    let t2 = locate (TypeArrow (locate (TypeIdent "Int"), locate (TypeIdent "String"))) in
    unify t1 t2
    |> Result.map ~f:Map.length
    |> Result.iter ~f:(Stdio.printf "%d");
    [%expect {| 0 |}]

  let%expect_test "Can unify two arrows complex arrows" =
  (* a -> String -> Bool, Int -> b -> Bool *)
    let t1 = locate (TypeArrow (locate (TypeVar "a"), locate (TypeArrow (locate (TypeIdent "String"), locate (TypeIdent "Bool"))))) in
    let t2 = locate (TypeArrow (locate (TypeIdent "Int"), locate (TypeArrow (locate (TypeVar "b"), locate (TypeIdent "Bool"))))) in
    unify t1 t2
    |> Result.iter ~f:(fun s -> Substitution.to_string s |> Stdio.print_endline);
    [%expect {| a = Int, b = String |}]

  let%expect_test "Does not unify two arrows that are different" =
    let t1 = locate (TypeArrow (locate (TypeIdent "Int"), locate (TypeIdent "String"))) in
    let t2 = locate (TypeArrow (locate (TypeIdent "Bool"), locate (TypeIdent "String"))) in
    unify t1 t2
    |> Result.map_error ~f:err_to_string
    |> Result.iter_error ~f:Stdio.print_endline;
    [%expect {| Cannot unify 'Int' with 'Bool' |}]

  let%expect_test "Can unify a generic and specialised arrow" =
    let t1 = locate (TypeArrow (locate (TypeVar "x"), locate (TypeIdent "String"))) in
    let t2 = locate (TypeArrow (locate (TypeIdent "Test"), locate (TypeIdent "String"))) in
    unify t1 t2
    |> Result.ok
    |> Option.bind ~f:(fun subs -> Map.find subs "x")
    |> Option.map ~f:Type.to_string
    |> Option.iter ~f:(Stdio.print_endline);
    [%expect {| Test |}]

  let%expect_test "Can unify a generic and specialised constructor" =
    let args1 = [locate (TypeVar "a"); locate (TypeIdent "Bool"); locate (TypeVar "c")] in
    let args2 = [locate (TypeIdent "Int"); locate (TypeVar "b"); locate (TypeIdent "String")] in
    let t1 = locate (TypeConstructor ("Test", args1)) in
    let t2 = locate (TypeConstructor ("Test", args2)) in
    unify t1 t2
    |> Result.iter ~f:(fun s -> Substitution.to_string s |> Stdio.print_endline);
    [%expect {| a = Int, b = Bool, c = String |}]

  let%expect_test "Can unify a generic and specialised tuple" =
    let xs = [locate (TypeVar "a"); locate (TypeIdent "Bool"); locate (TypeVar "c")] in
    let ys = [locate (TypeIdent "Int"); locate (TypeVar "b"); locate (TypeIdent "String")] in
    let t1 = locate (TypeTuple xs) in
    let t2 = locate (TypeTuple ys) in
    unify t1 t2
    |> Result.iter ~f:(fun s -> Substitution.to_string s |> Stdio.print_endline);
    [%expect {| a = Int, b = Bool, c = String |}]
end)

(** Create a TypeArrow from a list of parameter types *)

let arrow_type subs param_types return_type =
  List.fold_right
    ~init:return_type
    ~f:(fun l r ->
      locate (TypeArrow (Type.apply subs l, r))
    )
    param_types

let rec infer (env: Env.t) (expr: expression): ((Substitution.t * Type.t), err) Result.t =
  match expr.item with
  | ExprIdent id -> (
      match (Map.find env id) with
      | Some (t) -> instantiate t |> Result.map ~f:(fun t_ -> (Substitution.null, t_))
      | None -> Error (VariableNotFound { id; location = expr.location })
  )
  | ExprFn (param_ids, body_expr) -> (
      let (fn_env, param_types) = List.fold_map ~init:env ~f:(fun cur_env id -> (
        let tv = new_type_var () in 
        (Map.set cur_env id (Forall ([], tv)), tv)
      )) param_ids in
      let%bind (subs, return_type) = infer fn_env body_expr in
      Ok (subs, arrow_type subs param_types return_type)
  )
  | ExprValBinding (pattern, value_expr, body_expr) -> (
    match pattern.item with
    | PatternVar var_name -> (
      let%bind (value_subs, value_type) = infer env value_expr in
      let env_ = Env.apply value_subs env in
      let value_type_ = generalise env_ value_type in
      let%bind (body_subs, body_type) = infer (Env.set env_ var_name value_type_) body_expr in
      Ok (Substitution.compose value_subs body_subs, body_type)
    )
    | _ -> Error (Unimplemented "infer val binding for pattern")
  )
  | ExprApply (fn_expr, args) -> (
    let%bind (fn_subs, fn_type) = infer env fn_expr in


    Error (Unimplemented "infer apply")
  )
  | _ -> Error (Unimplemented "infer")
