open Base
open Ast.Syntax

open Result.Let_syntax

module StringMap = Map.M (String)
module StringSet = Set.M (String)

module Env = struct
  type t = type_signature StringMap.t

  let empty: t = Map.empty (module String)
  let set (m: t) (k: String.t) (v: type_signature): t = Map.set m ~key:k ~data:v
  let find (m: t) (k: String.t): type_signature Option.t = Map.find m k
  let remove (m: t) (k: String.t): t = Map.remove m k
end

module Substitution = struct
  type t = type_signature StringMap.t

  let null : t = Map.empty (module String)
  let singleton s t : t = Map.singleton (module String) s t

  let to_string (s: t) =
    Map.to_alist s
    |> List.map ~f:(fun (v, t) -> Printf.sprintf "%s = %s" v (type_signature_to_string t))
    |> String.concat ~sep:", "

  (** Apply substitutions to a type *)
  let rec apply (subst: t) (t: type_signature) =
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

  (** Given two substitutions, merge them and try to apply any possible substitutions *)
  let compose (s1: t) (s2: t) =
    Map.merge
      ~f:(fun ~key:_ x -> match x with `Left v | `Right v | `Both (_, v) -> Some v)
      (Map.map ~f:(apply s1) s2)
      s1

  let rec free_type_vars (t: type_signature): StringSet.t =
    match t.item with
    | TypeVar a -> Set.singleton (module String) a
    | TypeArrow (t1, t2) ->
        Set.union (free_type_vars t1) (free_type_vars t2)
    | TypeTuple ts ->
        ts |> List.map ~f:free_type_vars |> Set.union_list (module String)
    | _ -> Set.empty (module String)
end

type location = Lexing.position * Lexing.position

type err =
  | VariableNotFound of { id: string; location: location }
  | InfiniteType
  | UnequalLengths
  | TypeMismatch of type_signature * type_signature
  | Unimplemented of string

let err_to_string e =
  match e with
  | VariableNotFound { id; _ } -> Printf.sprintf "Variable '%s' not found" id
  | InfiniteType -> "Infinite Type"
  | UnequalLengths -> "Unequal Lengths"
  | TypeMismatch (a, b) ->
      Printf.sprintf "Cannot unify '%s' with '%s'"
        (type_signature_to_string a)
        (type_signature_to_string b)
  | Unimplemented s -> Printf.sprintf "Unimplemented: %s" s

let instantiate (t: type_signature) =
  match t.item with
  | TypeIdent _ -> Ok t
  | _ -> Error (Unimplemented "instantiate")

let locate (p: 'a) : 'a located = { item = p; location = (Lexing.dummy_pos, Lexing.dummy_pos) }

(* This is used to keep track of which type is which *)
let last_id = ref 0
let next_id () =
  let id = !last_id in
  last_id := id + 1;
  id

(** Create a new type variable with dummy position *)
let new_type_var () : type_signature =
  TypeVar (Printf.sprintf "t%d" (next_id ())) |> locate

(** Create a TypeArrow from a list of parameter types *)
let arrow_type param_types return_type =
  List.fold_right ~init:return_type ~f:(fun l r -> locate (TypeArrow (l, r))) param_types

let generalise t = t

(** Given a type variable's name, and another type, get the substitutions *)
let var_bind name t =
  match (name, t.item) with
  (* If name is the same as a TypeVar then we don't know any substitutions *)
  | name, TypeVar m when String.equal name m ->
      Ok Substitution.null

  (* If name is found in the free type variables of t, then it fails the occurs check *)
  | name, _ when Set.mem (Substitution.free_type_vars t) name ->
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
    |> Option.map ~f:type_signature_to_string
    |> Option.iter ~f:(Stdio.print_endline);
    [%expect {| Int |}]
end)

(** Given two types, determine if they can unify and return any possible
    type variable substitutions *)
let rec unify (t1: type_signature) (t2: type_signature) =
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
    let%map s2 = unify (Substitution.apply s1 x) (Substitution.apply s1 y) in
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
    |> Option.map ~f:type_signature_to_string
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
    |> Option.map ~f:type_signature_to_string
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

let rec infer (env: Env.t) (expr: expression) =
  match expr.item with
  | ExprIdent id -> (
      match (Map.find env id) with
      | Some (t) -> instantiate t
      | None -> Error (VariableNotFound { id; location = expr.location })
  )
  | ExprFn (param_ids, body_expr) -> (
      let param_types = List.map ~f:(fun _ -> new_type_var ()) param_ids in
      let fn_env = List.fold2_exn ~init:env ~f:Env.set param_ids param_types in
      match infer fn_env body_expr with
      | Ok return_type -> Ok ((arrow_type param_types) return_type)
      | e -> e
  )
  | ExprValBinding (pattern, value_expr, body_expr) -> (
    match pattern.item with
    | PatternVar var_name -> (
      infer env value_expr
      |> Result.map ~f:generalise
      |> Result.bind ~f:(fun generalised_t ->
        infer (Env.set env var_name generalised_t) body_expr
      )
    )
    | _ -> Error (Unimplemented "infer val binding for pattern")
  )
  | ExprApply (_fn_expr, _args) -> (

    Error (Unimplemented "infer apply")
  )
  | _ -> Error (Unimplemented "infer")
