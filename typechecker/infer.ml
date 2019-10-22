open Base
open Ast.Syntax

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
  | FailedOccurCheck
  | UnequalConstructorLengths
  | TypeMismatch
  | Unimplemented of string

let err_to_string e =
  match e with
  | VariableNotFound { id; _ } -> Printf.sprintf "Variable '%s' not found" id
  | FailedOccurCheck -> "Failed Occur Check"
  | UnequalConstructorLengths -> "Unequal Constructor Lengths"
  | TypeMismatch -> "Type Mismatch"
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
  | (name, TypeVar m) when String.equal name m ->
      Ok Substitution.null
  
  (* If name is found in the free type variables of t, then fail *)
  | (name, _) when Set.mem (Substitution.free_type_vars t) name ->
      Error FailedOccurCheck
  
  (* Otherwise substitute name with the type *)
  | _ -> Ok (Substitution.singleton name t)

let locate p = { item = p; location = (Lexing.dummy_pos, Lexing.dummy_pos) }

let%test_module "var_bind" = (module struct
  let%expect_test "name and type var are equal" =
    match var_bind "x" (locate (TypeVar "x")) with
    | Ok subs -> Stdio.printf "%i\n" (Map.length subs)
    | _ -> Stdio.print_endline "Error";
    [%expect {| 0 |}]
  
  let%expect_test "free type variables return error" =
    let t = TypeArrow (locate (TypeVar "x"), locate (TypeVar "y")) |> locate in
    match var_bind "x" t with
    | Ok subs -> Stdio.printf "%i\n" (Map.length subs)
    | _ -> Stdio.print_endline "Error";
    [%expect {| Error |}]
  
  let%expect_test "x can be substitued" =
    match var_bind "x" (locate (TypeIdent "Int")) with
    | Ok subs -> Map.length subs |> Int.to_string |> Stdio.print_endline
    | _ -> Stdio.print_endline "Error";
    [%expect {| 1 |}]
end)

let rec unify (t1: type_signature) (t2: type_signature) =
  match (t1.item, t2.item) with
  | (TypeArrow (arg1, ret1), TypeArrow (arg2, ret2)) ->
      unify arg1 arg2 |> Result.bind ~f:(fun s1 ->
        unify (Substitution.apply s1 ret1) (Substitution.apply s1 ret2)
        |> Result.map ~f:(fun s2 -> Substitution.compose s2 s1)
      )

  | (_, TypeVar n) -> var_bind n t1
  | (TypeVar n, _) -> var_bind n t2

  | (TypeIdent x, TypeIdent y) when String.equal x y ->
      Ok Substitution.null

  | (TypeConstructor (x, x_args), TypeConstructor (y, y_args)) when String.equal x y -> (
      let folder acc x_ y_ =
        match acc with
        | Ok s1 ->
            unify (Substitution.apply s1 x_) (Substitution.apply s1 y_)
            |> Result.map ~f:(fun s2 -> Substitution.compose s2 s1)
        | e -> e
      in
      let s = List.fold2 ~f:folder ~init:(Ok Substitution.null) x_args y_args in
      match s with
      | Ok (Ok subs) -> Ok subs
      | Ok e -> e
      | Unequal_lengths -> Error UnequalConstructorLengths
  )
  | _ -> Error TypeMismatch

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
    |> Result.iter ~f:(Stdio.printf "%d\n");
    [%expect {| 0 |}]
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
