open Base
open Ast.Syntax

module Env = struct
  module StringMap = Map.M (String)
  type t = type_signature StringMap.t

  let empty: t = Map.empty (module String)
  let set (m: t) (k: String.t) (v: type_signature): t = Map.set m ~key:k ~data:v
  let find (m: t) (k: String.t): type_signature Option.t = Map.find m k
  let remove (m: t) (k: String.t): t = Map.remove m k
end

type location = Lexing.position * Lexing.position

type err =
  | VariableNotFound of { id: string; location: location }
  | WrongNumberOfArgs of { expected: int; recieved: int; location: location }
  | Unimplemented

let err_to_string e =
  match e with
  | VariableNotFound { id; _ } -> Printf.sprintf "Variable '%s' not found" id
  | WrongNumberOfArgs _ -> "Unexpected number of arguments"
  | Unimplemented -> "Unimplemented"

let instantiate (t: type_signature) =
  match t.item with
  | TypeIdent _ -> Ok t
  | _ -> Error Unimplemented

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

let rec infer (env: Env.t) (expr: expression) =
  match expr.item with
  | ExprIdent id ->
      Map.find env id
      |> Result.of_option ~error:(VariableNotFound { id; location = expr.location })
      |> Result.bind ~f:instantiate
  | ExprFn (param_ids, body_expr) ->
      let param_types = List.map ~f:(fun _ -> new_type_var ()) param_ids in
      let fn_env = List.fold2_exn ~init:env ~f:Env.set param_ids param_types in
      let return_type = infer fn_env body_expr in
      Result.map ~f:(arrow_type param_types) return_type
  | _ -> Error Unimplemented
