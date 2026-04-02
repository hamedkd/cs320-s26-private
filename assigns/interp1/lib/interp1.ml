
(* Syntax *)

type ty = Ast.Interp1.ty =
  | Unit
  | Bool
  | Int
  | Fun of ty * ty

type bop = Ast.Interp1.bop =
  | Add | Sub | Mul | Div | Mod
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or

type expr = Ast.Interp1.expr =
  | Unit
  | Bool of bool
  | Int of int
  | Var of string
  | Let of string * expr * expr
  | LetRec of {
      name : string;
      arg : string;
      arg_ty : ty;
      out_ty : ty;
      binding : expr;
      body : expr;
    }
  | If of expr * expr * expr
  | Fun of string * ty * expr
  | App of expr * expr
  | Bop of bop * expr * expr
  | Negate of expr
  | Assert of expr

(* Environments *)

module Env = Map.Make (String)

(* Values *)

type value =
  | Unit
  | Bool of bool
  | Int of int
  | Clos of value Env.t * string option * expr

(* Contexts *)

type ctxt = ty Env.t

(* Dynamic Environments *)

type dyn_env = value Env.t

(* Type Checking *)

let type_of (ctxt : ctxt) (e : expr) : ty option =
  let rec go (ctx : ctxt) (expr : expr) : ty option =
    match expr with
    | Unit -> Some Unit
    | Bool _ -> Some Bool
    | Int _ -> Some Int
    | Var x -> Env.find_opt x ctx
    | Assert e ->
      (match go ctx e with
       | Some Bool -> Some Unit
       | _ -> None)
    | Negate e ->
      (match go ctx e with
       | Some Int -> Some Int
       | _ -> None)
    | Bop (op, e1, e2) ->
      (match op with
       | Add | Sub | Mul | Div | Mod ->
         (match go ctx e1, go ctx e2 with
          | Some Int, Some Int -> Some Int
          | _ -> None)
       | Eq | Neq | Lt | Lte | Gt | Gte ->
         (match go ctx e1, go ctx e2 with
          | Some t1, Some t2 when t1 = t2 -> Some Bool
          | _ -> None)
       | And | Or ->
         (match go ctx e1, go ctx e2 with
          | Some Bool, Some Bool -> Some Bool
          | _ -> None))
    | If (e1, e2, e3) ->
      (match go ctx e1, go ctx e2, go ctx e3 with
       | Some Bool, Some t2, Some t3 when t2 = t3 -> Some t2
       | _ -> None)
    | Fun (x, ty, body) ->
      let ctx' = Env.add x ty ctx in
      (match go ctx' body with
       | Some ty2 -> Some (Fun (ty, ty2))
       | None -> None)
    | App (e1, e2) ->
      (match go ctx e1, go ctx e2 with
       | Some (Fun (t2, t)), Some t2' when t2 = t2' -> Some t
       | _ -> None)
    | Let (x, e1, e2) ->
      (match go ctx e1 with
       | Some t1 ->
         let ctx' = Env.add x t1 ctx in
         go ctx' e2
       | None -> None)
    | LetRec { name; arg; arg_ty; out_ty; binding; body } ->
      let ctx1 = Env.add name ((Fun (arg_ty, out_ty)) : ty) ctx in
      let ctx2 = Env.add arg arg_ty ctx1 in
      (match go ctx2 binding with
       | Some t when t = out_ty -> go ctx1 body
       | _ -> None)
  in go ctxt e
(* Evaluation *)

exception Div_by_zero
exception Assert_fail

let eval (env : dyn_env) (e : expr) : value =
   let rec go (env : dyn_env) (expr : expr) : value =
    match expr with
    | Unit -> Unit
    | Bool b -> Bool b
    | Int n -> Int n
    | Var x -> Env.find x env
    | Assert e ->
      (match go env e with
       | Bool true -> Unit
       | Bool false -> raise Assert_fail
       | _ -> assert false)
    | Negate e ->
      (match go env e with
       | Int n -> Int (-n)
       | _ -> assert false)
    | Bop (op, e1, e2) ->
      (match op with
       | Add ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Int (v1 + v2)
          | _ -> assert false)
       | Sub ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Int (v1 - v2)
          | _ -> assert false)
       | Mul ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Int (v1 * v2)
          | _ -> assert false)
       | Div ->
         let v2 = go env e2 in
         (match v2 with
          | Int 0 -> raise Div_by_zero
          | Int n2 ->
            (match go env e1 with
             | Int n1 -> Int (n1 / n2)
             | _ -> assert false)
          | _ -> assert false)
       | Mod ->
         let v2 = go env e2 in
         (match v2 with
          | Int 0 -> raise Div_by_zero
          | Int n2 ->
            (match go env e1 with
             | Int n1 -> Int (n1 mod n2)
             | _ -> assert false)
          | _ -> assert false)
       | Eq ->
         let v1 = go env e1 in
         let v2 = go env e2 in
         Bool (v1 = v2)
       | Neq ->
         let v1 = go env e1 in
         let v2 = go env e2 in
         Bool (v1 <> v2)
       | Lt ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Bool (v1 < v2)
          | _ -> assert false)
       | Lte ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Bool (v1 <= v2)
          | _ -> assert false)
       | Gt ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Bool (v1 > v2)
          | _ -> assert false)
       | Gte ->
         (match go env e1, go env e2 with
          | Int v1, Int v2 -> Bool (v1 >= v2)
          | _ -> assert false)
       | And ->
         (match go env e1 with
          | Bool true -> go env e2
          | Bool false -> Bool false
          | _ -> assert false)
       | Or ->
         (match go env e1 with
          | Bool true -> Bool true
          | Bool false -> go env e2
          | _ -> assert false))
    | If (e1, e2, e3) ->
      (match go env e1 with
       | Bool true -> go env e2
       | Bool false -> go env e3
       | _ -> assert false)
    | Fun (x, ty, body) ->
      Clos (env, None, Fun (x, ty, body))
    | App (e1, e2) ->
      (match go env e1 with
       | Clos (clos_env, None, Fun (x, _ty, body)) ->
         let v2 = go env e2 in
         let env' = Env.add x v2 clos_env in
         go env' body
       | Clos (clos_env, Some f, Fun (x, _ty, body)) as clos ->
         let v2 = go env e2 in
         let env' = Env.add f clos (Env.add x v2 clos_env) in
         go env' body
       | _ -> assert false)
    | Let (x, e1, e2) ->
      let v1 = go env e1 in
      let env' = Env.add x v1 env in
      go env' e2
    | LetRec { name; arg; arg_ty; binding; body; _ } ->
      let clos = Clos (env, Some name, Fun (arg, arg_ty, binding)) in
      let env' = Env.add name clos env in
      go env' body
  in  go env e

(* Interpretation *)

let interp ~(filename : string) : value option =
  let e_ty =
    match Syntax.parse ~filename with
    | Ok p -> Ast.Interp1.expr_of_prog p
    | Error e -> Error e
  in
  match e_ty with
  | Ok e -> (
      match type_of Env.empty e with
      | Some _ -> Some (eval Env.empty e)
      | _ ->
        let _type_error_msg = print_endline "Type error"
        in None
    )
  | Error e ->
    let _parse_error_msg =
      In_channel.with_open_text filename
        (fun ic ->
           let text = In_channel.input_all ic in
           let msg = Error_msg.to_string ~filename ~text e in
           Format.eprintf "%s" msg)
    in None
