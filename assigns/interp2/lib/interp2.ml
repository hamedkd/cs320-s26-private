open Utils
module Error_msg = Error_msg

(* SYNTAX
   ----------------------------------------------------------------------
*)

type ty = Ast.Interp2.ty =
    | TUnit
    | TBool
    | TInt
    | TInt_list
    | TFun of ty * ty
    | TTuple of ty list

let rec pp_ty ppf ty =
  let open Fmt in
  let pp_parens ppf ty =
    match ty with
    | TFun (_, _)
    | TTuple _
    | _ -> pp_ty ppf ty
  in
  match ty with
  | TUnit -> pf ppf "unit"
  | TBool -> pf ppf "bool"
  | TInt -> pf ppf "int"
  | TFun (t1, t2) -> pf ppf "%a -> %a" pp_parens t1 pp_ty t2
  | TTuple ts -> list ~sep:(Fmt.any " * ") pp_ty ppf ts
  | TInt_list -> pf ppf "int list"

type _pattern = Ast.Interp2._pattern =
  | PUnit
  | PBool of bool
  | PInt of int
  | PNil
  | PCons of pattern * pattern
  | PTuple of pattern list
  | PVar of string
and pattern = Ast.Interp2.pattern =
  {
    pos : pos;
    pattern : _pattern;
  }

type bop = Ast.Interp2.bop =
  | Add | Sub | Mul | Div | Mod
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | Cons

type _expr = Ast.Interp2._expr =
  | Unit
  | Bool of bool
  | Int of int
  | Var of string
  | Nil
  | Assert of expr
  | Negate of expr
  | Tuple of expr list
  | Bop of bop * expr * expr
  | If of expr * expr * expr
  | Fun of (string * ty) list * expr
  | App of expr * expr list
  | Let of
      {
        is_rec : bool;
        name : string;
        args : (string * ty) list;
        annot : ty option;
        binding : expr;
        body : expr;
      }
  | Match of expr * (pattern * expr) list
and expr = Ast.Interp2.expr =
  {
    pos : pos;
    expr : _expr;
  }

type _stmt = Ast.Interp2._stmt =
  | SLet of {
      is_rec : bool;
      name : string;
      args : (string * ty) list;
      annot : ty option;
      binding : expr;
    }
and stmt = Ast.Interp2.stmt =
  {
    pos : pos;
    stmt : _stmt;
  }

type prog = stmt list

module Env = Map.Make(String)

(* TYPE ERRORS
   ----------------------------------------------------------------------
*)

let unknown_var pos x = Error_msg.mk pos (Format.asprintf "Unbound value %s" x)

let exp_ty pos t1 t2 =
  let msg =
    Format.asprintf
      "This expression has type %a but an expression was expected of type %a"
      pp_ty t1 pp_ty t2
  in Error_msg.mk pos msg

let exp_pat pos t1 t2 =
  let msg =
    Format.asprintf
      "This pattern matches values of type %a but a pattern was expected which matches values of type %a"
      pp_ty t1 pp_ty t2
  in Error_msg.mk pos msg

let exp_tuple_pat pos t =
  let msg =
    Format.asprintf
      "This pattern matches values of a tuple type but a pattern was expected which matches values of type %a"
      pp_ty t
  in Error_msg.mk pos msg

let exp_diff_tuple_pat pos ty =
  let msg =
    Format.asprintf
      "This pattern matches values of a tuple type but a pattern was expected which matches values of a different tuple type %a"
      pp_ty ty
  in Error_msg.mk pos msg

let not_func pos ty =
  let msg =
    Format.asprintf
      "This expression has type %a. This is not a function; it cannot be applied"
      pp_ty ty
  in Error_msg.mk pos msg

let too_many_args pos ty =
  let msg =
    Format.asprintf
      "This function has type %a. It is applied to to many arguments"
      pp_ty ty
  in Error_msg.mk pos msg

let missing_rec_annot pos =
  Error_msg.mk pos "Must provide output type annotation for recursive function"

let missing_rec_arg pos =
  Error_msg.mk pos "Must provide argument for recursive function"

let bound_several_times pos x =
  let msg =
    Format.asprintf
      "Variable %s is bound several times in this matching"
      x
  in Error_msg.mk pos msg


(* TYPING
   ----------------------------------------------------------------------
*)

(* Contexts *)

type ctxt = ty Env.t

(* Type Checking *)

let type_of_expr (ctxt : ctxt) (e : expr) : (ty, Error_msg.t) result =
  let ( let* ) = Result.bind in
  
  let rec infer ctxt e =
    match e.expr with
    | Unit -> Ok TUnit
    | Bool _ -> Ok TBool
    | Int _ -> Ok TInt
    | Nil -> Ok TInt_list
 
    | Var x ->
      (match Env.find_opt x ctxt with
       | Some ty -> Ok ty
       | None -> Error (unknown_var e.pos x))
 
    | Assert e1 ->
      let* _ = check ctxt e1 TBool in
      Ok TUnit
 
    | Negate e1 ->
      let* _ = check ctxt e1 TInt in
      Ok TInt
 
    | Bop (bop, e1, e2) ->
      (match bop with
       | Add | Sub | Mul | Div | Mod ->
         let* _ = check ctxt e1 TInt in
         let* _ = check ctxt e2 TInt in
         Ok TInt
       | Lt | Lte | Gt | Gte ->
         let* _ = check ctxt e1 TInt in
         let* _ = check ctxt e2 TInt in
         Ok TBool
       | And | Or ->
         let* _ = check ctxt e1 TBool in
         let* _ = check ctxt e2 TBool in
         Ok TBool
       | Eq | Neq ->
         (* Both sides must have the same type; infer from left *)
         let* t1 = infer ctxt e1 in
         let* _  = check ctxt e2 t1 in
         Ok TBool
       | Cons ->
         let* _ = check ctxt e1 TInt in
         let* _ = check ctxt e2 TInt_list in
         Ok TInt_list)
 
    | If (e1, e2, e3) ->
      let* _  = check ctxt e1 TBool in
      let* t2 = infer ctxt e2 in
      let* _  = check ctxt e3 t2 in
      Ok t2
 
    | Tuple es ->
      let* ts =
        List.fold_left
          (fun acc ei ->
            let* ts = acc in
            let* t  = infer ctxt ei in
            Ok (ts @ [t]))
          (Ok []) es
      in
      Ok (TTuple ts)
 
    | Fun (args, body) ->
      (* Add all typed args to context *)
      let ctxt' = List.fold_left (fun c (x, t) -> Env.add x t c) ctxt args in
      let* ret  = infer ctxt' body in
      (* Build curried type: t1 -> t2 -> ... -> ret *)
      Ok (List.fold_right (fun (_, t) acc -> TFun (t, acc)) args ret)
 
    | App (f_expr, arg_exprs) ->
      let* f_ty = infer ctxt f_expr in
      (* Peel off one TFun per argument *)
      let* result_ty =
        List.fold_left
          (fun acc_ty arg_expr ->
            let* ty = acc_ty in
            match ty with
            | TFun (param_ty, ret_ty) ->
              let* _ = check ctxt arg_expr param_ty in
              Ok ret_ty
            | _ ->
              Error (not_func f_expr.pos ty))
          (Ok f_ty) arg_exprs
      in
      Ok result_ty
 
    | Let { is_rec=false; name; args=[]; annot; binding; body } ->
      (* let name [: annot] = binding in body *)
      let* bind_ty =
        match annot with
        | None     -> infer ctxt binding
        | Some ann ->
          let* _ = check ctxt binding ann in
          Ok ann
      in
      infer (Env.add name bind_ty ctxt) body
 
    | Let { is_rec=false; name; args; annot; binding; body } ->
      (* let name (x1:t1)...(xk:tk) [: annot] = binding in body *)
      let ctxt' = List.fold_left (fun c (x, t) -> Env.add x t c) ctxt args in
      let* ret_ty =
        match annot with
        | None     -> infer ctxt' binding
        | Some ann ->
          let* _ = check ctxt' binding ann in
          Ok ann
      in
      let fun_ty  = List.fold_right (fun (_, t) acc -> TFun (t, acc)) args ret_ty in
      infer (Env.add name fun_ty ctxt) body
 
    | Let { is_rec=true; name=_; args=[]; annot=_; binding=_; body=_ } ->
      (* Recursive with no args is an error after type-checking *)
      Error (missing_rec_arg e.pos)
 
    | Let { is_rec=true; name; args; annot=None; binding=_; body=_ } ->
      ignore (name, args);
      Error (missing_rec_annot e.pos)
 
    | Let { is_rec=true; name; args; annot=Some ret_ty; binding; body } ->
      (* let rec f (x1:t1)...(xk:tk) : ret_ty = binding in body *)
      let fun_ty   = List.fold_right (fun (_, t) acc -> TFun (t, acc)) args ret_ty in
      (* Binding context: f + all args *)
      let ctxt_bind =
        List.fold_left (fun c (x, t) -> Env.add x t c) ctxt args
        |> Env.add name fun_ty
      in
      let* _ = check ctxt_bind binding ret_ty in
      infer (Env.add name fun_ty ctxt) body
 
    | Match _ ->
      (* Not required for check-in *)
      assert false
 
  (* Check that e has exactly [expected] type *)
  and check ctxt e expected =
    let* actual = infer ctxt e in
    if actual = expected then Ok actual
    else Error (exp_ty e.pos actual expected)
  in
  ignore (exp_pat, exp_tuple_pat, exp_diff_tuple_pat, too_many_args, bound_several_times);
  infer ctxt e

let type_of (p : prog) : (ty, Error_msg.t) result =
  let rec go ctxt ty p =
    match p with
    | [] -> Ok (Option.value ~default:TUnit ty)
    | {pos; stmt=SLet {is_rec; name; args; annot; binding}} :: ps -> (
      let body = {pos=dummy_pos; expr=Var name} in
      let e = {pos; expr=Let {is_rec; name; args; annot; binding; body}} in
      match type_of_expr ctxt e with
      | Ok ty ->
        let ctxt = Env.add name ty ctxt in
        go ctxt (Some ty) ps
      | Error err -> Error err
    )
  in go Env.empty None p


(* EVALUATION
   ----------------------------------------------------------------------
*)

(* Values *)

type value =
  | VUnit
  | VBool of bool
  | VInt of int
  | VTuple of value list
  | VClos of {
      env : value Env.t;
      name : string option;
      args : string list;
      body : expr;
    }
  | VInt_list of int list

(* Dynamic Environments *)

type dyn_env = value Env.t

(* Evaluation *)

exception Div_by_zero of pos
exception Assert_fail of pos
exception Match_fail of pos

let eval_expr (env : dyn_env) (e : expr) : value =
  let rec apply caller_env f_val arg_expr =
    let arg_val = go caller_env arg_expr in
    match f_val with
    | VClos { env = clos_env; name; args; body } ->
      (match args with
       | [] -> failwith "apply: closure has no parameters"
       | [x] ->
         (* Final argument: extend closure env and evaluate body *)
         let env' = Env.add x arg_val clos_env in
         (* Re-bind self for recursive closures *)
         let env' = match name with
           | None   -> env'
           | Some f -> Env.add f f_val env'
         in
         go env' body
       | x :: rest ->
         (* Partial application: return a new closure *)
         let env' = Env.add x arg_val clos_env in
         let env' = match name with
           | None   -> env'
           | Some f -> Env.add f f_val env'
         in
         VClos { env = env'; name; args = rest; body })
    | _ -> failwith "apply: not a closure"
 
  and go env e =
    match e.expr with
    | Unit    -> VUnit
    | Bool b  -> VBool b
    | Int n   -> VInt n
    | Nil     -> VInt_list []
 
    | Var x ->
      (match Env.find_opt x env with
       | Some v -> v
       | None   -> failwith ("Unbound variable: " ^ x))
 
    | Assert e1 ->
      (match go env e1 with
       | VBool true -> VUnit
       | _          -> raise (Assert_fail e.pos))
 
    | Negate e1 ->
      (match go env e1 with
       | VInt n -> VInt (-n)
       | _      -> failwith "Negate: expected int")
 
    | Bop (bop, e1, e2) -> eval_bop env e bop e1 e2
 
    | If (e1, e2, e3) ->
      (match go env e1 with
       | VBool true  -> go env e2
       | VBool false -> go env e3
       | _           -> failwith "If: expected bool")
 
    | Tuple es -> VTuple (List.map (go env) es)
 
    | Fun (args, body) ->
      (* Multi-arg fun becomes a curried closure carrying the full arg list *)
      VClos { env; name = None; args = List.map fst args; body }
 
    | App (f_expr, arg_exprs) ->
      let f_val = go env f_expr in
      List.fold_left (apply env) f_val arg_exprs
 
    | Let { is_rec; name; args; annot=_; binding; body } ->
      let v =
        if is_rec then
          (* let rec f (x1:t1)...(xk:tk) : t = binding
             Store a named closure so recursive calls find f in its own env. *)
          VClos { env; name = Some name; args = List.map fst args; body = binding }
        else
          match args with
          | [] -> go env binding
          | _  ->
            (* let f (x1:t1)...(xk:tk) = binding  =>  fun x1 ... xk -> binding *)
            VClos { env; name = None; args = List.map fst args; body = binding }
      in
      go (Env.add name v env) body
 
    | Match _ ->
      (* Not required for check-in *)
      assert false
 
  and eval_bop env e bop e1 e2 =
    match bop with
    | Add ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VInt (a + b) | _ -> failwith "Add")
    | Sub ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VInt (a - b) | _ -> failwith "Sub")
    | Mul ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VInt (a * b) | _ -> failwith "Mul")
    | Div ->
      (* Per spec: evaluate e2 first; raise Div_by_zero if 0 *)
      (match go env e2 with
       | VInt 0 -> raise (Div_by_zero e.pos)
       | VInt b -> (match go env e1 with VInt a -> VInt (a / b) | _ -> failwith "Div")
       | _ -> failwith "Div")
    | Mod ->
      (match go env e2 with
       | VInt 0 -> raise (Div_by_zero e.pos)
       | VInt b -> (match go env e1 with VInt a -> VInt (a mod b) | _ -> failwith "Mod")
       | _ -> failwith "Mod")
    | Eq  ->
      VBool (go env e1 = go env e2)
    | Neq ->
      VBool (go env e1 <> go env e2)
    | Lt  ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VBool (a < b)  | _ -> failwith "Lt")
    | Lte ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VBool (a <= b) | _ -> failwith "Lte")
    | Gt  ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VBool (a > b)  | _ -> failwith "Gt")
    | Gte ->
      (match go env e1, go env e2 with
       | VInt a, VInt b -> VBool (a >= b) | _ -> failwith "Gte")
    | And ->
      (* Short-circuit: only evaluate e2 if e1 is true *)
      (match go env e1 with
       | VBool false -> VBool false
       | VBool true  -> go env e2
       | _ -> failwith "And")
    | Or ->
      (match go env e1 with
       | VBool true  -> VBool true
       | VBool false -> go env e2
       | _ -> failwith "Or")
    | Cons ->
      (match go env e1, go env e2 with
       | VInt n, VInt_list ns -> VInt_list (n :: ns)
       | _ -> failwith "Cons")
  in
  go env e

let eval (p : prog) : value =
  let rec go env v p =
    match p with
    | [] -> Option.value ~default:VUnit v
    | {pos; stmt=SLet {is_rec; name; args; annot; binding}} :: ps ->
      let body = {pos=dummy_pos; expr=Var name} in
      let e = {pos; expr=Let {is_rec; name; args; annot; binding; body}} in
      let v = eval_expr env e in
      go (Env.add name v env) (Some v) ps
  in go Env.empty None p


(* INTERPRETER
   ----------------------------------------------------------------------
*)

let interp ~(filename : string) : (value * ty, Error_msg.t) result =
  let ( let* ) = Result.bind in
  let* prog = Syntax.parse ~filename in
  let* prog = Ast.Interp2.prog_of_prog prog in
  let* ty = type_of prog in
  let* v =
    match eval prog with
    | v -> Ok v
    | exception Assert_fail pos -> Error (Error_msg.mk pos "(Exception) Assert_fail")
    | exception Div_by_zero pos -> Error (Error_msg.mk pos "(Exception) Div_by_zero")
    | exception Match_fail pos -> Error (Error_msg.mk pos "(Exception) Match_fail")
  in
  Ok (v, ty)


(* TESTING STUFF
   ----------------------------------------------------------------------
*)

let parse_expr s =
  let s = "let _ = " ^ s in
  let p = Parser.prog Lexer.read (Lexing.from_string s) in
  match Ast.Interp2.prog_of_prog p with
  | Ok [{pos=_;stmt=SLet {binding=e;_}}] -> e
  | _ -> assert false

let parse_ty s =
  let s = "let _ : " ^ s ^ " = assert false" in
  let p = Parser.prog Lexer.read (Lexing.from_string s) in
  match Ast.Interp2.prog_of_prog p with
  | Ok [{pos=_;stmt=SLet {annot=Some ty;_}}] -> ty
  | _ -> assert false
