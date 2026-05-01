open Utils
module Error_msg = Error_msg
module Ast = Ast

type ty = Ast.Type.t =
  | TUnit
  | TBool
  | TInt
  | TString
  | TTuple of ty list
  | TAdt of ty list * string
  | TFun of ty * ty
  | TParam of string

type _pattern = Ast.Pattern.pattern =
  | PWild
  | PVar of string
  | PUnit
  | PBool of bool
  | PInt of int
  | PString of string
  | PTuple of pattern list
  | PCons of string * pattern option
and pattern = Ast.Pattern.t =
  {
    pos : pos;
    pattern : _pattern;
  }

type bop = Ast.Expr.bop =
  | Add | Sub | Mul
  | Div | Mod
  | And | Or
  | Concat
  | Eq | Neq | Lt | Lte | Gt | Gte

type _expr = Ast.Expr.expr =
  | Unit
  | Bool of bool
  | Int of int
  | String of string
  | Negate of expr
  | Bop of bop * expr * expr
  | If of expr * expr * expr
  | Annot of expr * ty
  | Tuple of expr list
  | Assert of expr
  | Var of string
  | Cons of string * expr option
  | Fun of (string * ty option) * expr
  | App of expr * expr
  | Let of
      {
        is_rec : bool;
        name : string;
        binding : expr;
        body : expr;
      }
  | Match of expr * (pattern * expr) list
and expr = Ast.Expr.t =
  {
    pos : pos;
    expr : _expr;
  }

type _stmt = Ast.Stmt.stmt =
  | SLet of
      {
        is_rec : bool;
        name : string;
        binding : expr;
      }
  | SAdt of
      {
        tpars : string list;
        name : string;
        constrs : (string * ty option) list
      }
and stmt = Ast.Stmt.t =
  {
    pos : pos;
    stmt : _stmt;
  }

module Env = Map.Make(String)

let dummy_error = Error_msg.mk dummy_pos "Dummy error"
let unknown_var pos x = Error_msg.mk pos (Format.asprintf "Unbound value %s" x)
let exp_ty pos t1 t2 =
  let msg =
    Format.asprintf
      "This expression has type %a but an expression was expected of type %a"
      Ast.Type.pp t1 Ast.Type.pp t2
  in Error_msg.mk pos msg
let invalid_app pos = Error_msg.mk pos "Invalid application"
let invalid_tuple pos = Error_msg.mk pos "Invalid tuple"
let unknown_cons pos x = Error_msg.mk pos (Format.asprintf "Unbound constructor %s" x)
let cons_exp_no_args pos x =
  Error_msg.mk pos (Format.asprintf "The constructor %s expects 0 arguments" x)
let cons_exp_args pos x =
  Error_msg.mk pos (Format.asprintf "The constructor %s expects arguments" x)
let exp_pat pos t1 t2 =
  let msg =
    Format.asprintf
      "This pattern matches values of type %a but a pattern was expected which matches values of type %a"
      Ast.Type.pp t1 Ast.Type.pp t2
  in Error_msg.mk pos msg
let bound_several_times pos x =
  let msg =
    Format.asprintf
      "Variable %s is bound several times in this matching"
      x
  in Error_msg.mk pos msg
let dup_ty_name pos x =
  let msg =
    Format.asprintf
      "Type using name %s is already defined"
      x
  in Error_msg.mk pos msg
let unbound_ty_var pos n =
  Error_msg.mk pos
    (Format.asprintf "The type variable %s is unbound in this type declaration" n)
let ty_param_several_times pos =
  Error_msg.mk pos "A type parameter occurs several times"

type ty_scheme = string list * ty
type ctxt = ty_scheme Env.t
type constr = ty * ty

let fresh () = TParam (_gensym ())

let rec subst_ty param replacement ty =
  match ty with
  | TUnit | TBool | TInt | TString -> ty
  | TParam a -> if a = param then replacement else ty
  | TTuple ts -> TTuple (List.map (subst_ty param replacement) ts)
  | TAdt (ts, name) -> TAdt (List.map (subst_ty param replacement) ts, name)
  | TFun (t1, t2) -> TFun (subst_ty param replacement t1, subst_ty param replacement t2)

let apply_subst (subst : ty Env.t) ty =
  Env.fold subst_ty subst ty

let apply_subst_constrs subst constrs =
  List.map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) constrs

let rec occurs a t =
  match t with
  | TParam b -> a = b
  | TFun (t1, t2) -> occurs a t1 || occurs a t2
  | TTuple ts | TAdt (ts, _) -> List.exists (occurs a) ts
  | _ -> false

let unify (constrs : constr list) : (ty Env.t, Error_msg.t) result =
  let rec go subst constrs =
    match constrs with
    | [] -> Ok subst
    | (t1, t2) :: rest ->
      let t1 = apply_subst subst t1 in
      let t2 = apply_subst subst t2 in
      if t1 = t2 then
        go subst rest
      else
        match t1, t2 with
        | TFun (s1, t1'), TFun (s2, t2') ->
          go subst ((s1, s2) :: (t1', t2') :: rest)
        | TTuple ts1, TTuple ts2 when List.length ts1 = List.length ts2 ->
          go subst (List.combine ts1 ts2 @ rest)
        | TAdt (ts1, n1), TAdt (ts2, n2) when n1 = n2 && List.length ts1 = List.length ts2 ->
          go subst (List.combine ts1 ts2 @ rest)
        | TParam a, t | t, TParam a ->
          if occurs a t then
            Error dummy_error
          else
            let new_subst = Env.singleton a t in
            let subst' = Env.map (apply_subst new_subst) subst in
            let subst'' = Env.add a t subst' in
            let rest' = apply_subst_constrs new_subst rest in
            go subst'' rest'
        | _ ->
          Error dummy_error
  in
  go Env.empty constrs

let instantiate (params, ty) =
  List.fold_left (fun ty param ->
    subst_ty param (fresh ()) ty
  ) ty params

let rec nub l =
  match l with
  | [] -> []
  | x :: xs -> x :: List.filter ((<>) x) (nub xs)

let free_vars ty =
  let rec go = function
    | TTuple ts | TAdt (ts, _) -> List.concat_map go ts
    | TFun (t1, t2) -> go t1 @ go t2
    | TParam a -> [a]
    | _ -> []
  in nub (go ty)

let normalize_ty ty =
  let vars = free_vars ty in
  let n = List.length vars in
  let names =
    List.init n (fun i ->
      if i < 26 then String.make 1 (Char.chr (Char.code 'a' + i))
      else Format.sprintf "t%d" i
    )
  in
  let mapping = List.combine vars names in
  let rec rename ty =
    match ty with
    | TParam a -> (match List.assoc_opt a mapping with Some b -> TParam b | None -> ty)
    | TFun (t1, t2) -> TFun (rename t1, rename t2)
    | TTuple ts -> TTuple (List.map rename ts)
    | TAdt (ts, name) -> TAdt (List.map rename ts, name)
    | _ -> ty
  in
  (names, rename ty)

let rec type_of_pattern (ctxt : ctxt) (p : pattern)
  : (ty * constr list * ty Env.t, Error_msg.t) result =
  match p.pattern with
  | PWild ->
    let a = fresh () in
    Ok (a, [], Env.empty)
  | PVar x ->
    let a = fresh () in
    Ok (a, [], Env.singleton x a)
  | PUnit -> Ok (TUnit, [], Env.empty)
  | PBool _ -> Ok (TBool, [], Env.empty)
  | PInt _ -> Ok (TInt, [], Env.empty)
  | PString _ -> Ok (TString, [], Env.empty)
  | PTuple ps ->
    let ( let* ) = Result.bind in
    let rec go ps =
      match ps with
      | [] -> Ok ([], [], Env.empty)
      | p :: rest ->
        let* (t, c, env) = type_of_pattern ctxt p in
        let* (ts, cs, envs) = go rest in
        let overlap = Env.find_first_opt (fun k -> Env.mem k envs) env in
        (match overlap with
         | Some (k, _) -> Error (bound_several_times p.pos k)
         | None ->
           Ok (t :: ts, c @ cs, Env.union (fun _ a _ -> Some a) env envs))
    in
    let* (ts, cs, env) = go ps in
    Ok (TTuple ts, cs, env)
  | PCons (cname, popt) ->
    (match Env.find_opt cname ctxt with
     | None -> Error (unknown_cons p.pos cname)
     | Some scheme ->
       let ty_inst = instantiate scheme in
       (match popt, ty_inst with
        | None, TAdt (ts, name) ->
          let betas = List.map (fun _ -> fresh ()) ts in
          let result_ty = TAdt (betas, name) in
          let cs = List.combine ts betas in
          Ok (result_ty, cs, Env.empty)
        | None, TFun _ ->
          Error (cons_exp_args p.pos cname)
        | Some _, TAdt _ ->
          Error (cons_exp_no_args p.pos cname)
        | Some sub_pat, TFun (arg_ty, TAdt (ts, name)) ->
          let ( let* ) = Result.bind in
          let* (pt, pcs, penv) = type_of_pattern ctxt sub_pat in
          let betas = List.map (fun _ -> fresh ()) ts in
          let result_ty = TAdt (betas, name) in
          let fresh_pairs = List.combine ts betas in
          let arg_ty_subst = List.fold_left (fun ty (orig, beta) ->
            match orig with
            | TParam a -> subst_ty a beta ty
            | _ -> ty
          ) arg_ty fresh_pairs in
          let cs = (pt, arg_ty_subst) :: pcs in
          Ok (result_ty, cs, penv)
        | _ ->
          Error dummy_error))

let type_of_expr (ctxt : ctxt) (e : expr) : (ty_scheme, Error_msg.t) result =
  let ( let* ) = Result.bind in
  let rec infer (ctxt : ctxt) (e : expr) : (ty * constr list, Error_msg.t) result =
    match e.expr with
    | Unit -> Ok (TUnit, [])
    | Bool _ -> Ok (TBool, [])
    | Int _ -> Ok (TInt, [])
    | String _ -> Ok (TString, [])
    | Negate e1 ->
      let* (t, c) = infer ctxt e1 in
      Ok (TInt, (t, TInt) :: c)
    | Bop (op, e1, e2) ->
      let* (t1, c1) = infer ctxt e1 in
      let* (t2, c2) = infer ctxt e2 in
      let cs = c1 @ c2 in
      (match op with
       | Add | Sub | Mul | Div | Mod ->
         Ok (TInt, (t1, TInt) :: (t2, TInt) :: cs)
       | And | Or ->
         Ok (TBool, (t1, TBool) :: (t2, TBool) :: cs)
       | Concat ->
         Ok (TString, (t1, TString) :: (t2, TString) :: cs)
       | Eq | Neq ->
         Ok (TBool, (t1, t2) :: cs)
       | Lt | Lte | Gt | Gte ->
         Ok (TBool, (t1, t2) :: cs))
    | If (e1, e2, e3) ->
      let* (t1, c1) = infer ctxt e1 in
      let* (t2, c2) = infer ctxt e2 in
      let* (t3, c3) = infer ctxt e3 in
      Ok (t2, (t1, TBool) :: (t3, t2) :: c1 @ c2 @ c3)
    | Annot (e1, ty) ->
      let* (t', c) = infer ctxt e1 in
      Ok (ty, (t', ty) :: c)
    | Tuple es ->
      let* (ts, cs) =
        List.fold_right (fun e acc ->
          let* (ts, cs) = acc in
          let* (t, c) = infer ctxt e in
          Ok (t :: ts, c @ cs)
        ) es (Ok ([], []))
      in
      Ok (TTuple ts, cs)
    | Assert {expr=Bool false; _} ->
      let a = fresh () in
      Ok (a, [])
    | Assert e1 ->
      let* (t, c) = infer ctxt e1 in
      Ok (TUnit, (t, TBool) :: c)
    | Var x ->
      (match Env.find_opt x ctxt with
       | None -> Error (unknown_var e.pos x)
       | Some scheme ->
         let ty = instantiate scheme in
         Ok (ty, []))
    | Cons (cname, eopt) ->
      (match Env.find_opt cname ctxt with
       | None -> Error (unknown_cons e.pos cname)
       | Some scheme ->
         let ty_inst = instantiate scheme in
         (match eopt, ty_inst with
          | None, TAdt (ts, name) ->
            let betas = List.map (fun _ -> fresh ()) ts in
            let result_ty = TAdt (betas, name) in
            let cs = List.combine ts betas in
            Ok (result_ty, cs)
          | None, TFun _ ->
            Error (cons_exp_args e.pos cname)
          | Some _, TAdt _ ->
            Error (cons_exp_no_args e.pos cname)
          | Some e1, TFun (arg_ty, TAdt (ts, name)) ->
            let* (t, c) = infer ctxt e1 in
            let betas = List.map (fun _ -> fresh ()) ts in
            let result_ty = TAdt (betas, name) in
            let fresh_pairs = List.combine ts betas in
            let arg_ty_subst = List.fold_left (fun ty (orig, beta) ->
              match orig with
              | TParam a -> subst_ty a beta ty
              | _ -> ty
            ) arg_ty fresh_pairs in
            Ok (result_ty, (t, arg_ty_subst) :: c)
          | _ ->
            Error dummy_error))
    | Fun ((x, None), body) ->
      let a = fresh () in
      let ctxt' = Env.add x ([], a) ctxt in
      let* (t_body, c) = infer ctxt' body in
      Ok (TFun (a, t_body), c)
    | Fun ((x, Some ty_ann), body) ->
      let ctxt' = Env.add x ([], ty_ann) ctxt in
      let* (t_body, c) = infer ctxt' body in
      Ok (TFun (ty_ann, t_body), c)
    | App (e1, e2) ->
      let* (t1, c1) = infer ctxt e1 in
      let* (t2, c2) = infer ctxt e2 in
      let a = fresh () in
      Ok (a, (t1, TFun (t2, a)) :: c1 @ c2)
    | Let {is_rec=false; name; binding; body} ->
      let* (t1, c1) = infer ctxt binding in
      let ctxt' = Env.add name ([], t1) ctxt in
      let* (t2, c2) = infer ctxt' body in
      Ok (t2, c1 @ c2)
    | Let {is_rec=true; name; binding; body} ->
      let a = fresh () in
      let ctxt' = Env.add name ([], a) ctxt in
      let* (t1, c1) = infer ctxt' binding in
      let ctxt'' = Env.add name ([], t1) ctxt in
      let* (t2, c2) = infer ctxt'' body in
      Ok (t2, (a, t1) :: c1 @ c2)
    | Match (e0, branches) ->
      let* (t0, c0) = infer ctxt e0 in
      (match branches with
       | [] -> Error dummy_error
       | _ ->
         let* branch_results =
           List.fold_right (fun (pat, branch_e) acc ->
             let* results = acc in
             let* (tp, cp, pat_env) = type_of_pattern ctxt pat in
             let pat_schemes = Env.map (fun t -> ([], t)) pat_env in
             let ctxt' = Env.union (fun _ _ v -> Some v) ctxt pat_schemes in
             let* (te, ce) = infer ctxt' branch_e in
             Ok ((tp, cp, te, ce) :: results)
           ) branches (Ok [])
         in
         let (tp1, cp1, te1, ce1) = List.hd branch_results in
         let rest = List.tl branch_results in
         let cs_pats = List.concat_map (fun (tp, cp, te, ce) ->
           (tp, t0) :: (te, te1) :: cp @ ce
         ) rest in
         let all_cs = (tp1, t0) :: cp1 @ ce1 @ cs_pats @ c0 in
         Ok (te1, all_cs))
  in
  let* (ty, constrs) = infer ctxt e in
  let* subst = unify constrs in
  let ty' = apply_subst subst ty in
  let (params, ty_norm) = normalize_ty ty' in
  Ok (params, ty_norm)

let well_typed (p : stmt list) : (unit, Error_msg.t) result =
  let rec go (used_ty_names : string list) (ctxt : ctxt) p =
    match p with
    | [] -> Ok ()
    | {pos; stmt=SLet {is_rec;name;binding}} :: ps ->
      let body = Ast.Expr.var dummy_pos name in
      let e = Ast.Expr.let_ pos is_rec name [] None binding body in
      begin
        match type_of_expr ctxt e with
        | Ok ty -> go used_ty_names (Env.add name ty ctxt) ps
        | Error e -> Error e
      end
    | {pos; stmt=SAdt {tpars; name; constrs}} :: ps ->
      if nub tpars = tpars
      then
        if List.mem name used_ty_names
        then Error (dup_ty_name pos name)
        else
          let rec process ctxt cs =
            match cs with
            | [] -> Ok ctxt
            | (cons_name, None) :: cs ->
              let tparams = List.map (fun x -> TParam x) tpars in
              process (Env.add cons_name (tpars, TAdt(tparams, name)) ctxt) cs
            | (cons_name, Some ty) :: cs ->
              begin
                match List.(find_opt (fun x -> not (mem x tpars)) (free_vars ty)) with
                | None ->
                  let tparams = List.map (fun x -> TParam x) tpars in
                  let ctxt = Env.add cons_name (tpars, TFun (ty, TAdt(tparams, name))) ctxt in
                  process ctxt cs
                | Some a -> Error (unbound_ty_var pos a)
              end
          in
          match process ctxt constrs with
          | Ok ctxt -> go (name :: used_ty_names) ctxt ps
          | Error e-> Error e
      else Error (ty_param_several_times pos)
  in
  let ctxt =
    Env.(
      empty
      |> add "print_endline" ([], TFun (TString, TUnit))
      |> add "Nil" (["a"], TAdt ([TParam "a"], "list"))
      |> add "Cons" (["a"], TFun (TTuple [TParam "a"; TAdt ([TParam "a"], "list")], TAdt ([TParam "a"], "list")))
    )
  in go [] ctxt p

type value =
  | VUnit
  | VBool of bool
  | VInt of int
  | VString of string
  | VCons of string * value option
  | VTuple of value list
  | VClos of {
      env : value Env.t;
      name : string option;
      arg : string;
      body : expr;
    }

type dyn_env = value Env.t

exception Div_by_zero of pos
exception Assert_fail of pos
exception Match_fail of pos
exception Compare_fun_val of pos

let rec match_pattern (v : value) (p : pattern) : value Env.t option =
  match p.pattern, v with
  | PWild, _ -> Some Env.empty
  | PVar x, _ -> Some (Env.singleton x v)
  | PUnit, VUnit -> Some Env.empty
  | PBool b, VBool b' when b = b' -> Some Env.empty
  | PInt n, VInt n' when n = n' -> Some Env.empty
  | PString s, VString s' when s = s' -> Some Env.empty
  | PTuple ps, VTuple vs when List.length ps = List.length vs ->
    let bindings = List.map2 match_pattern vs ps in
    if List.for_all Option.is_some bindings then
      Some (List.fold_left (fun acc env ->
        Env.union (fun _ a _ -> Some a) acc (Option.get env)
      ) Env.empty bindings)
    else None
  | PCons (cname, None), VCons (cname', None) when cname = cname' ->
    Some Env.empty
  | PCons (cname, Some sub_pat), VCons (cname', Some v') when cname = cname' ->
    match_pattern v' sub_pat
  | _ -> None

let rec compare_values pos v1 v2 =
  match v1, v2 with
  | VUnit, VUnit -> 0
  | VBool b1, VBool b2 -> compare b1 b2
  | VInt n1, VInt n2 -> compare n1 n2
  | VString s1, VString s2 -> compare s1 s2
  | VTuple vs1, VTuple vs2 ->
    let rec cmp_list l1 l2 =
      match l1, l2 with
      | [], [] -> 0
      | x :: xs, y :: ys ->
        let c = compare_values pos x y in
        if c <> 0 then c else cmp_list xs ys
      | _ -> 0
    in cmp_list vs1 vs2
  | VCons (n1, None), VCons (n2, None) -> compare n1 n2
  | VCons (n1, Some v1'), VCons (n2, Some v2') ->
    let c = compare n1 n2 in
    if c <> 0 then c else compare_values pos v1' v2'
  | VClos _, _ | _, VClos _ -> raise (Compare_fun_val pos)
  | _ -> 0

let eval_expr (env : dyn_env) (e : Ast.Expr.t) : value =
  let rec eval (env : dyn_env) (e : expr) : value =
    match e.expr with
    | Unit -> VUnit
    | Bool b -> VBool b
    | Int n -> VInt n
    | String s -> VString s
    | Negate e1 ->
      (match eval env e1 with
       | VInt n -> VInt (-n)
       | _ -> assert false)
    | Bop (op, e1, e2) ->
      (match op with
       | And ->
         (match eval env e1 with
          | VBool false -> VBool false
          | VBool true -> eval env e2
          | _ -> assert false)
       | Or ->
         (match eval env e1 with
          | VBool true -> VBool true
          | VBool false -> eval env e2
          | _ -> assert false)
       | Div ->
         let v2 = eval env e2 in
         let v1 = eval env e1 in
         (match v1, v2 with
          | VInt _, VInt 0 -> raise (Div_by_zero e.pos)
          | VInt n1, VInt n2 -> VInt (n1 / n2)
          | _ -> assert false)
       | Mod ->
         let v2 = eval env e2 in
         let v1 = eval env e1 in
         (match v1, v2 with
          | VInt _, VInt 0 -> raise (Div_by_zero e.pos)
          | VInt n1, VInt n2 -> VInt (n1 mod n2)
          | _ -> assert false)
       | _ ->
         let v1 = eval env e1 in
         let v2 = eval env e2 in
         (match op, v1, v2 with
          | Add, VInt n1, VInt n2 -> VInt (n1 + n2)
          | Sub, VInt n1, VInt n2 -> VInt (n1 - n2)
          | Mul, VInt n1, VInt n2 -> VInt (n1 * n2)
          | Concat, VString s1, VString s2 -> VString (s1 ^ s2)
          | Eq, _, _ -> VBool (compare_values e.pos v1 v2 = 0)
          | Neq, _, _ -> VBool (compare_values e.pos v1 v2 <> 0)
          | Lt, _, _ -> VBool (compare_values e.pos v1 v2 < 0)
          | Lte, _, _ -> VBool (compare_values e.pos v1 v2 <= 0)
          | Gt, _, _ -> VBool (compare_values e.pos v1 v2 > 0)
          | Gte, _, _ -> VBool (compare_values e.pos v1 v2 >= 0)
          | _ -> assert false))
    | If (e1, e2, e3) ->
      (match eval env e1 with
       | VBool true -> eval env e2
       | VBool false -> eval env e3
       | _ -> assert false)
    | Annot (e1, _) -> eval env e1
    | Tuple es -> VTuple (List.map (eval env) es)
    | Assert e1 ->
      (match eval env e1 with
       | VBool true -> VUnit
       | VBool false -> raise (Assert_fail e.pos)
       | _ -> assert false)
    | Var x ->
      (match Env.find_opt x env with
       | Some v -> v
       | None -> assert false)
    | Cons (cname, None) -> VCons (cname, None)
    | Cons (cname, Some e1) ->
      let v = eval env e1 in
      VCons (cname, Some v)
    | Fun ((x, _), body) ->
      VClos { env; name = None; arg = x; body }
    | App (e1, e2) ->
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      (match v1 with
       | VClos { env = cenv; name = None; arg; body } ->
         let env' = Env.add arg v2 cenv in
         (match body.expr with
          | Unit ->
            if arg = "$print_endline" then
              (match v2 with
               | VString s -> print_endline s; VUnit
               | _ -> assert false)
            else eval env' body
          | _ -> eval env' body)
       | VClos { env = cenv; name = Some f; arg; body } ->
         let env' = Env.add f v1 (Env.add arg v2 cenv) in
         eval env' body
       | _ -> assert false)
    | Let {is_rec=false; name; binding; body} ->
      let v1 = eval env binding in
      let env' = Env.add name v1 env in
      eval env' body
    | Let {is_rec=true; name; binding; body} ->
      (match binding.expr with
       | Fun ((x, _), fun_body) ->
         let clos = VClos { env; name = Some name; arg = x; body = fun_body } in
         let env' = Env.add name clos env in
         eval env' body
       | _ ->
         let clos = VClos { env; name = Some name; arg = "_"; body = binding } in
         let env' = Env.add name clos env in
         eval env' body)
    | Match (e0, branches) ->
      let v0 = eval env e0 in
      let rec try_branches = function
        | [] -> raise (Match_fail e.pos)
        | (pat, branch_e) :: rest ->
          (match match_pattern v0 pat with
           | None -> try_branches rest
           | Some bindings ->
             let env' = Env.union (fun _ _ v -> Some v) env bindings in
             eval env' branch_e)
      in
      try_branches branches
  in
  eval env e

let eval (p : stmt list) : value =
  let rec go env v p =
    match p with
    | [] -> Option.value ~default:VUnit v
    | {pos; stmt=SLet {is_rec; name; binding}} :: ps ->
      let body = {pos=dummy_pos; expr=Var name} in
      let e = Ast.Expr.let_ pos is_rec name [] None binding body in
      let v = eval_expr env e in
      go (Env.add name v env) (Some v) ps
    | _ :: ps -> go env v ps
  in
  let env =
    Env.(
      empty
      |> add "print_endline"
        (VClos
           {
             env = empty;
             name = None;
             arg = "$print_endline";
             body = Ast.Expr.mk dummy_pos Unit;
           })
    )
  in go env None p

let interp ~(filename : string) : (value, Error_msg.t) result =
  let ( let* ) = Result.bind in
  let* prog = Syntax.parse ~filename in
  let* () = well_typed prog in
  let* v =
    match eval prog with
    | v -> Ok v
    | exception Assert_fail pos -> Error (Error_msg.mk pos "(Exception) Assert_fail")
    | exception Div_by_zero pos -> Error (Error_msg.mk pos "(Exception) Div_by_zero")
    | exception Match_fail pos -> Error (Error_msg.mk pos "(Exception) Match_fail")
    | exception Compare_fun_val pos -> Error (Error_msg.mk pos "(Exception) Compare_fun_val")
  in
  Ok v

let parse_expr s =
  let s = "let _x = " ^ s in
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | [{pos=_;stmt=SLet {binding=e;_}}] -> e
  | _ -> assert false