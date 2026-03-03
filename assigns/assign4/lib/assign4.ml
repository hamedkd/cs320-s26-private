let is_ws = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

type token = Lpar | Rpar | Word of string

let tokens_of_string (s : string) : token list =
  let rec go acc i =
    if i >= String.length s
    then acc
    else
      match s.[i] with
      | '(' -> go (Lpar :: acc) (i + 1)
      | ')' -> go (Rpar :: acc) (i + 1)
      | c ->
        if is_ws c
        then go acc (i + 1)
        else
          let rec go' j =
            if i + j >= String.length s
            then Word (String.sub s i j) :: acc
            else
              let c = s.[i + j] in
              if List.mem c ['('; ')'] || is_ws c
              then go (Word (String.sub s i j) :: acc) (i + j)
              else go' (j + 1)
          in go' 1
  in List.rev (go [] 0)

type sexpr =
  | Atom of string
  | List of sexpr list

let sexpr_of_tokens_opt (ts : token list) : sexpr option =
  let rec go (ts : token list) : (sexpr * token list) option =
    match ts with
    | [] -> None
    | t :: ts -> (
        match t with
        | Word a -> Some (Atom a, ts)
        | Lpar -> (
            match go' ts with
            | es, Rpar :: ts -> Some (List es, ts)
            | _ -> None
          )
        | Rpar -> None
      )
  and go' (ts : token list) : sexpr list * token list =
    match go ts with
    | Some (e, ts) ->
      let (es, ts) = go' ts in
      e :: es, ts
    | None -> [], ts
  in
  match go ts with
  | Some (e, []) -> Some e
  | _ -> None

let sexpr_of_string_opt (s : string) : sexpr option =
  sexpr_of_tokens_opt (tokens_of_string s)

let rec string_of_sexpr (e : sexpr) : string =
  match e with
  | Atom s -> s
  | List ss -> "(" ^ String.concat " " (List.map string_of_sexpr ss) ^ ")"

type op = Add | Mul | Eq

let string_of_op (op : op) : string =
  match op with
  | Add -> "+"
  | Mul -> "*"
  | Eq -> "="

let op_of_sexpr_opt (s : sexpr) : op option =
  match s with
  | Atom "+" -> Some Add
  | Atom "*" -> Some Mul
  | Atom "=" -> Some Eq
  | _ -> None

type expr =
  | Int of int
  | Bop of op * expr * expr
  | If of expr * expr * expr

let expr_of_sexpr_opt (s : sexpr) : expr option =
  let rec go s =
    match s with
    | Atom a -> (
        match int_of_string_opt a with
        | Some n -> Some (Int n)
        | None -> None
      )
    | List [Atom "if";
             cond_s;
             then_s;
             else_s] -> (
        match go cond_s, go then_s, go else_s with
        | Some c, Some t, Some e -> Some (If (c, t, e))
        | _ -> None
      )
    | List [op_s; 
            e1_s; 
            e2_s] -> (
        match op_of_sexpr_opt op_s, go e1_s, go e2_s with
        | Some op, Some e1, Some e2 -> Some (Bop (op, e1, e2))
        | _ -> None
      )
    | _ -> None
  in go s

let expr_of_string_opt (s : string) : expr option =
  match sexpr_of_string_opt s with
  | Some se -> expr_of_sexpr_opt se
  | None -> None

let rec sexpr_of_expr (e : expr) : sexpr =
  match e with
  | Int n -> Atom (string_of_int n)
  | Bop (op, e1, e2) ->
    List [Atom (string_of_op op); sexpr_of_expr e1; sexpr_of_expr e2]
  | If (cond, e1, e2) ->
    List [Atom "if"; sexpr_of_expr cond; sexpr_of_expr e1; sexpr_of_expr e2]

let string_of_expr (e : expr) : string =
  string_of_sexpr (sexpr_of_expr e)

type ty = BoolT | IntT

let ty_of_sexpr_opt (e : sexpr) : ty option =
  match e with
  | Atom s -> (
      match s with
      | "bool" -> Some BoolT
      | "int" -> Some IntT
      | _ -> None
    )
  | _ -> None

let string_of_ty (ty : ty) : string =
  match ty with
  | BoolT -> "bool"
  | IntT -> "int"

type ty_jmt =
  {
    expr : expr;
    ty : ty;
  }

let string_of_ty_jmt (j : ty_jmt) : string =
  string_of_expr j.expr ^ " : " ^ string_of_ty j.ty

type ty_rule =
  | Int_lit
  | Add_int
  | Mul_int
  | Eq_rule
  | If_rule

let string_of_ty_rule (r : ty_rule) =
  match r with
  | Int_lit -> "intLit"
  | Add_int -> "addInt"
  | Mul_int -> "mulInt"
  | Eq_rule -> "eq"
  | If_rule -> "if"

let ty_rule_of_sexpr_opt (e : sexpr) : ty_rule option =
  match e with
  | Atom s -> (
      match s with
      | "INTLIT" -> Some Int_lit
      | "ADDINT" -> Some Add_int
      | "MULINT" -> Some Mul_int
      | "EQ" -> Some Eq_rule
      | "IF" -> Some If_rule
      | _ -> None
    )
  | _ -> None

type ty_deriv =
  | Rule_app of {
      prem_derivs : ty_deriv list;
      concl : ty_jmt;
      rname : ty_rule;
    }
  | Hole

let ty_deriv_of_sexpr_opt (s : sexpr) : ty_deriv option =
  let rec go s =
    match s with
    | Atom "???" -> Some Hole
    | List (expr_s :: ty_s :: rname_s :: prem_ss) -> (
        match expr_of_sexpr_opt expr_s, ty_of_sexpr_opt ty_s, ty_rule_of_sexpr_opt rname_s with
        | Some expr, Some ty, Some rname ->
          let prem_derivs_opt = List.map go prem_ss in
          let prem_derivs = List.fold_left (fun acc opt ->
            match opt with
            | Some v -> v :: acc
            | None -> acc
          ) [] prem_derivs_opt |> List.rev in
          if List.length prem_derivs = List.length prem_derivs_opt
          then Some (Rule_app {
            prem_derivs;
            concl = { expr; ty };
            rname;
          })
          else None
        | _ -> None
      )
    | _ -> None
  in go s

let ty_deriv_of_string_opt (s : string) : ty_deriv option =
  match sexpr_of_string_opt s with
  | Some se -> ty_deriv_of_sexpr_opt se
  | None -> None

let string_of_ty_deriv (d : ty_deriv) : string =
  let rec go d =
    match d with
    | Hole -> [("???", "hole")]
    | Rule_app d ->
      (string_of_ty_jmt d.concl, string_of_ty_rule d.rname) :: go' [] d.prem_derivs
  and go' has_line ds =
    let lines =
      List.fold_left
        (fun acc b -> (if b then "│  " else "   ") ^ acc)
        ""
        has_line
    in
    match ds with
    | [] -> []
    | [Hole] ->
      [lines ^ "└──???" , "hole"]
    | [Rule_app d] ->
      let next_line =
        ( lines ^ "└──" ^ string_of_ty_jmt d.concl
        , string_of_ty_rule d.rname
        )
      in next_line :: go' (false :: has_line) d.prem_derivs
    | Hole :: ds -> (lines ^ "├──???" , "hole") :: go' has_line ds
    | Rule_app d :: ds ->
      let next_line =
        ( lines ^ "├──" ^ string_of_ty_jmt d.concl
        , string_of_ty_rule d.rname
        )
      in
      next_line
      :: go' (true :: has_line) d.prem_derivs
      @ go' has_line ds
  in
  let lines = go d in
  let length = Uuseg_string.fold_utf_8 `Grapheme_cluster (fun x _ -> x + 1) 0 in
  let width =
    List.fold_left
      (fun acc (line, _) -> max acc (length line))
      0
      lines
  in
  let lines =
    List.map
      (fun (line, rname) ->
         String.concat ""
           [
             line;
             String.init (width - length line + 2) (fun _ -> ' ');
             "("; rname; ")";
           ])
      lines
  in
  String.concat "\n" lines

let check_rule (rule : ty_rule) (prems : ty_jmt option list) (concl : ty_jmt) : bool =
  match rule with
  | Int_lit -> (
      match concl.expr, concl.ty, prems with
      | Int _, IntT, [] -> true
      | _ -> false
    )
  | Add_int -> (
      match concl.expr, concl.ty, prems with
      | Bop (Add, e1, e2), IntT, [p1; p2] ->
        (match p1 with None -> true | Some j -> j.expr = e1 && j.ty = IntT) &&
        (match p2 with None -> true | Some j -> j.expr = e2 && j.ty = IntT)
      | _ -> false
    )
  | Mul_int -> (
      match concl.expr, concl.ty, prems with
      | Bop (Mul, e1, e2), IntT, [p1; p2] ->
        (match p1 with None -> true | Some j -> j.expr = e1 && j.ty = IntT) &&
        (match p2 with None -> true | Some j -> j.expr = e2 && j.ty = IntT)
      | _ -> false
    )
  | Eq_rule -> (
      match concl.expr, concl.ty, prems with
      | Bop (Eq, e1, e2), BoolT, [p1; p2] ->
        let t = match p1 with
          | Some j -> Some j.ty
          | None -> (match p2 with Some j -> Some j.ty | None -> None)
        in
        (match p1 with None -> true | Some j -> j.expr = e1 && Some j.ty = t) &&
        (match p2 with None -> true | Some j -> j.expr = e2 && Some j.ty = t)
      | _ -> false
    )
  | If_rule -> (
      match concl.expr, prems with
      | If (e1, e2, e3), [p1; p2; p3] ->
        let tau = concl.ty in
        (match p1 with None -> true | Some j -> j.expr = e1 && j.ty = BoolT) &&
        (match p2 with None -> true | Some j -> j.expr = e2 && j.ty = tau) &&
        (match p3 with None -> true | Some j -> j.expr = e3 && j.ty = tau)
      | _ -> false
    )

type status =
  | Complete
  | Invalid
  | Partial

let check_deriv (d : ty_deriv) : status =
  let rec go d =
    match d with
    | Hole -> Partial
    | Rule_app { prem_derivs; concl; rname } ->
      let prem_jmts = List.map (fun pd ->
        match pd with
        | Hole -> None
        | Rule_app r -> Some r.concl
      ) prem_derivs in
      if not (check_rule rname prem_jmts concl)
      then Invalid
      else
        let sub_statuses = List.map go prem_derivs in
        if List.fold_left (fun acc s -> acc || s = Invalid) false sub_statuses
        then Invalid
        else if List.fold_left (fun acc s -> acc || s = Partial) false sub_statuses
        then Partial
        else Complete
  in go d

type value = BoolV of bool | IntV of int

let string_of_value (v : value) : string =
  match v with
  | BoolV b -> string_of_bool b
  | IntV n -> string_of_int n

let value_of_expr (e : expr) : value =
  let rec go e =
    match e with
    | Int n -> IntV n
    | Bop (Add, e1, e2) -> (
        match go e1, go e2 with
        | IntV v1, IntV v2 -> IntV (v1 + v2)
        | _ -> assert false
      )
    | Bop (Mul, e1, e2) -> (
        match go e1, go e2 with
        | IntV v1, IntV v2 -> IntV (v1 * v2)
        | _ -> assert false
      )
    | Bop (Eq, e1, e2) -> BoolV (go e1 = go e2)
    | If (cond, e1, e2) -> (
        match go cond with
        | BoolV true -> go e1
        | BoolV false -> go e2
        | _ -> assert false
      )
  in go e

type error = Parse_error | Invalid_deriv of ty_deriv

let interp (s : string) : (ty_deriv * value option, error) result =
  match ty_deriv_of_string_opt s with
  | Some deriv -> (
    match check_deriv deriv with
    | Complete -> (
      match deriv with
      | Rule_app d -> Ok (deriv, Some (value_of_expr d.concl.expr))
      | _ -> assert false
    )
    | Partial -> Ok (deriv, None)
    | Invalid -> Error (Invalid_deriv deriv)
  )
  | None -> Error Parse_error

let example_deriv : string =
  {|((if (= (= 5 (+ 1 4)) (= 0 1)) (+ 2 3) (* (+ 4 5) 67)) int IF
  ((= (= 5 (+ 1 4)) (= 0 1)) bool EQ
    ((= 5 (+ 1 4)) bool EQ
      (5 int INTLIT)
      ((+ 1 4) int ADDINT
        (1 int INTLIT)
        (4 int INTLIT)))
    ((= 0 1) bool EQ
      (0 int INTLIT)
      (1 int INTLIT)))
  ((+ 2 3) int ADDINT
    (2 int INTLIT)
    (3 int INTLIT))
  ((* (+ 4 5) 67) int MULINT
    ((+ 4 5) int ADDINT
      (4 int INTLIT)
      (5 int INTLIT))
    (67 int INTLIT)))|}