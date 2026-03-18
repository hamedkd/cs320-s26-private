module Tensor = Tensor
type tensor = Tensor.t

type 'a sexpr = 'a Sexpr.t =
  | Atom of 'a
  | List of 'a sexpr list

type op = Syntax.op = Add | Mul

type expr = Syntax.expr =
  | Ident of string * string list
  | Map of op * expr * expr
  | Fold of op * string * expr

type stmt = Syntax.stmt =
  | Init of string * int list * float sexpr
  | Set of string * string list * expr

let dim_check (env : (string * tensor) list) (e : expr) : ((string * int) list) option =
  let consistent i j =
    List.for_all (fun (lbl, n) ->
      match List.assoc_opt lbl j with
      | None -> true
      | Some m -> n = m
    ) i
  in
  let union_idx i j =
    let extra = List.filter (fun (lbl, _) -> not (List.mem_assoc lbl i)) j 
    in i @ extra
  in
  let remove_axis lbl idx = List.filter (fun (l, _) -> l <> lbl) idx in
  let rec go e =
    match e with
    | Ident (name, new_labels) -> (
        match List.assoc_opt name env with
        | None -> None
        | Some t ->
          let idx = Tensor.idx_space t in
          let n = List.length idx in
          if List.length new_labels <> n 
          then None
          else
            let new_idx = List.combine new_labels (List.map snd idx) in
            let unique = List.sort_uniq String.compare new_labels in
            if List.length unique <> n 
            then None
            else Some new_idx
      )
    | Map (_, e1, e2) -> (
        match go e1, go e2 with
        | Some i, Some j when consistent i j -> Some (union_idx i j)
        | _ -> None
      )
    | Fold (_, lbl, e1) -> (
        match go e1 with
        | Some idx when List.mem_assoc lbl idx -> Some (remove_axis lbl idx)
        | _ -> None
      )
  in go e

let eval (env : (string * tensor) list) (e : expr) : tensor =
   let union_idx i j =
    let extra = List.filter (fun (lbl, _) -> not (List.mem_assoc lbl i)) j in
    i @ extra
  in
  let remove_axis lbl idx = List.filter (fun (l, _) -> l <> lbl) idx in
  let apply_op op a b = match op with Add -> a +. b | Mul -> a *. b in
  let fold_init op = match op with Add -> 0.0 | Mul -> 1.0 in
  let rec go e =
    match e with
    | Ident (name, new_labels) ->
      let t = List.assoc name env in
      Tensor.relabel_axes t new_labels
    | Map (op, e1, e2) ->
      let t1 = go e1 in
      let t2 = go e2 in
      let combined = union_idx (Tensor.idx_space t1) (Tensor.idx_space t2) in
      Tensor.init combined (fun idx ->
        apply_op op (Tensor.get t1 idx) (Tensor.get t2 idx))
    | Fold (op, lbl, e1) ->
      let t = go e1 in
      let n = List.assoc lbl (Tensor.idx_space t) in
      let out_idx = remove_axis lbl (Tensor.idx_space t) in
      Tensor.init out_idx (fun idx_out ->
        let acc = ref (fold_init op) in
        for k = 0 to n - 1 do
          acc := apply_op op !acc (Tensor.get t ((lbl, k) :: idx_out))
        done;
        !acc)
  in go e
 

type error =
  | Parse_error
  | Dim_error
  | Init_error

let interp (env : (string * tensor) list) (s : string) : ((string * tensor) list, error) result =
  let interp_stmt env stmt =
    match Syntax.stmt_of_sexpr_opt stmt with
    | Some (Init (a, shape, expr)) -> (
        match Tensor.of_sexpr_opt shape expr with
        | Some t -> Ok ((a, t) :: env)
        | _ -> Error Init_error
      )
    | Some (Set (a, idx, e)) -> (
        let sort  = List.sort String.compare in
        match dim_check env e with
        | Some idx_space when sort idx = sort (List.map fst idx_space) ->
          let idx_space = List.map (fun x -> (x, List.assoc x idx_space)) idx in
          let t = Tensor.init idx_space (Tensor.get (eval env e)) in
          Ok ((a, t) :: env)
        | _ -> Error Dim_error
      )
    | _ -> Error Parse_error
  in
  let rec interp_prog env = function
    | [] -> Ok env
    | e :: es -> (
        match interp_stmt env e with
        | Ok env -> interp_prog env es
        | Error e -> Error e
      )
  in
  match Sexpr.list_of_string_opt s with
  | Some ss -> interp_prog env ss
  | None -> Error Parse_error
