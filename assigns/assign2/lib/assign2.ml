
let is_ws c =
  match c with
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

let is_digit c =
  let c = int_of_char c in
  48 <= c && c <= 57

let lex s =
  let rec go acc i =
    let rec go_digits acc i j =
      if i + j >= String.length s
      then List.rev (String.sub s i j :: acc)
      else if is_digit (String.get s (i + j))
      then go_digits acc i (j + 1)
      else go (String.sub s i j :: acc) (i + j)
    in
    if i >= String.length s
    then List.rev acc
    else
      match String.get s i with
      | '+' -> go ("+" :: acc) (i + 1)
      | '-' -> go ("-" :: acc) (i + 1)
      | '*' -> go ("*" :: acc) (i + 1)
      | '/' -> go ("/" :: acc) (i + 1)
      | '(' -> go ("(" :: acc) (i + 1)
      | ')' -> go (")" :: acc) (i + 1)
      | c ->
        if is_digit c
        then go_digits acc i 1
        else if is_ws c
        then go acc (i + 1)
        else assert false
  in go [] 0

let rec drop_last l =
  match l with
  | x :: y :: rest -> x :: drop_last (y :: rest)
  | _ -> []

let eval expr =
  let split_at i l =
    let rec loop n acc l =
      if n = 0 
      then match l with
           | _ :: t -> (List.rev acc, t)
           | [] -> assert false
      else match l with
      | h :: t -> loop (n - 1) (h :: acc) t
      | [] -> assert false
    in loop i [] l
  in
  let help2 ops expr =
    let rec loop i depth f = function
      | [] -> f
      | h :: t ->
        if h = "(" then loop (i + 1) (depth + 1) f t
        else if h = ")" 
        then loop (i+1) (depth - 1) f t
        else if depth = 0 && List.mem h ops 
        then
          loop (i+1) depth (Some (i, h)) t
        else
          loop (i+1) depth f t
    in
    loop 0 0 None expr
  in
  let rec eval_expr expr =
    match help2 ["+"; "-"] expr with
    | Some (i, op) ->
        let (l, r) = split_at i expr in
        if op = "+" 
        then eval_expr l + eval_expr r
        else eval_expr l - eval_expr r
    | None -> eval_mul_div expr
  and eval_mul_div expr =
    match help2 ["*"; "/"] expr with
    | Some (i, op) ->
        let (lhs, rhs) = split_at i expr in
        if op = "*" 
        then eval_mul_div lhs * eval_mul_div rhs
        else eval_mul_div lhs / eval_mul_div rhs
    | None -> eval_num_paren expr
  and eval_num_paren expr =
    match expr with
    | [n] -> int_of_string n               (* number *)
    | "(" :: rest -> eval_expr (drop_last rest) (* parened expr *)
    | _ -> assert false                    (* undefined *)
  in eval_expr expr



let interp (input : string) : int =
  match eval (lex input) with
  | output -> output
  | exception _ -> failwith "whoops!"
