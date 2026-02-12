
let is_ws c =
  match c with
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

let is_digit c =
  let c = int_of_char c in
  48 <= c && c <= 57

let is_upper c =
  let c = int_of_char c in
  65 <= c && c <= 90

let all_upper x =
  let rec loop i =
    if i >= String.length x
    then true
    else if not (is_upper x.[i])
    then false
    else loop (i + 1)
  in loop 0

let lex (s : string) : string list =
  let len = String.length s in
  let rec loop i acc current =
    if i >= len then
      if current = "" then List.rev acc else List.rev (current :: acc)
    else
      let c = s.[i] in
      if is_ws c then
        let acc' = if current = "" then acc else current :: acc in
        loop (i + 1) acc' ""
      else if c = '(' || c = ')' || c = '+' || c = '-' || c = '*' || c = '/' || c = '=' then
        let acc' = if current = "" then acc else current :: acc in
        loop (i + 1) (String.sub s i 1 :: acc') ""
      else if is_digit c then
        loop (i + 1) acc (current ^ String.sub s i 1)
      else if is_upper c then
        loop (i + 1) acc (current ^ String.sub s i 1)
      else
        loop (i + 1) acc current
  in
  loop 0 [] ""

let rec eval (env : (string * int) list) (expr : string list) : int =
  let (result, _) = parse_expr env expr in
  result

and parse_expr (env : (string * int) list) (tokens : string list) : int * string list =
  let (value, rest) = parse_term env tokens in
  parse_expr_rest env value rest

and parse_expr_rest (env : (string * int) list) (left : int) (tokens : string list) : int * string list =
  match tokens with
  | "+" :: rest ->
      let (right, rest') = parse_term env rest in
      parse_expr_rest env (left + right) rest'
  | "-" :: rest ->
      let (right, rest') = parse_term env rest in
      parse_expr_rest env (left - right) rest'
  | _ -> (left, tokens)

and parse_term (env : (string * int) list) (tokens : string list) : int * string list =
  let (value, rest) = parse_factor env tokens in
  parse_term_rest env value rest

and parse_term_rest (env : (string * int) list) (left : int) (tokens : string list) : int * string list =
  match tokens with
  | "*" :: rest ->
      let (right, rest') = parse_factor env rest in
      parse_term_rest env (left * right) rest'
  | "/" :: rest ->
      let (right, rest') = parse_factor env rest in
      parse_term_rest env (left / right) rest'
  | _ -> (left, tokens)

and parse_factor (env : (string * int) list) (tokens : string list) : int * string list =
  match tokens with
  | [] -> (0, [])
  | "(" :: rest ->
      let (value, rest') = parse_expr env rest in
      (match rest' with
       | ")" :: rest'' -> (value, rest'')
       | _ -> (value, rest'))
  | token :: rest ->
      if all_upper token then
        (match List.assoc_opt token env with
         | Some value -> (value, rest)
         | None -> (0, rest))
      else if String.length token > 0 && is_digit token.[0] then
        (int_of_string token, rest)
      else
        (0, rest)

let insert_uniq (k : 'k) (v : 'v) (r : ('k * 'v) list) : ('k * 'v) list =
  let rec loop acc = function
    | [] -> (k, v) :: acc
    | (k', v') :: rest ->
        if k = k' then
          loop acc rest
        else
          loop ((k', v') :: acc) rest
  in
  loop [] r

 
let interp (input : string) (env : (string * int) list) : int * (string * int) list =
  match lex input with
  | var :: "=" :: expr -> (
    match eval env expr with
    | ouput -> ouput, insert_uniq var ouput env
    | exception _ -> failwith "whoops!"
  )
  | _
  | exception _ -> failwith "whoops!"
