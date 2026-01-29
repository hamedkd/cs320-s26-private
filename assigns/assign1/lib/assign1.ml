
let sqrt (n : int) : int = (* CHANGE _n to n! *)
  let rec loop k=
    if k*k>=n 
    then k 
    else loop(k+1)
  in loop 0

(*-----------------------TEST-----------*)

let pow (n : int) (k : int) : int = (* CHANGE _n to n and _k to k! *)
  if k < 0 
  then 0
  else
  let rec loop acc k=
    if k=0 
    then acc
    else loop(acc * n) (k - 1)
  in loop 1 k 

(*-----------------------TEST-----------*)


let is_ws = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

(*--------------------Good--------------*)

let string_of_char (c : char) : string =
  String.init 1 (fun _ -> c)

(*--------------------Good--------------*)

let explode (s : string) : char list =
  let rec loop acc i =
    if i = String.length s
    then List.rev acc
    else loop (String.get s i :: acc) (i + 1)
  in loop [] 0

(*--------------------Good--------------*)

let implode (cs : char list) : string =
  String.init
    (List.length cs)
    (fun i -> List.nth cs i)

(*--------------------Good--------------*)

let implode_all (css : char list list) : string list =
  let rec loop acc css =
    match css with
    | [] -> List.rev acc
    | cs :: rest -> loop (implode cs :: acc) rest
  in loop [] css

(*--------------------Good--------------*)

let split_on_ws_helper (cs : char list) : char list list =
  let rec loop st acc = function
    | [] ->
        if st = [] 
        then List.rev acc
        else List.rev (List.rev st :: acc)

    | c :: res ->
        if is_ws c then
          if st = [] 
          then loop [] acc res
          else loop [] (List.rev st :: acc) res
        else loop (c :: st) acc res
  in loop [] [] cs

(*------------Testing----------------*)

let split_on_ws (s : string) : string list =
  implode_all (split_on_ws_helper (explode s))

(*--------------------Good--------------*)

let rec eval (stack : int list) (_prog : string list) : int list =
  match _prog with
  | [] -> stack
  | i :: r ->
    match i, stack with
      | "+", a :: b :: s -> eval ((b + a) :: s) r
      | "-", a :: b :: s -> eval ((b - a) :: s) r
      | "*", a :: b :: s -> eval ((b * a) :: s) r
      | "/", a :: b :: s -> eval ((b / a) :: s) r
      | "mod", a :: b :: s -> eval ((b mod a) :: s) r
      | "sqrt", a :: s ->  eval (sqrt a :: s) r
      | "^", a :: b :: s -> eval (pow b a :: s) r
      | _, _ -> eval (int_of_string i :: stack) r
      


let interp (input : string) : int =
  match eval [] (split_on_ws input) with
  | [output] -> output
  | _ -> failwith "whoops!"

(*--------------------Good--------------*)
