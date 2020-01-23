(*
Impératif :
- type unit ()
- tableaux (array)
- références
  # let i = ref 0;;
  # !i
    int val = 0
  # i <- 1
*)

(* Exercice 105. Factorielle impérative *)

let fact (n : int) : int =
  let res : int ref = ref 1 in
  begin
  for i = 1 to n do
    res := !res * i
  done;
  !res
  end
;;

fact 2;;
fact 3;;
fact 4;;
  
(* Exercice 108. Type Array *)

let reverse (a : 'a array) : 'a array =
  let n : int = Array.length a in
  for i = 0 to ((n / 2) + 1) do
    let tmp : 'a = a.(i) in
    a.(i) <- a.(n - i - 1);
    a.(n - i - 1) <- tmp
    (* Array.set a i (Array.get a (n - i)) *)
  done;
  a
;;

let a1 : int array = [| 1 ; 2 ; 3 |];;
let a2 : int array = [| 7 ; 6 ; 5 ; 4 |];;

reverse a1;;
reverse a2;;

(* Exercice 109. Type Array et listes *)

let array_map (f : 'a -> 'b) (a : 'a array) : 'b array =
  let n : int = Array.length a in
  if (n <= 0) then [||]
  else
    let b : 'b array = Array.make n (f a.(0)) in
    begin
      for i = 0 to (n - 1) do
        b.(i) <- f (a.(i))
      done;
      b
    end
;;

let f (x : int) : int = x + 1;;
let g (x : int) : int = 2 * x;;

array_map f a1;;
array_map g a2;;

let array_map2 (f : 'a -> 'b) (a : 'a array) : 'b array =
  Array.init (Array.length a) (fun i -> f a.(i))
;;

array_map2 f a1;;
array_map2 g a2;;

let array_to_list (a : 'a array) : 'b list =
  let n : int = Array.length a in
  let b : 'b list ref = ref [] in
  begin
    for i = (n - 1) downto 0 do
      b := (a.(i))::(!b)
    done;
    !b
  end
;;

array_to_list a1;;
array_to_list a2;;

let rec array_to_list2 (a : 'a array) : 'a list =
  let n : int = Array.length a in
  let rec aux a i =
    if (i = n) then []
    else a.(i)::(aux a (i + 1)) in
  aux a 0
;;

array_to_list2 a1;;
array_to_list2 a2;;

let rec array_of_list (l : 'a list) : 'a array =
  match l with
  | [] -> [||]
  | h::q ->
     let n : int = List.length l in
     let a : 'a array = Array.make n h in
     let rec aux (l : 'a list) (i : int) : unit =
       match l with
       | [] -> ()
       | e::r -> a.(i) <- e ; aux r (i + 1) in
     aux l 0;
     a
;;

array_of_list (array_to_list2 a1);;
array_of_list (array_to_list2 a2);;
