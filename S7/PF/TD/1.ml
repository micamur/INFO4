(* 1. INTRODUCTION À OCAML *)

(* Exercice 1. Deviner *)

let a =
  1 + 1;;
let r =
  let x = 7 in
  6 * x;;
let a = (r - 6) / 6 - 6;;
let o = r * r - x * x - 51;;
let u =
  let x = 9 in
  if (x < 9) then
    9 / (x - x)
  else
    (x + x) / 9;;

(* Exercice 2. Corriger *)

let pisur4 = 3.14 /. 4.;;
let danslordre = 1 < 2 && 2 < 3;; (* 1 < 2 < 3 *)
let positif =
  let a = 42 in
  if a >= 0 then true else false;;
let doubleabsolu =
  let x = -2.7 in
  (if (x < 0.) then
     -. x
   else
     x)
  *. 2.;;

(* Exercice 3. Échauffement *)

type semaine = Lundi | Mardi | Mercredi | Jeudi | Vendredi | Samedi | Dimanche;;
type point2D = int * int;;
let p1 : point2D = (1, 2);;
type segment = point2D * point2D;;
type carre = { top : segment };;
type rectangle = { diagonale : segment };;
type cercle = { rayon : segment };;
type figure = Carre of carre | Rectangle of rectangle | Cercle of cercle;;
let fcarre : figure = Carre({ top = ( (1, 1), (2, 1) ) });;
let frect : figure = Rectangle({ diagonale = ( (1, 1), (4, 0) ) });;
let fcercle : figure = Cercle({ rayon = ( (1, 1), (3, 1) ) });;

(* Exercice 4. Jeu de Uno *)

type couleur = Rouge | Jaune | Bleu | Vert;;
type typenormal = Int of int | Plus2 | Inversion | Passer;;
type normal = { c : couleur ; t : typenormal };;
type special = Joker | Plus4;;
type carte = Normal of normal | Special of special;;

let j1 : carte = Normal( { c = Jaune ; t = Int(1) } );;
let joker : carte = Special( Joker );;
let binv : carte = Normal( { c = Bleu ; t = Inversion } );;

(* Exercice 5. Premières fonctions *)

let f = fun a -> a - 1;;
f(4);;
let cube = fun f -> f *. f *. f;;
cube(2.);;
let pos = fun x -> x >= 0;;
pos(-2);;
pos(1);;
let pair = fun x -> x mod 2 == 0;;
pair(1);;
pair(2);;
let signe = fun x -> if x == 0 then 0 else if x < 0 then -1 else +1;;
signe (-2);;
signe(0);;
signe(+2);;

(* Exercice 6. Curry *)

let somme = fun x -> fun y -> x + y;;

let prod3entiers = fun x -> fun y -> fun z -> x * y * z;;
(((prod3entiers 1) 2) 3);;

let somme3entiers = fun x -> fun y -> fun z -> x + y + z;;
(((somme3entiers 1) 2) 3);;
somme3entiers 1 2 3;;

(* Exercice 7. Prédicats *)

let tripletpythagoricien = fun x -> fun y -> fun z -> x * x + y * y == z * z;;
(((tripletpythagoricien 3) 4) 5);;

let memesigne = fun x -> fun y -> x * y >= 0;;
memesigne (-1) (-2);;

(* Exercice 8. Types - facultatif *)

let somme = fun x -> fun y -> x + y;; (* int -> int -> int *)
somme 2 3;;
let egaux = fun x -> fun y -> x == y;; (* int -> int -> bool *)
egaux 2 2;;
egaux 2 3;;

(* Exercice 9. Minimum de deux entiers *)

let min2entiers = fun x -> fun y -> if x <= y then x else y;;
min2entiers 2 1;;
min2entiers 2 2;;
min2entiers 2 3;;

(* Exercice 10. Minimum de trois entiers *)

let min3entiers = fun x -> fun y -> fun z -> min2entiers (min2entiers x y) z;;
min3entiers 1 2 3;;
min3entiers 1 3 2;;
min3entiers 2 1 3;;
min3entiers 2 3 1;;
min3entiers 3 1 2;;
min3entiers 3 2 1;;

(* Exercice 11. Point 2D *)

let milieusegment = fun ((x1, y1), (x2, y2)) -> ((x1 + x2) / 2, (y1 + y2) / 2);;
milieusegment((0, 0), (0, 4));;
milieusegment((0, 0), (4, 4));;

let pointappartientsegment =
  fun (x, y) ->
  fun ((x1, y1), (x2, y2)) ->
  (x2-x1)/(y2-y1) == (x-x1)/(y-y1) && x <= x2 && x >= x1;;
pointappartientsegment (0, 2) ((0, 0), (0, 4));;
pointappartientsegment (1, 2) ((0, 0), (0, 4));;
pointappartientsegment (2, 2) ((0, 0), (4, 4));;

(* Exercice 12. Jour de la semaine *)

let weekend = fun j -> j == Samedi || j == Dimanche;;
weekend(Lundi);;
weekend(Samedi);;

(* Exercice 13. Aires *)

let abs = fun x -> if x >= 0 then x else -x;;

let airecarre = fun ((x1, y1), (x2, y2)) -> abs(x2 - x1) * abs(x2 - x1);;
airecarre ((0, 2), (2, 2));;
let airerectangle = fun ((x1, y1), (x2, y2)) -> abs(x2 - x1) * abs(y2 - y1);;
airerectangle ((0, 2), (2, 0));;
airerectangle ((0, 2), (3, 0));;
let airecercle = fun ((x1, y1), (x2, y2)) -> abs(x2 - x1) * abs(x2 - x1) * 3;;
airecercle ((0, 0), (3, 0));;

(* Exercice 14. Règles Uno *)

let valeurcarte =
  fun c ->
  match c with
  | Normal n ->
     (match n.t with
      | Int i -> i
      | Inversion | Passer | Plus2 -> 20)
  | Special s -> 50;;
                      
let j1 : carte = Normal( { c = Jaune ; t = Int(1) } );;
let joker : carte = Special( Joker );;
let binv : carte = Normal( { c = Bleu ; t = Inversion } );;
let rpasser : carte = Normal( { c = Bleu ; t = Passer } );;
let vplus2 : carte = Normal( {c = Vert ; t = Plus2} );;

valeurcarte j1;; (* 1 *)
valeurcarte vplus2;; (* 20 *)
valeurcarte joker;; (* 50 *)
valeurcarte rpasser;; (* 20 *)
valeurcarte binv;; (* 20 *)

let pourrajouer = fun c ->
  match c with
  | Normal n -> (match n.t with
                | Int i -> true
                | _ -> false)
  | Special s -> s == Joker;;

pourrajouer j1;; (* true *)
pourrajouer vplus2;; (* false *)
pourrajouer joker;; (* true *)
pourrajouer rpasser;; (* false *)
pourrajouer binv;; (* false *)

(* Exercice 15. Listes *)

let rec sommeliste : int list -> int =
  fun l ->
  match l with
  | [] -> 0
  | e::rl -> e + sommeliste rl;;
              
sommeliste (1::1::1::[]);;
sommeliste (1::2::3::[]);;

let rec tousposliste : int list -> bool =
  fun l ->
  match l with
  | [] -> true
  | e::rl -> (e >= 0) && tousposliste rl;;
              
tousposliste (0::1::2::[]);;
tousposliste (1::-2::3::[]);;

let rec ajfin : 'a list -> 'a -> 'a list =
  fun l ->
  fun ef ->
  match l with
  | [] -> ef::[]
  | e::rl -> e::(ajfin rl ef);;

ajfin [] 4;;
ajfin (1::2::3::[]) 4;;

let rec concat : 'a list -> 'a list -> 'a list =
  fun l1 ->
  fun l2 ->
  match l1 with
  | [] -> l2
  | e::rl -> e::(concat rl l2);;

concat (1::2::3::[]) (4::5::[]);;

(* Exercice 16. Encore du Uno ! *)

type main1 = Nil | Cons of carte * main1;;

let rec valmain1 =
  fun m ->
  match m with
  | Nil -> 0
  | Cons(c, rm) -> valeurcarte c + valmain1 rm;;

(* polymorphisme : exemple "pour de faux"
type 'a list =
  | []
  | :: of 'a * 'a list;;
 *)

(* liste (formes équivalentes) :
  Cons(7, Cons(2, Nil))
  7::(2::[])
  7::2::[]
 *)

type main2 = carte list;;

let rec valmain2 =
  fun m ->
  match m with
  | [] -> 0
  | c::rm -> valeurcarte c + valmain2 rm;;
