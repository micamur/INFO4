(*
ABR : suppression d'un élément

1. Chercher l'élément maximum d'un ABR
2. "Supprimer l'élément maximum d'un ABR
3. "Supprimer" l'élément à la racine
4. "Supprimer" un élément dans un ABR
*)

type arbin = V | N of arbin * int * arbin;;

exception ArbreVide;;

let maxArbin (abr : arbin) : int =
  let aux (abr : arbin) : int =
    | N(_, f, V) -> f
    | N(_, _, fd) -> (aux fd)
  in
  match abr with
  | V -> raise ArbreVide
  | n -> (aux n)
;;

let supMaxArbin (abr : arbin) : arbin =
  let aux (abr : arbin) : int =
    | N(fg, x, N(fdg, y, V)) -> N(fg, x, fdg)
    | N(fg, x, fd) -> N(fg, x, (aux fd))
  in
  match abr with
  | V -> raise ArbreVide
  | n -> (aux n)
;;

let supprRacine (abr : arbin) : arbin =
  let brancheADroite (bg : arbin) (bd : arbin) : arbin = 
    V (** TODO **)
  in
  match abr with
  | V -> raise ArbreVide
  | N(V, _, V) -> Vide
  | N(fg, _, fd) -> (brancheADroite fg fd)
;;
