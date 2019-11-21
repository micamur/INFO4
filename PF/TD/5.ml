(* Un mini-interpréteur pour While *)

(* Exercice 73. *)

type constante = bool;;
type nom = A | B | C | D;;
type variable = Nom of nom * V of constante;;
type expression = V of variable | C of constante;;
type affectation = V of variable * E of expression;;

type programme =
  | Skip
  | Affect of affectation
  | Seq of programme * programme
  | If of expression * programme * programme
  | While of expression * programme;;


