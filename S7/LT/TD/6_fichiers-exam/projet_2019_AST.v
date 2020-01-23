Require Import String.
Definition word := list bool.
Definition ident := string.

Inductive oper1 : Set :=
  | Bneg
.

Inductive oper2 : Set :=
  | Shift_l
  | Shift_r
  | Wxor
  | Wand
  | Band
  | Bor
  | Cmp_eq
.

Inductive expr : Set := 
  | Ent32 : word -> expr
  | Bool : bool -> expr
  | Var : ident -> expr
  | Op1 : oper1 -> expr -> expr
  | Op2 : oper2 -> expr -> expr -> expr
.

Inductive instr : Set :=
  | Skip : instr
  | Assg : ident -> expr -> instr
  | Seq : instr -> instr -> instr
  | Par : instr -> instr -> instr
  | If : expr -> instr -> instr -> instr
  | Wh : expr -> instr -> instr
.

(* Traduction en OCaml *)
Require Import Extraction.
(* Les listes de booléens pour word seront remplacées par des int32 *)
Extract Constant word => "int32".
Extract Constant ident => "string".
Extract Inductive bool => "bool" [ "true" "false" ].
(* Fabrication du fichier *)
Extraction "expr_types.ml" instr.
