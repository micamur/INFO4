
type word = int32

type ident = string

type oper1 =
| Bneg

type oper2 =
| Shift_l
| Shift_r
| Wxor
| Wand
| Band
| Bor
| Cmp_eq

type expr =
| Ent32 of word
| Bool of bool
| Var of ident
| Op1 of oper1 * expr
| Op2 of oper2 * expr * expr

type instr =
| Skip
| Assg of ident * expr
| Seq of instr * instr
| Par of instr * instr
| If of expr * instr * instr
| Wh of expr * instr
