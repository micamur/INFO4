Fixpoint renv (l:lisstN) listN :=
    match l with
    | [] => []
    | x::r => renv r @ x::[]
end.

Fixpoint rvc (l:lisstN) (u:listN) :=
    match l with
    | [] => u
    | x::r => rvc r (x::u)
end.

let f = fun x -> 2*x.
let f x = 2*x.

(* Definition f := fun x => ... *)
(* Definition f x => ... *)

(*
forall l, rvc l [] = renv l
P l :=

- P [] = (rvc [] [] = renv [])
  trivial.

- Sachant (hyp de récurrence) rvc l [] = renv l
   Prouver rvc (x::r) [] = renv (x::r)
           rvc r (x::[]) = renv r @ (x::[])
           (par hrec)    = (rvc r []) @ (x::[])
*)

(*
forall l u, rvc l u = (renv l)@u
P l = ?
On fixe u, <---- Non !
P l rvc l u = renv l @ u
P [] : rvc [] u =? renv [] @ u
       u        =ok [] @ u

*)

(*
forall l l2 l3, (l @ l2)@l3 = l@(l2@l3)
On suppose rvc r u = renv r @ u
           rvc (x::r) u =? renv (x::r) @ u
           rvc r (x::u) ? (renv r @ (x::[])) @ u
*)

Fixpoint app l u :=
  match l with
  | [] => u
  | x::r => x::(app r u)
end.
