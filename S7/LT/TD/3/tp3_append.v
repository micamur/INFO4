(** Preuves par récurrence structurelle sur des listes,
    propriétés élémentaires de la concaténation app.
    Pour se concentrer sur l'essentiel, on considère
    des  listes d'entiers naturels
 *)

(** Rappel des tactiques déjà vues
- reflexivity, rewrite (égalités)
- apply (application d'une hypothèse ou d'un lemme)
- intro, intros (implications et quantifications universelles en conclusion)
- destruct (décomposition d'une hypothèse, raisonnement par cas)
- induction (récurrence structurelle)
- left, right (disjonction)
- split (conjonction)
- simpl, cbn, hnf, unfold (calcul)
*)

(* Listes d'entiers naturels *)
Inductive listN : Set :=
 | Nil : listN
 | Cons : nat -> listN -> listN.

(* Concaténation *)
Fixpoint app (l1 : listN) (l2 : listN) : listN :=
  match l1 with
   | Nil => l2
   | Cons x r1 => Cons x (app r1 l2)
  end.

Theorem app_neutre_droite : forall l, app l Nil = l.
Proof.
Admitted.

Section sec_app_assoc.

  Variables l2 l3 : listN.

  Theorem app_assoc_section : forall l, app (app l l2) l3 = app l (app l2 l3).
  Proof.
  Admitted.
  
  (* Visualiser le théorème obtenu, avant fermeture de la section *)
  Check app_assoc_section.

End sec_app_assoc.

(* Visualiser le théorème obtenu, une fois la section fermée  *)
Check app_assoc_section.

(* Refaire la preuve précédente en dehors d'une section, comme suit *)

Theorem app_assoc : forall l l2 l3, app (app l l2) l3 = app l (app l2 l3).
Proof.
  intros l l2 l3.
  induction l as [ | x r Hrec_r ] ; simpl.
Admitted.

Check app_assoc.

(** Avec de jolies notations *)

Infix "::" := Cons (at level 60, right associativity).
Notation "[ ]" := Nil (format "[ ]").
Infix "@" := app (right associativity, at level 60).

(* Remarquer la différence avec OCaml :
- En OCaml les listes n'ont pas le même type suivant qu'elles sont fabriquées 
  avec Nil et Cons ou avec [] et ::, même si les valeurs sont semblables.
  De la même façon 
- En Coq, l'utilisation faite ci-dessus de [] et :: 
  procure un artifice d'écriture, les véritables noms de constructeurs
  sous-jacents restent Nil et Cons
 *)

Check Nil.
About "[ ]".
About "::".
Print app.

About "::".
Print Cons.
Theorem app_neutre : forall l, app l Nil = l.
Proof.
  intro l.
  destruct l as [ l | x r ].
  - simpl. reflexivity.
  - simpl. destruct r as [ | y rr ].
    + simpl. reflexivity.
      (* On peut noter x :: ([] @ []) = x :: [] *)
    + simpl. destruct rr as [ | z rrr ].
      (* On peut noter x :: (y :: rr) @ [] = x :: y :: rr *)
      * simpl. reflexivity.
      * Abort.
(* On a essayé de faire tous les cas possibles *)

Theorem app_neutre : forall l, app l Nil = l.
Proof.
  intro l.
  induction l as [ | x r Hrec_r ] ; simpl.
  - reflexivity.
  - rewrite Hrec_r. reflexivity.
Qed.
(* Ça marche mieux en faisant de la récurrence *)

Fail check app_neutre_par_cas.

Fixpoint app_neutre_pf (l : listN) : app l Nil = l.
Proof.
(*
  Check (app_neutre l).
  apply (app_neutre l).
Fail Qed.
*)
  destruct l as [ | x r ] ; simpl.
  - reflexivity.
  - Check (app_neutre r).
    rewrite (app_neutre r). reflexivity.
Qed.

Print app.
Print app_neutre_pf.

Theorem app_neutre_droite_joli : forall l, l @ [] = l.
Proof.
Admitted.

Check app_assoc.

Section sec_app_assoc_joli.

  Variables l2 l3 : listN.

  Theorem app_assoc_section_joli : forall l, (l @ l2) @ l3 = l @ (l2 @ l3).
  Proof.
  Admitted.
  
End sec_app_assoc_joli.

Theorem app_assoc_joli : forall l l2 l3, (l @ l2) @ l3 = l @ (l2 @ l3).
Proof.
Admitted.

Fixpoint rve (l:listN) (u:listN) :=
  match l with
  | [] => u
  | x::r => rve r(x::u)
end.

Fixpoint renv (l:listN) :=
  match l with
  | [] => []
  | x::r => renv r @ (x::[])
end.

Print renv.

Lemma rve_renv_aux : forall l u, rve l u = renv l @ u.
Proof.
  intros l.
  induction l as [ | x r Hrec_r ] ; simpl ; intro u0.
  - reflexivity.
  - Check (Hrec_r (1 :: 2 :: [])).
    Check (Hrec_r (x :: u0)).
    rewrite (Hrec_r (x :: u0)).
    Check (app_assoc (renv r) (x :: []) u0).
    Check (app_assoc).
    Check (app_assoc (renv r) (x :: [])).
    rewrite (app_assoc (renv r) (x :: []) u0). simpl. reflexivity.
    Undo 3.
    rewrite app_assoc. reflexivity.
    Show Proof.
Qed.

Theorem rve_renv : forall l, rve l [] = renv l.
Proof.
  intro l.
  Check (rve_renv_aux l []).
  rewrite (rve_renv_aux l []). simpl.
  Check app_neutre.
  Check (app_neutre l).
  apply (app_neutre l).

  induction l as [ | x r Hr ].
  - simpl. reflexivity.
  - simpl.

