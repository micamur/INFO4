(* Envoyer votre fichier complété à 
   jean-francois.monin@univ-grenoble-alpes.fr *)

Inductive coul : Set :=
| jaune : coul
| vert : coul
| orange : coul
| rouge : coul
| bleu : coul
| violet : coul
.

Definition perm_vr : coul -> coul :=
  fun c =>
    match c with
    | vert => rouge
    | rouge => vert
    | _ => c
    end.

(* Démontrer en commençant par une tactique de calcul *)
Theorem perm_oran : perm_vr orange = orange.
Proof.
  reflexivity.
Qed.

(* Autre preuve *)
Theorem perm_oran_bis : perm_vr orange = orange.
Proof.
  reflexivity.
Qed.

(* Que concluez vous ? --> QCM *)

Theorem deux_perm :
  forall c, perm_vr (perm_vr c) = c.
Proof.
  intro c.
  Fail destruct c as [ | | | ]. (* comprendre le message *)
(*   NE PAS REPONDRE DANS CE FICHIER--> QCM *)
  (* Terminer la preuve *)
Admitted.

Theorem trois_perm_orange :
  perm_vr (perm_vr (perm_vr orange)) = orange.
Proof.
  simpl.
  reflexivity.
Qed.

(* Réfléchir à ce qui ne va pas dans le suivant *)
(*   NE PAS REPONDRE DANS CE FICHIER--> QCM *)
Theorem trois_perm_echec :
  forall c, perm_vr (perm_vr (perm_vr c)) = c.
Proof.
Abort.

(* Décommenter, remplacer A_REMPLIR par une expression
   convenable et prouver de DEUX MANIERES *)

(* Utilisation de destruct *)
Theorem trois_perm_version1  :
  forall c, perm_vr (perm_vr (perm_vr c)) = (perm_vr c).
Proof.
  intro c.
  destruct c ; simpl ; reflexivity.
Qed.

(* Utilisation de deux_perm *)
Theorem trois_perm_version2  :
  forall c, perm_vr (perm_vr (perm_vr c)) = (perm_vr c).
Proof.
  intro c.
  apply deux_perm.
Qed.

(* Améliorer la définition suivante, suivant vos connaissances en coloriage *)
(* Version originale à conserver en commentaire
Definition melange : coul -> coul -> coul :=
  fun c1 c2 =>
    match c1, c2 with
    | jaune, bleu => vert
    | _, _ => c1
    end.
 *)

Definition melange : coul -> coul -> coul :=
  fun c1 c2 =>
    match c1, c2 with
    | jaune, bleu => vert
    | jaune, rouge => orange
    | bleu, rouge => violet
    | _, _ => c1
    end.


Inductive expcoul : Set :=
| Cst : coul -> expcoul
| Prm : expcoul -> expcoul
| Mel : expcoul -> expcoul -> expcoul
.

(* Définir la sémantique fonctionnelle de expcoul associant 
   aux constructeurs Prm et Mel les fonctions pertinentes
   parmi les précédentes.
   Suggestions : l'une des deux lignes suivantes peut servir.

Definition sf (e : expcoul) : coul :=
Fixpoint sf (e : expcoul) : coul :=

 *)

Fixpoint sf (e : expcoul) : coul :=
  match e with
  | Cst c  => c
  | Prm p  => perm_vr (sf p)
  | Mel c1 c2 => melange (sf c1) (sf c2)
end.


(* Voici un prédicat indiquant qu'une expression ne contient que du bleu *)

Fixpoint toutbleu (e : expcoul) : Prop :=
  match e with
  | Cst c => c = bleu
  | Prm e => toutbleu e
  | Mel e1 e2 => toutbleu e1 /\ toutbleu e2
  end.

(* Démontrer le théorème suivant *)
Theorem eval_tout_bleu :
  forall e, toutbleu e -> sf e = bleu.
Proof.
  intros e H.
  induction e as [ | c IH | e1 IH1 e2 IH2 ] ; simpl.
  - apply H.
  - apply IH in H.
    rewrite H.
    simpl.
    reflexivity.
  - destruct H as [ H0 H1 ].
    apply IH1 in H0.
    apply IH2 in H1.
    rewrite H0.
    rewrite H1.
    simpl.
    reflexivity.
Qed.

Section prop.
  Variables c : coul.
  Theorem t :  forall e, e = Cst c -> sf e = vert.
  Proof.
    destruct c as [ | | | | | ].
Admitted.


