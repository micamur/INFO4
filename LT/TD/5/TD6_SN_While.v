(**********************  TD n°6  ***************************)
(* Ce TD porte sur la sémantique naturelle codée en Coq    *)
(* du petit langage impératif While déjà vu précédemment.  *)
(* On va l'utiliser pour faire des dérivations, montrer    *)
(* des propriétés, étudier des extensions.                 *)
(***********************************************************)

(* On importe les bibliothèques de Coq utiles pour le TD   *)

Require Import Bool Arith List.
Import List.ListNotations.


(** * On reprend les sémantiques fonctionnelles
      des expressions artihmétiques et booléennes      *)

(** * Syntaxe des expressions arithétiques *)

Inductive AExp :=
| Ana : nat -> AExp
| Ava : nat -> AExp
| Apl : AExp -> AExp -> AExp
| Amu : AExp -> AExp -> AExp
| Amo : AExp -> AExp -> AExp.


(** * On choisit de définir ici un état comme une liste d'entiers naturels.
      Une variable (Ava i) étant représentée par un entier naturel i,
      sa valeur dans l'état est la valeur de la ieme position de la liste *)

Definition State := list nat.

(** * Quelques états pour faire des tests *)

(* S1 est un état dans lequel la variable '0' vaut 1 et la variable '1' vaut 2
   et toutes les autres '0' (valeur par défaut)                                 *)
Definition S1 := [1; 2].

Definition S2 := [0; 3].
Definition S3 := [0; 7; 5; 41].

(** * La fonction get x s rend la valeur de x dans s.                                     *)
(** * Elle rend 0 par défaut, par exemple si la variable n'est pas définie/initialisée    *)

Fixpoint get (x:nat) (s:State) : nat :=
match x,s with
| 0,v::_      => v
| S x1, _::l1 => get x1 l1
| _,_         => 0
end.

(* Exemples *)

Compute (get 0 S3).
Compute (get 1 S3).
Compute (get 2 S3).
Compute (get 3 S3).
Compute (get 4 S3).

(** * La mise à jour d'une variable v par un nouvel entier n dans un état s
      s'écrit 'update s v n'
      Cette fonction n'échoue jamais et écrit la valeur à sa place même
      si elle n'est pas encore définie dans l'état *)

Fixpoint update (s:State) (v:nat) (n:nat): State :=
match v,s with
| 0, a::l1     => n :: l1
| 0, nil       => n :: nil
| S v1, a ::l1 => a :: (update l1 v1 n)
| S v1, nil    => 0 :: (update nil v1 n) end.

Definition S4 := update (update (update (update (update S1 4 1) 3 2) 2 3) 1 4) 0 5.

Compute S1.
Compute S4.

(** * Sémantique fonctionnelle pour AExp *)
Fixpoint Sfa (a : AExp) (s : State) : nat :=
  match a with
  | Ana x     => x
  | Ava x     => get x s
  | Apl a1 a2 => Sfa a1 s + Sfa a2 s
  | Amu a1 a2 => Sfa a1 s * Sfa a2 s
  | Amo a1 a2 => Sfa a1 s - Sfa a2 s
  end.

(** * Syntaxe des expressions booléennes *)

Inductive BExp :=
| Bvr : BExp
| Bfa : BExp
| Bno : BExp -> BExp
| Bet : BExp -> BExp -> BExp
| Beq : AExp -> AExp -> BExp
.

(** * Sémantique fonctionnelle pour BExp *)
Fixpoint Sfb (b: BExp) (s : State) : bool :=
  match b with
| Bvr       => true
| Bfa       => false
| Bno b1    => negb (Sfb b1 s)
| Bet b1 b2 => andb (Sfb b1 s) (Sfb b2 s)
| Beq a1 a2 => beq_nat (Sfa a1 s) (Sfa a2 s)
end.


(* Pour définir plus facilement des expressions de test on prédéfinit
   des constantes entières ... *)

Definition N0 := Ana 0.
Definition N1 := Ana 1.
Definition N2 := Ana 2.
Definition N3 := Ana 3.
Definition N4 := Ana 4.

(* ....  et des variables *)

Definition X := Ava 1.
Definition Y := Ava 2.
Definition Z := Ava 3.


(* Quelques expressions arithmétiques pour tester *)

(* exp1 = x + 3 *)
Definition E1 := Apl X N3.

(* exp2 = y - 1 *)
Definition E2 := Amo Y N1.

(* exp3 = (x + y) * 2 *)
Definition E3 := Amu (Apl X Y) N2.

Compute S1.
Compute S2.
Compute S3.

Compute (Sfa E1 S1).
Compute (Sfa E1 S2).
Compute (Sfa E2 S1).
Compute (Sfa E2 S2).
Compute (Sfa E3 S1).
Compute (Sfa E3 S2).

(* Quelques expressions booléennes pour tester *)

(* B1 :=  exp1 = 4 *)
Definition B1 := Beq E1 N4.

(* B2 := not ( bexp1 /\ (exp1 = 7) *)
Definition B2 := Bno (Bet B1 (Beq X N2)).

Compute (Sfb B1 S1).
Compute (Sfb B1 S2).
Compute (Sfb B2 S1).
Compute (Sfb B2 S2).

(* ================================================================================== *)
(** * Syntaxe du langage impératif While *)

Inductive WExp :=
| Skip  : WExp
| Ass   : nat -> AExp -> WExp
| Seq   : WExp -> WExp -> WExp
| If    : BExp -> WExp -> WExp -> WExp
| While : BExp -> WExp -> WExp.


(** *  !!!! Vu dans le TD précédent !!!!
      La sémantique naturelle (ou sémantique opérationnelle à grands pas) du langage While
      est donnée sous la forme d'un prédicat inductif. *)

Inductive SN: WExp -> State -> State -> Prop :=
| SN_skip        : forall s,             SN Skip s s
| SN_ass         : forall v a s,         SN (Ass v a) s (update s v (Sfa a s))
| SN_seq         : forall c1 c2 s s1 s2, SN c1 s s1 -> SN c2 s1 s2 -> SN (Seq c1 c2) s s2
| SN_if_true     : forall b c1 c2 s s1, (Sfb b s = true)  ->  SN c1 s s1 -> SN (If b c1 c2) s s1
| SN_if_false    : forall b c1 c2 s s2, (Sfb b s = false) ->  SN c2 s s2 -> SN (If b c1 c2) s s2
| SN_while_false : forall b c s,        (Sfb b s = false) ->  SN (While b c) s s
| SN_while_true  : forall b c s s1 s2,  (Sfb b s = true)  ->  SN c s s1 -> SN (While b c) s1 s2
                                                          ->  SN (While b c) s s2.

(** * On code dans While un programme P1 correspondant à
      while  not (i=0)) do i:=i-1;x:=1+x *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.

Definition P1 := While (Bno (Beq Ir N0)) (Seq (Ass Il (Amo Ir N1)) (Ass Xl (Apl N1 Xr))).

(** * On montre que P1 transforme l'état S1 en l'état S2  *)

Theorem reduction1 : SN P1 S1 S2.
(* Regardez les états courants tout au long de la preuve *)
Proof.
  unfold P1. unfold S1. unfold S2.

  (* apply SN_while_true. *)
  (* On peut essayer d'avancer avec 'apply SN_while_true.'  ... mais ça échoue.
     Ici Coq ne peut pas deviner ce que sera l'état intermédiaire s1. *)
  Fail apply SN_while_true.
  eapply SN_while_true.
  (* eapply introduit des variables avec un ? quand Coq ne peut pas deviner un paramètre.
     Ces variables sont liées dans les sous-cas : en prouvant le premier sous-cas nous
     allons determiner la valeur de l'état intermediaire.
     Une autre tactique possible serait d'indiquer directement l'état intermédiaire avec
     la variante 'apply ... with (s1:=..)'. Il faut deviner les paramètres corrects
     ce qui n'est pas toujours facile. Dans notre cas cela serait : *)
  (* apply SN_while_true with (s1:=[0;3]). *)
- reflexivity.
- eapply SN_seq.
  + apply SN_ass.
    (* En appliquant cette règle nous avons fixé la valeur de l'état d'arrivée *)
  + (* L'état de départ vient du cas précédent, comme les états sont connus on peut simplifier *)
    simpl.
    apply SN_ass.
- simpl.
  apply SN_while_false.
  + reflexivity.
Qed.

(** * On veut montrer maintenant que P1 rend toujours un état où
      i vaut 0 et x voit sa valeur augmenter de la valeur initiale de i           *)

(* Remarque : En Coq les entiers naturels sont définis par un type inductif :
              un entier est soit zero (représenté par O), soit le successeur d'un entier (S n).
              Un entier non nul s'écrit (S n) (que l'on peut lire comme (1 + n))  *)

Print nat.

(* Les lemmes suivants de la bibliothèque Coq peuvent être utiles
   Lemma minus_n_O : forall n, n = n - 0.
   Lemma plus_n_Sm : forall n m, S (n + m) = n + S m.
 *)

Theorem reduction2 : forall i x, SN P1 [i;x] [0;i+x].
Proof.
  intros i.
  induction i as [ | i Hrec_i] ; intros ; simpl.
  - eapply SN_while_false.
    + reflexivity.
  - eapply SN_while_true.
    + reflexivity.
    + eapply SN_seq.
      * eapply SN_ass.
      * eapply SN_ass.
    + fold P1.
      simpl.
      rewrite <- minus_n_O.
      rewrite plus_n_Sm.
      apply Hrec_i.
Qed.


(** Transformation simple de programme : if false then X else Y ---> Y  *)
Fixpoint simpl_test_Bfa (c: WExp) : WExp :=
  match c with
  | Skip => Skip
  | Ass v a => c
  | Seq w1 w2 => Seq (simpl_test_Bfa w1) (simpl_test_Bfa w2)
  | If Bfa c1 c2 => simpl_test_Bfa c2
  | If b c1 c2 => If b (simpl_test_Bfa c1) (simpl_test_Bfa c2)
  | While b c => While b (simpl_test_Bfa c)
  end.

Theorem simpl_test_Bfa_correct : forall w s s', SN w s s' -> SN (simpl_test_Bfa w) s s'.
Proof.
  intros.
  induction H.
  - simpl. eapply SN_skip.
  - simpl. eapply SN_ass.
  - simpl. eapply SN_seq.
    + apply IHSN1.
    + apply IHSN2.
  - destruct b ; try (apply SN_if_true ; auto).
    + simpl in H. discriminate H.
  - destruct b ; try (apply SN_if_false ; auto).
    + simpl. apply IHSN.
  - simpl. eapply SN_while_false.
    + rewrite H. reflexivity.
  - simpl. eapply SN_while_true.
    + rewrite H. reflexivity.
    + apply IHSN1.
    + auto.
Qed.

(** * Un prédicat inductif définit des règles de déduction
      qui sont les seules permettant de montrer le prédicat.
      Ainsi, si on a  SN Skip s1 s2         alors on peut en déduire que s1=s2
             si on a  SN (If b c1 c2) s1 s2 alors on peut en déduire que
                      soit (Sfb b s1 = true  /\ SN c1 s1 s2)
                      soit (Sfb b s1 = false /\ SN c2 s1 s2)
      C'est ce que l'on va montrer maintenant                                   *)

(** * La définition de la propriété                                             *)

Definition SN_inv_type : WExp -> State -> State -> Prop :=
  fun c s1 s2 =>
    match c with
    | Skip       => s2 = s1
    | Ass v a    => s2 = update s1 v (Sfa a s1)
    | Seq c1 c2  => exists s, SN c1 s1 s /\ SN c2 s s2
    | If b c1 c2 => (Sfb b s1 = true /\ SN c1 s1 s2) \/
                    (Sfb b s1 = false /\ SN c2 s1 s2)
    | While b c  => (Sfb b s1 = true /\ exists s, SN c s1 s /\ SN (While b c) s s2) \/
                    (Sfb b s1 = false /\ s2 = s1)
    end.

(** * Le lemme, dit "d'inversion" qui décortique les façons de prouver un prédicat. *)

Lemma SN_inv : forall c s1 s2, SN c s1 s2 -> SN_inv_type c s1 s2.
Proof.
  intros c s1 s2 H.
  destruct H; simpl.

      (* complétez ici *)
Admitted.




(** * ! Vu dans le TD précédent !
      On montre que l'on peut dérouler une boucle While c-a-d que
      'While b c' et 'If b (Seq c (While b c)) Skip' sont sémantiquement
      équivalent. *)

Theorem deroul_correct : forall b c s s', SN (While b c) s s'
                                       -> SN (If b (Seq c (While b c)) Skip) s s'.
Proof.
intros b c s s' H.
apply SN_inv in H. simpl in H.
destruct H as [[H1 [s1 [H2 H3]]]| [H2 H3]].
              (* complétez ici *)


(** * La tactique "inversion" a l'effet du lemme SN_inv pour tout prédicat inductif.   *)
(** * On utilisera la version suivante de la tactique qui simplifie un peu les choses     *)
(** * Tactique 'invert' :   *)

Ltac invert H := inversion H; clear H; subst.

(** * On remontre la propriété précédente cette fois à l'aide de 'invert'  *)

Theorem deroul_correct_inv : forall b c s s', SN (While b c) s s'
                                           -> SN (If b (Seq c (While b c)) Skip) s s'.
Proof.
intros b c s s' H.
invert H.

          (* complétez ici *)



(** * On montre maintenant l'autre sens de l'équivalence.
      A faire avec l'une des deux méthodes
      'apply SN_inv' ou 'invert'                                         *)

Theorem deroul_correct2 : forall b c s s', SN (If b (Seq c (While b c)) Skip) s s'
                                        -> SN (While b c) s s'.
Proof.
intros b c s s' H.

          (* complétez ici *)



(** * On veut maintenant montrer que
      'if b (c1;c) else (c2;c)' et '(if b than c1 else c2); c'
      sont sémantiquement équivalents.
      C'est à dire, il faut montrer                                    *)

Theorem echange_correct1 : forall b c1 c2 c s s', SN (If b (Seq c1 c) (Seq c2 c)) s s' ->
                                                  SN (Seq (If b c1 c2) c) s s'.
Proof.
        (* Complétez ici *)



(** * ... et également l'autre sens *)
Theorem echange_correct2 : forall b c1 c2 c s s', SN (Seq (If b c1 c2) c) s s' ->
                                                  SN (If b (Seq c1 c) (Seq c2 c)) s s'.
Proof.
        (* complétez ici *)




(** * On va maintenant montrer que la sémantique naturelle de While est deterministe.
      C'est à dire :                                                                    *)

Theorem SN_det : forall c s s1, SN c s s1 -> (forall s2, SN c s s2 -> s1 = s2).
Proof.
  intros c s s1 H1.
  induction H1; intros s1' H2; invert H2; auto.

(* Quand les hypothèses sont contradictoires le but est prouvé
   C'est le principe d'une preuve par contradiction.
   On peut tout déduire de Faux (forall P, False -> P).
   La tactique 'discriminate' permet de montrer n'importe quel but si dans les hypothèses
   on a une égalité, clairement fausse, entre des valeurs obtenues par des constructeurs
   différents (par ex. de la forme '0=1' ou 'true=false') *)

        (* complétez ici *)






(** * On veut maintenant étendre le langage While avec la commande
                       'Repeat c until b'
      qui exécute c puis sort si b est vrai, et sinon recommence. *)

(* Etendre la syntaxe du langage avec Repeat
  (on redéfinit un nouveau type avec de nouveaux constructeurs.    *)

Inductive WEXP :=
| SKIP  : WEXP
| ASS   : nat -> AExp -> WEXP
| SEQ   : WEXP -> WEXP -> WEXP
| IFF   : BExp -> WEXP -> WEXP -> WEXP
| WHILE : BExp -> WEXP -> WEXP
| REPEAT: (* complétez ici *).

(* Définir la sémantique naturelle du langage While étendu avec Repeat *)

Inductive SNr: WEXP -> State -> State -> Prop :=
| SNr_skip        : forall s,             SNr SKIP s s
| SNr_ass         : forall v a s,         SNr (ASS v a) s (update s v (Sfa a s))
| SNr_seq         : forall c1 c2 s s1 s2, SNr c1 s s1 -> SNr c2 s1 s2 -> SNr (SEQ c1 c2) s s2
| SNr_if_true     : forall b c1 c2 s s1, (Sfb b s = true)  ->  SNr c1 s s1 -> SNr (IFF b c1 c2) s s1
| SNr_if_false    : forall b c1 c2 s s2, (Sfb b s = false) ->  SNr c2 s s2 -> SNr (IFF b c1 c2) s s2
| SNr_while_false : forall b c s,        (Sfb b s = false) ->  SNr (WHILE b c) s s
| SNr_while_true  : forall b c s s1 s2,  (Sfb b s = true)  ->  SNr c s s1 -> SNr (WHILE b c) s1 s2
                                       -> SNr (WHILE b c) s s2
| SNr_repeat_false : (* complétez ici *)
| SNr_repeat_true  : (* complétez ici *)
.

(** * On va maintenant montrer que : 'Repeat c until b'
      peut être remplacé par       : 'c; while (not b) do c'     *)

(** * Ecrire une fonction qui remplace dans toute expression WEXP
      les repeat par l'expression équivalente ci-dessus
 *)

Fixpoint rem_repeat (c:WEXP) : WEXP :=
    match c with
    | SKIP        => SKIP
    | ASS v a     => ASS v a
    | SEQ c1 c2   =>

              (* complétez ici *)


    end.


(** * Et montrer que cette transformation préserve la sémantique c-a-d : *)

Theorem rem_repeat_correct : forall c s1 s2, SNr c s1 s2 -> SNr (rem_repeat c) s1 s2.
Proof.
intros c s1 s2 H.
induction H; simpl.


            (* complétez ici *)



(** * Optionel : En vous inspirant de l'exercice précédent prouver que l'on peut
      transformer une expression WEXP avec repeat en une expression WExp du langage
      non étendu tout en préservant sa sémantique  *)
