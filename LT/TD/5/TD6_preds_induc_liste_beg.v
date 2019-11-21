Require Import List.

Print length.

Inductive begaie {A: Type} : list A -> Prop :=
| Bnil : begaie nil
| Bcc : forall x l, begaie l -> begaie (x :: x :: l).

Fixpoint echanges {A: Type} (l : list A) : list A :=
    match l with
    | x :: y :: r => y :: x :: echanges r
    | _ => l
    end.

Theorem beg_ech_invar : forall A (l: list A), begaie l -> echanges l = l.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl. rewrite IHbegaie. reflexivity.
Qed.

Inductive pair : nat -> Prop :=
| P0 : pair 0
| P2 : forall n, pair n -> pair (S (S n)).

Theorem nbp : forall A (l: list A), begaie l -> pair (length l).
Proof.
  intros.
  induction H ; simpl.
  - apply P0. (* ou constructor *)
  - apply P2. apply IHbegaie.
Qed.

Inductive begloin  {A: Type} : list A -> Prop :=
| Blnil : begloin nil
| Blca : forall x u v, begloin (u ++ v) -> begloin (x :: u ++ x :: v).

Search (length (_ ++ _)).
Print PeanoNat.Nat.add_succ_r.

Theorem nblp : forall A (l: list A), begloin l -> pair (length l).
Proof.
  intros.
  induction H ; simpl.
  - apply P0.
  - rewrite app_length.
    simpl.
    rewrite PeanoNat.Nat.add_succ_r.
    rewrite <- app_length.
    apply P2.
    apply IHbegloin.
Qed.

Inductive begloin'  {A: Type} : list A -> Prop :=
| Blnil' : begloin' nil
| Blca' : forall x u v w, begloin' (u ++ v ++ w) -> begloin' (u ++ x :: v ++ x :: w).

Theorem nblp' : forall A (l: list A), begloin' l -> pair (length l).
Proof.
  intros.
  induction H ; simpl.
  - apply P0.
  - rewrite app_length.
    simpl.
    rewrite PeanoNat.Nat.add_succ_r.
    simpl.
    rewrite app_length.
    simpl.
    rewrite PeanoNat.Nat.add_succ_r.
    rewrite <- app_length.
    rewrite PeanoNat.Nat.add_succ_r.
    apply P2.
    rewrite <- app_length.
    apply IHbegloin'.
Qed.
