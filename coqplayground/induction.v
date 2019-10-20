Require Import Basics.

Theorem plus_n_O_firsttry : forall n : nat,
    n = n + 0.

Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_O_secondtry : forall n : nat,
    n = n + 0.

Proof.
  intros [].
  - reflexivity.
  - simpl. simpl.
Abort.

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
    minus n n = 0.

Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_O_r : forall n : nat,
    n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'.reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).

Proof.
  intros n. induction n as [|n' IHn'].
  {simpl. reflexivity.}
