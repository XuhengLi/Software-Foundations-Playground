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
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).

Proof.
  intros n m. induction n as [|n' IHn'].
  { simpl. reflexivity. }
  {
    induction m as [|m' IHm'].
    { simpl. rewrite -> IHn'. reflexivity. }
    { simpl. rewrite -> IHn'. reflexivity. }
  }
Qed.

Theorem plus_comm : forall n m : nat,
    n +  m = m + n.

Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p: nat,
    n + (m + p) = (n + m) + p.

Proof.
  intros n m p. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem mult_O_plus' : forall n m : nat,
    (0 + n) * m = n * m.

Proof.
  intros n m.
  assert (H : 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert ( H : n + m = m + n ).
  {rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.
