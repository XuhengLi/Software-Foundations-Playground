(* (* In this case, the function definition will be rejected even if it will actually
      terminate *)
Fixpoint reject_def (b : bool) : bool :=
  match b with
| true => true
| false => (reject_def (negb b))
end.
*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite x.
  rewrite x.
  reflexivity. Qed.

Theorem negation_fn_applies_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite x.
  rewrite x.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_eq_orb:
  forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
  intros [][].
  {
    reflexivity.
  }
  {
    simpl.
    intros H.
    rewrite H.
    reflexivity.
  }
  {
    simpl.
    intros H.
    rewrite H.
    reflexivity.
  }
  {
    reflexivity.
  }
Qed.

Inductive bin : Type :=
| Z
| A (n : bin)
| B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B Z => A (B Z)
  | A m' => B m'
  | B m' => A (incr m')
  end.

Compute incr Z.
Compute (incr (incr (incr Z))).
Compute incr (incr (incr (incr Z))).
Compute incr (incr (incr (incr (incr Z)))).
Compute incr (incr (incr (incr (incr (incr Z))))).
Compute incr (incr (incr (incr (incr (incr (incr Z)))))).
Compute incr (incr (incr (incr (incr (incr (incr (incr Z))))))).

Inductive nat : Type :=
| O
| S (n : nat).

(*
Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
    | zero          => O
    | twice b'      => mult 2 (bin_to_nat b')
    | twicePlus1 b' => plus 1 (mult 2 (bin_to_nat b'))
  end.
*)
