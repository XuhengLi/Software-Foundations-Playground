Require Import Induction.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).
Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x, y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O ,_ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

Theorem surjective_pairing' : forall(n m : nat),
    (n, m) = (fst (n, m), snd (n, m)).

Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros p.destruct p as [n m]. simpl. reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).

Definition mylist := cons 1 ( cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
            | O => nonzeros t
            | _ => h :: (nonzeros t)
            end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;0;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
            | true => h :: (oddmembers t)
            | _ => oddmembers t
            end
  end.

Example test_oddmembers:
  oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l : natlist): nat :=
  match oddmembers l with
  | nil => O
  | l' => length l'
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  | nil, _ => l2
  | _, nil => l1
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [4;5;6] = [4;5;6].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | h :: t => match eqb h v with
            | true => S (count v t)
            | _ => count v t
            end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  match count v s with
  | O => false
  | _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

