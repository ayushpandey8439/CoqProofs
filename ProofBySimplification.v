Require Import Arith.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
    intros n. reflexivity. Qed.

Theorem plus_1_l : forall n :nat, 1 + n = S n.
Proof.
    intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
    intros n. reflexivity. Qed.


Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity. Qed.   

Theorem plus_id_exercise : forall n m o : nat,
    n = m ->
    m = o -> 
    n + m = m + o.
  Proof.
    intros n m o.
    intros H.
    intros H1.
    rewrite -> H.
    rewrite -> H1.
    reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
   (n + 1) =? 0 = false.
  Proof.
    intros n.
    destruct  n as [|n'] eqn:E.
    - reflexivity.
    - reflexivity.
    Qed.

Theorem andb_true_elim2: forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c eqn: C.
    -destruct b eqn: B.
      +reflexivity.
      +reflexivity.
    -destruct b eqn: B.
      +discriminate.
      +discriminate. 
Qed.
  
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
    intros n.
    destruct n as [|n'] eqn:E.
    - reflexivity.
    - reflexivity. Qed.

Theorem identity_fn_applied_twice:
forall (f: bool -> bool),
(forall (x: bool), f x = x) ->
(forall (x: bool), f (f x) = x).
Proof.
  intros.
  rewrite H.
  apply H.
Qed.


Theorem negation_fn_applied_twice:
forall (f: bool -> bool),
(forall (x: bool), f x = negb x) ->
(forall (x: bool), f (f x) = x).
Proof.
  intros.
  rewrite H.
  rewrite H.
  destruct x.
  - reflexivity.
  - reflexivity. Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros.
  destruct b.
  -destruct c.
    +reflexivity.
    +discriminate.
  -destruct c.
    +discriminate.
    +reflexivity. Qed.

Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin).

Fixpoint incr (m:bin) : bin:=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : (incr (B0 (B0 (B1 Z)))) = B1 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

