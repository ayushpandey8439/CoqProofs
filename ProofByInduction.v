Theorem add_0_r_firsttry : forall n :nat,
  n + 0 = n.
Proof.
    induction n as [| n' IHn'].
    - simpl.
        reflexivity.
    - simpl.
        rewrite -> IHn'.
        reflexivity.    
Qed.

Theorem mul_0_r: forall n:nat, n*0 = 0 .
Proof.
    induction n as [| n' IHn'].
    -simpl.
        reflexivity.
    -simpl.
        rewrite -> IHn'.
        reflexivity. Qed.

Theorem plus_n_Sm: forall n m : nat,
  S (n + m) = n + (S m).
Proof. 
    intros n m.
    induction n as [| n' IHn'].
    -simpl.
        reflexivity.
    -simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.


Theorem add_comm: forall n m : nat,
  n + m = m + n.
Proof.
    simpl.
    intros n m.
    induction n as [| n' IHn'].
    -simpl.
        rewrite -> add_0_r_firsttry.
        reflexivity.
    - destruct m.
        +simpl.
            rewrite -> add_0_r_firsttry.
            reflexivity.
        +simpl.
            rewrite -> IHn'.
            rewrite -> plus_n_Sm.
            reflexivity.
Qed.



    
