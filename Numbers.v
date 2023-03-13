Module NatPlayground.

(** S is the successor constructor*)

Inductive nat :Type :=
| O 
| S (n:nat).

Definition pred(n: nat) : nat :=
match n with
| O => O
| S n' => n'
end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n:nat) : nat :=
    match n with 
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Compute (minustwo 4).

(** For recursive functions, we use Fixpoint instead of Definition. This recursively matched the conditions*)

Fixpoint even (n: nat ) : bool :=
    match n with 
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Definition odd (n: nat) : bool :=
    negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.