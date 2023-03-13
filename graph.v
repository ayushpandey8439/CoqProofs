(** https://gist.github.com/andrejbauer/8dade8489dff8819c352e88f446154a1*)


Require Import Arith.

Notation "'all i : V, P" := (forall i:nat , i<V -> P) (at level 20, i at level 99).
Notation "'some' i: V, P" := (exists i : nat, i < V /\ P) (at level 20, i at level 99).
