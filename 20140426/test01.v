Require Import List.

Theorem map_length:
  forall (A B : Type) (f : A -> B) (xs : list A),
  length (map f xs) = length xs.
Proof.
  intros A B f xs.
  induction xs.
    reflexivity.

    simpl.
    rewrite IHxs.
    reflexivity.
Qed.
