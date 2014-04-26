Require Import ssreflect ssrbool eqtype ssrnat.

Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
    exact H1.
  apply H0.
  exact H1.
Qed.

End HilbertSaxiom.
