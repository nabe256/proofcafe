Require Import ssreflect ssrbool eqtype ssrnat.

Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
  apply H1.
  apply H0.
  apply H1.
Qed.

End HilbertSaxiom.
