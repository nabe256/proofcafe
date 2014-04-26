Require Import ssreflect ssrbool eqtype ssrnat.

Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  move=> hAiBiC hAiB hA.
  move: hAiBiC.
  apply.
    by [].
  by apply: hAiB.
Qed.

Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).

Lemma HilbertS2 : C.
Proof.
  apply : hAiBiC; first by apply : hA.
  exact : hAiB.
Qed.

Lemma HilbertS2' : C.
Proof.
  move:hAiBiC.
  apply.
    by [].
  exact : hAiB.
Qed.

Lemma HilbertS3 : C.
Proof.
  by apply: hAiBiC; last exact: hAiB.
Qed.

End HilbertSaxiom.
