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

Theorem ModusPonens : (A -> B) -> A -> B.
Proof.
  intros.
  apply H.
  exact H0.
Qed.

Check hAiBiC.
Check (hAiBiC hA).
Check (hAiBiC hA (hAiB hA)).

Lemma HilbertS4 : C.
Proof.
  exact : (hAiBiC _ (hAiB _)).
Qed.

Lemma HilbertS5 : C.
Proof.
  exact : hAiBiC (hAiB _).
Qed.

Lemma HilbertS5' : C.
Proof.
  move : hAiBiC (hAiB hA).
  by apply.
Qed.

Lemma HilbertS6 : C.
Proof.
  exact : HilbertS5.
Qed.

End HilbertSaxiom.

Section Symmetric_Conjunction_Disjunction.

Lemma andb_sym : forall A B : bool,
  A && B -> B && A.
Proof.
  case.
    by case.
  by [].
Qed.


Lemma andb_sym' : forall A B : bool,
  A && B -> B && A.
Proof.
  case.
    case.
      by [].
    by case.
  by [].
Qed.

Lemma andb_sym2 : forall A B : bool,
  A && B -> B && A.
Proof.
  by case; case.
Qed.

Lemma andb_sym3 : forall A B : bool,
  A && B -> B && A.
Proof.
  by do 2! case.
Qed.

Print reflect.
Check reflect.

End Symmetric_Conjunction_Disjunction.
