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

End HilbertSaxiom.
