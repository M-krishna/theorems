(* This theorem proves that negation of negation b is b *)
(* That is not (not b) = b *)

Theorem negb_involutive: forall b: bool,
    negb (negb b) = b.
Proof.
intros b.
destruct b eqn:E.
- simpl; reflexivity.
- simpl; reflexivity.
Qed.
