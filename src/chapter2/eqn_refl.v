Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
  Proof.
  intros.
  induction n.
  simpl. reflexivity.
  simpl. rewrite IHn. reflexivity.
  Qed.
