Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
  Proof.
  intros n m.
  induction n, m eqn:E.
  - simpl. reflexivity.
  - simpl. rewrite <- E. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
  Qed.
