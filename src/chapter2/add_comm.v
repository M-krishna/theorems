Theorem add_comm : forall n m : nat,
  n + m = m + n.
  Proof.
  intros n m.
  induction m, n as [|n' IHn'] eqn:E.
  - reflexivity.
  - rewrite <- E. rewrite add_0_r. rewrite add_0_l. reflexivity.
  - simpl. rewrite <- IHm. rewrite plus_n_Sm. simpl. reflexivity.
  - rewrite <- plus_n_Sm. rewrite IHm. rewrite <- E. rewrite plus_n_Sm. simpl. rewrite <- plus_n_Sm. reflexivity.
  Qed.
