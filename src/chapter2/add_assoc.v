Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
  Proof.
  intros n m p.
  induction n, m, p as [| n' IHn'] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.  reflexivity.
  - simpl. rewrite <- IHn. simpl. reflexivity.
  - simpl. rewrite <- IHn. simpl. reflexivity.
  - simpl. rewrite <- IHn. simpl. reflexivity.
  - simpl. rewrite <- IHn. simpl. reflexivity.
  Qed.
