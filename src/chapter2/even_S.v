Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.


Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
  Proof.
  intros n.
  induction n.
  - reflexivity.
  - rewrite IHn. rewrite negb_involutive. simpl. reflexivity.
  Qed.
