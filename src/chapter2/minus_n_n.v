Fixpoint minus (a b: nat): nat :=
  match a, b with
  | O, _ => O
  | S _, O => a
  | S m', S n' => minus m' n'
  end.

Theorem minus_n_n : forall n,
  minus n n = 0.
  Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.
