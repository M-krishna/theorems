Theorem add_0_r: forall (n: nat), n + 0 = n.
Proof.
intros n.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

