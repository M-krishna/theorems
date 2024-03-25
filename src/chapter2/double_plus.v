Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.



(* Two ways of solving the theorem, syntactically different *)
Lemma double_plus : forall n, double n = n + n.
Proof.
intros n. induction n as [|n']. 
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
  Qed.

Lemma double_plus' : forall n, double n = n + n.
Proof.
intros.
induction n.
simpl. reflexivity.
simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.
