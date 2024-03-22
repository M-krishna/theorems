(* Prove (andb b c) is equal to (orb b c) which implies b is equal to c *)

Theorem andb_eq_orb: forall (b c: bool),
    (andb b c = orb b c) -> b = c.
Proof.
intros.
destruct b eqn:Eb.
- destruct c eqn:Ec.
    + reflexivity.
    + simpl in H. rewrite <- H. reflexivity.
- destruct c eqn:Ec.
    + simpl in H. rewrite <- H. reflexivity.
    + reflexivity.
Qed.
