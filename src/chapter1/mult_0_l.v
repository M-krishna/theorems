(* Prove 0 * n = 0 *)

Theorem mult_0_l: forall n: nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.
