(* Prove 1 + n = S n *)
(* which means, if n = 1, then 1 + 1 = S 1 => 2 = 2 *)

Theorem plus_1_l: forall n: nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.
