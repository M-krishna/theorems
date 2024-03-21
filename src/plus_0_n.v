(* Prove that 0 + n = n *)
Theorem plus_0_n: forall n: nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

(* The above theorem can be written like this as well *)
(* We are not using "simpl." because "reflexivity." takes care of that *)
Theorem plus_0_n': forall n: nat = 0 + n = n.
Proof. intros n. reflexivity. Qed.
