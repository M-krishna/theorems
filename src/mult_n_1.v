(*
Use mult_n_Sm and mult_n_O to prove the following theorem

We can use previously proved theorem with "rewrite"
If the statement of the previously proved theorem involves quantified variables, Coq will try to fill in appropriate values for them 
by matching the body of the previous theorem statement against the current goal.
*)


Check mult_n_Sm.
Check mult_n_O.


Theorem mult_n_1: forall p: nat, p * 1 = p.
Proof.
intros p.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
simpl.
reflexivity.
Qed.
