(* This theorem is part of Software foundations book *)

(* Prove for all natural numbers n and m, n = m implies n + n = m + m *)

Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
Proof.
intros n m.
intros H.
rewrite -> H.
reflexivity.
Qed.


(*
intros n m.	    -> moves n and m variable to the current context of the goal
intros H.	    -> moves the hypothesis n = m to the current context of the goal
rewrite -> H.	    -> (->) tells coq to replace whatever is on the left side of the equality with right. since n = m, then n + n = m + m becomes
		    m + m = m + m
reflexivity.	    -> checks the equality on both sides.
*)
