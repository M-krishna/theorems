(* This exercise is part of the software foundations book *)
(* Theorem: for all natural numbers n, m and o. prove n = m implies m = o implies n + m = m + o *)


Theorem plus_id_example: forall n m o: nat,
    n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H1 H2.
rewrite -> H1.
rewrite -> H2.
reflexivity.
Qed.


(*
intros n m o.	    -> moves n, m and o variables to the current context of the goal
intros H1 H2.	    -> moves the hypothesis(n = m and m = o) to the current context of the goal. H1 holds n = m and H2 holds m = o
rewrite -> H1.	    -> replaces left side of equality with right side. So, n + m becomes m + m
rewrite -> H2.	    -> replaces left side of equality with right side. So, m + m becomes o + o. Finally we have o + o = o + o
reflexivity.	    -> checks equality on both sides and proves the theorem.
*)
