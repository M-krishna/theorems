(* Prove that n + 1 is not equal to 0 *)
(* This theorem introduces the use of destruct tactic *)


Fixpoint eqb (a b: nat): bool :=
  match a, b with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S m, S n => eqb m n
  end.
  
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0: forall n: nat,
    (n + 1) =? 0 = false.
Proof.
intros n.
destruct n. (* this gives us two subgoals to prove. One is n = 0 and the other n = S n' *)
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


(* The above theorem can also be written as *)
Theorem plus_1_neq_0': forall n: nat,
    (n + 1) =? 0 = false.
Proof.
intros n.
destruct n as [| n'] eqn:E.
- simpl; reflexivity.
- simpl; reflexivity.
Qed.

(*
* The part "as [| n']" is called intro pattern
* "eqn:E", eqn is short for equation and E is the name of the equation. Instead of E we can have anything.
* The "-" signs are called bullets. Since we have two subgoals to prove, each bullet indicates a subgoal
*)
