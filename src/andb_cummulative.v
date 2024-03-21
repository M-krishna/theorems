(* Prove andb b c = andb c b *)
(*
There are 4 cases
* when b is true
* when b is false
* when c is true
* when c is false 
*)

(* There is more than one way to write the proof, let's look at all. *)

Theorem andb_cummulative: forall b c: bool, andb b c = andb c d.
Proof.
intros b c.
destruct b, c.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
Qed.


(* Using bullets. '-' and '+' *)
Theorem andb_cummulative: forall b c: bool, andb b c = andb c d.
Proof.
intros b c.
destruct b eqn:Eb.
- destruct c eqn:Ec.
    + simpl. reflexivity.
    + simpl. reflexivity.
- destruct c eqn:Ec.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.
