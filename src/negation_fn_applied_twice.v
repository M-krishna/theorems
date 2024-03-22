(* What is negation function?  *)

(*
negb x = x, which means if the input is true then false.
if the input is false then true
*)

(* What is negation function applied twice? *)

(*
That is negb (negb b) = b.

We've proved this already in "negb_involutive.v"
*)


Theorem negb_involutive: forall b: bool,
    negb (negb b) = b.
Proof.
intros b.
destruct b eqn:E.
- simpl; reflexivity.
- simpl; reflexivity.
Qed.


Theorem negation_fn_applied_twice: forall (f: bool -> bool),
    (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
intros f x b.
rewrite x.
rewrite x.
rewrite negb_involution.
reflexivity.
Qed.
