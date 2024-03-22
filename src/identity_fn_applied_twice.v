(* Prove that identity function applied twice *)
(*
What is Identity function?

In lambda calculas, an identify function is written as lambda x:x, which means it returns the input as it is as the output. It can also be
written as f x = x

What is Identity function applied twice?
In lambda calculas, it is written as lambda x:lambda y:y, which is f (f x)

*)

Theorem identity_fn_applied_twice: forall (f: bool -> bool),
    (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
intros f x b.
rewrite x.
rewrite x.
reflexivity.
Qed.

