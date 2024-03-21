(* Prove and b c  = true implies c = true *)


(* Variant 1 *)
Theorem andb_true_elim2: forall b c: bool,
  andb b c = true -> c = true.
Proof.
intros b c.
intros H.
destruct b eqn:Eb.
- destruct c eqn:Ec.
  + simpl. reflexivity.
  + destruct H. simpl. reflexivity.
- destruct c eqn:Ec.
  + simpl. reflexivity.
  + destruct H. simpl. reflexivity.
Qed.



(* Above theorem using "rewrite" *)
Theorem andb_true_elim3: forall b c: bool,
  andb b c = true -> c = true.
Proof.
intros b c.
intros H.
destruct b eqn:Eb.
- destruct c eqn:Ec.
  + simpl. reflexivity.
  + rewrite <- H. simpl. reflexivity.
- destruct c eqn:Ec.
  + simpl. reflexivity.
  + rewrite <- H. simpl. reflexivity.
Qed.


(* Make it simpler *)
Theorem andb_true_elim4: forall b c: bool,
  andb b c = true -> c = true.
Proof.
intros b c.
intros H.
destruct b eqn:Eb.
- destruct c eqn:Ec.
  + reflexivity.
  + rewrite <- H. reflexivity.
- destruct c eqn:Ec.
  + reflexivity.
  + rewrite <- H. reflexivity.
Qed.
