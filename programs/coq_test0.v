Theorem add_comm : forall a b : nat, a + b = b + a.
Proof.
  induction a as [| n hn].
  - simpl.  (* Base case: a = 0 *)
    rewrite Nat.add_0_r.
    reflexivity.
  - simpl.  (* Inductive step *)
    rewrite <- hn.
    rewrite Nat.add_succ_comm.
    reflexivity.
Qed.
