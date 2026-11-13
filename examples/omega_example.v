Require Import Arith PeanoNat.
From Coq Require Import Lia.

(* Example: Prove that the sum of two even numbers is even. *)
Theorem sum_of_two_evens_is_even (n m : nat) (Hn : Nat.divide 2 n) (Hm : Nat.divide 2 m) : Nat.divide 2 (n + m).
Proof.
  destruct Hn as [a Ha].
  destruct Hm as [b Hb].
  exists (a + b).
  lia.
Qed.
