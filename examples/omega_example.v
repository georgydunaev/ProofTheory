Require Import Omega.

(* Example: Prove that the sum of two even numbers is even. *)
Theorem sum_of_two_evens_is_even (n m : nat) (Hn : 2 | n) (Hm : 2 | m) : 2 | (n + m).
Proof.
  omega.
Qed.
