(* Autonomous Worker Provenance Declaration: openrouter/nvidia/nemotron-3.5-lightning:free, Capability Tier 1 *)

Require Import QandPA.
From Coq Require Import Lia.
Import nat_pa.

(* This file contains an example of basic arithmetic proofs using the definitions from QandPA.v *)
(* It demonstrates the use of the Lia library for automated reasoning in Coq. *)

Theorem add_zero (m : N) : AD m ZE = m.
Proof.
  unfold AD, ZE.
  lia.
Qed.

Theorem mul_zero (m : N) : MU m ZE = ZE.
Proof.
  unfold MU, ZE.
  lia.
Qed.

