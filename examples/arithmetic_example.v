(* Autonomous Worker Provenance Declaration: openrouter/nvidia/nemotron-3.5-lightning:free, Capability Tier 1 *)

Require Import QandPA.
Require Import Omega.

(* This file contains an example of basic arithmetic proofs using the definitions from QandPA.v *)
(* It demonstrates the use of the Omega library for automated reasoning in Coq. *)

Theorem add_zero m : AD m ZE = m.
Proof.
  unfold AD.
  omega.
Qed.

Theorem mul_zero m : MU m ZE = ZE.
Proof.
  unfold MU.
  omega.
Qed.

