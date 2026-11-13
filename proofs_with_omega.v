From Coq Require Import Lia.
(* ordinary coq proof with giant term *)

(* Author: mistral/mistral-medium-latest (Capability Tier 1) *)

(* Theorem: If a number m is less than or equal to zero, then m must be equal to zero. *)
Theorem OCP_leq0_then_eq0 m (H : m <= 0) : m = 0.
Proof. lia. (*Show Proof.*) Defined.
