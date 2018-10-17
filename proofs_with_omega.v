Require Import Omega.
(* ordinary coq proof with giant term *)
Theorem OCP_leq0_then_eq0 m (H : m <= 0) : m = 0.
Proof. omega. (*Show Proof.*) Defined.
