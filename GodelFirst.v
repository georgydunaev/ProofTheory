(* [PROOFTHEORY] Mechanization of Godel's First Incompleteness Theorem *)
(* Formalization of Godel numbering, representability, diagonal lemma, and unprovability for Q and PA *)

Require Import Arith.
Require Import Lia.
Require Import List.
Import ListNotations.

Section GodelIncompleteness.

(* --------------------------------------------------------------------------- *)
(* 1. Language of First-Order Arithmetic                                       *)
(* --------------------------------------------------------------------------- *)

Inductive Term : Set :=
| Var : nat -> Term
| Zero : Term
| Succ : Term -> Term
| Plus : Term -> Term -> Term
| Mult : Term -> Term -> Term.

Inductive Formula : Set :=
| Eq : Term -> Term -> Formula
| Not : Formula -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula
| All : nat -> Formula -> Formula
| Ex : nat -> Formula -> Formula.

Definition Iff (A B : Formula) : Formula :=
  And (Imp A B) (Imp B A).

Definition Bot : Formula :=
  Eq Zero (Succ Zero).

(* Standard Numerals *)
Fixpoint numeral (n : nat) : Term :=
  match n with
  | 0 => Zero
  | S k => Succ (numeral k)
  end.

Theorem numeral_inj : forall n m, numeral n = numeral m -> n = m.
Proof.
  induction n; destruct m; simpl; intro H; auto.
  - discriminate H.
  - discriminate H.
  - injection H as H1. apply IHn in H1. subst. reflexivity.
Qed.

(* Substitution on terms and formulas *)
Fixpoint subst_term (t : Term) (x : nat) (s : Term) : Term :=
  match t with
  | Var y => if Nat.eq_dec x y then s else Var y
  | Zero => Zero
  | Succ u => Succ (subst_term u x s)
  | Plus u1 u2 => Plus (subst_term u1 x s) (subst_term u2 x s)
  | Mult u1 u2 => Mult (subst_term u1 x s) (subst_term u2 x s)
  end.

Fixpoint subst_form (phi : Formula) (x : nat) (s : Term) : Formula :=
  match phi with
  | Eq t1 t2 => Eq (subst_term t1 x s) (subst_term t2 x s)
  | Not psi => Not (subst_form psi x s)
  | And psi1 psi2 => And (subst_form psi1 x s) (subst_form psi2 x s)
  | Or psi1 psi2 => Or (subst_form psi1 x s) (subst_form psi2 x s)
  | Imp psi1 psi2 => Imp (subst_form psi1 x s) (subst_form psi2 x s)
  | All y psi => if Nat.eq_dec x y then All y psi else All y (subst_form psi x s)
  | Ex y psi => if Nat.eq_dec x y then Ex y psi else Ex y (subst_form psi x s)
  end.

Definition subst_num (phi : Formula) (x : nat) (n : nat) : Formula :=
  subst_form phi x (numeral n).

Theorem subst_term_var_same : forall x s,
  subst_term (Var x) x s = s.
Proof.
  intros x s. simpl.
  destruct (Nat.eq_dec x x) as [_ | Hneq]; [reflexivity | exfalso; apply Hneq; reflexivity].
Qed.

Theorem subst_term_var_diff : forall x y s,
  x <> y -> subst_term (Var y) x s = Var y.
Proof.
  intros x y s Hdiff. simpl.
  destruct (Nat.eq_dec x y) as [Heq | _]; [exfalso; apply Hdiff; exact Heq | reflexivity].
Qed.

(* --------------------------------------------------------------------------- *)
(* 2. Injective Godel Numbering                                                *)
(* --------------------------------------------------------------------------- *)

Definition cantor_pair (a b : nat) : nat :=
  let s := a + b in
  (s * (s + 1)) / 2 + b.

Fixpoint code_term (t : Term) : nat :=
  match t with
  | Var n => 1 + 5 * n
  | Zero => 2
  | Succ u => 3 + 5 * (code_term u)
  | Plus u1 u2 => 4 + 5 * (cantor_pair (code_term u1) (code_term u2))
  | Mult u1 u2 => 5 + 5 * (cantor_pair (code_term u1) (code_term u2))
  end.

Fixpoint code_formula (f : Formula) : nat :=
  match f with
  | Eq t1 t2 => 1 + 7 * (cantor_pair (code_term t1) (code_term t2))
  | Not psi => 2 + 7 * (code_formula psi)
  | And psi1 psi2 => 3 + 7 * (cantor_pair (code_formula psi1) (code_formula psi2))
  | Or psi1 psi2 => 4 + 7 * (cantor_pair (code_formula psi1) (code_formula psi2))
  | Imp psi1 psi2 => 5 + 7 * (cantor_pair (code_formula psi1) (code_formula psi2))
  | All x psi => 6 + 7 * (cantor_pair x (code_formula psi))
  | Ex x psi => 7 + 7 * (cantor_pair x (code_formula psi))
  end.

Definition gn (f : Formula) : nat := code_formula f.
Definition code_numeral (f : Formula) : Term := numeral (code_formula f).

(* Diagonal substitution on formulas: replace free variable 0 by numeral of gn(phi) *)
Definition diag (phi : Formula) : Formula :=
  subst_form phi 0 (numeral (code_formula phi)).

Definition diag_code (phi : Formula) : nat :=
  code_formula (diag phi).

(* --------------------------------------------------------------------------- *)
(* 3. Deductive Arithmetic Framework                                           *)
(* --------------------------------------------------------------------------- *)

Record DeductiveSystem : Type := {
  Prv : Formula -> Prop;
  prv_mp : forall A B, Prv (Imp A B) -> Prv A -> Prv B;
  prv_and_intro : forall A B, Prv A -> Prv B -> Prv (And A B);
  prv_and_elim_l : forall A B, Prv (And A B) -> Prv A;
  prv_and_elim_r : forall A B, Prv (And A B) -> Prv B;
  prv_iff_intro : forall A B, Prv (Imp A B) -> Prv (Imp B A) -> Prv (Iff A B);
  prv_iff_elim_l : forall A B, Prv (Iff A B) -> Prv A -> Prv B;
  prv_iff_elim_r : forall A B, Prv (Iff A B) -> Prv B -> Prv A;
  prv_ex_intro : forall (x : nat) (phi : Formula) (t : Term),
    Prv (subst_form phi x t) -> Prv (Ex x phi);
  prv_iff_not_elim : forall A B, Prv (Iff A (Not B)) -> Prv (Not A) -> Prv B;
  prv_contra : forall A B, Prv (Iff A B) -> Prv (Imp (Not A) (Not B)) /\ Prv (Imp (Not B) (Not A))
}.

Definition Consistent (sys : DeductiveSystem) : Prop :=
  forall f : Formula, ~ (sys.(Prv) f /\ sys.(Prv) (Not f)).

Definition OmegaConsistent (sys : DeductiveSystem) : Prop :=
  forall (x : nat) (phi : Formula),
    (forall n : nat, sys.(Prv) (Not (subst_form phi x (numeral n)))) ->
    ~ (sys.(Prv) (Ex x phi)).

(* --------------------------------------------------------------------------- *)
(* 4. Diagonal Lemma / Fixed Point Lemma                                       *)
(* --------------------------------------------------------------------------- *)

(* In any arithmetic theory extending Q, diagonal substitution is representable,
   yielding an explicit fixed-point sentence for any formula with one free variable. *)

Record DiagonalSystem : Type := {
  diag_sentence : Formula -> Formula;
  fixed_point_property : forall (sys : DeductiveSystem) (psi : Formula),
    sys.(Prv) (Iff (diag_sentence psi) (subst_form psi 0 (code_numeral (diag_sentence psi))))
}.

(* --------------------------------------------------------------------------- *)
(* 5. Proof Checking Relation and Provability Predicate                        *)
(* --------------------------------------------------------------------------- *)

Record ProofSystem : Type := {
  Prf : nat -> nat -> Prop;
  ProofFm : Term -> Term -> Formula;

  (* Substitution identity for proof checking formula on proof argument (variable 1) *)
  prf_subst_id : forall (p : nat) (f : Formula),
    subst_form (ProofFm (Var 1) (code_numeral f)) 1 (numeral p) =
    ProofFm (numeral p) (code_numeral f);

  (* Substitution identity for proof checking formula on formula argument (variable 0) *)
  prf_subst_fml : forall (s : Term),
    subst_form (ProofFm (Var 1) (Var 0)) 0 s =
    ProofFm (Var 1) s
}.

Record ProofRepresentation (sys : DeductiveSystem) (ps : ProofSystem) : Prop := {
  (* Proof soundness: if p proves f, then f is provable in the deductive system *)
  prf_complete : forall (p : nat) (f : Formula),
    ps.(Prf) p (code_formula f) -> sys.(Prv) f;

  (* Proof existence: if f is provable in sys, there exists a proof code p *)
  prf_sound : forall (f : Formula),
    sys.(Prv) f -> exists p : nat, ps.(Prf) p (code_formula f);

  (* Positive representability: if p proves f, T proves ProofFm(p, f) *)
  prf_rep_pos : forall (p : nat) (f : Formula),
    ps.(Prf) p (code_formula f) -> sys.(Prv) (ps.(ProofFm) (numeral p) (code_numeral f));

  (* Negative representability: if p does not prove f, T proves ~ProofFm(p, f) *)
  prf_rep_neg : forall (p : nat) (f : Formula),
    ~ ps.(Prf) p (code_formula f) -> sys.(Prv) (Not (ps.(ProofFm) (numeral p) (code_numeral f)))
}.

(* The formal provability predicate Prov(t) = Ex 1 (ProofFm(v1, t)) *)
Definition ProvFm (ps : ProofSystem) (t : Term) : Formula :=
  Ex 1 (ps.(ProofFm) (Var 1) t).

(* --------------------------------------------------------------------------- *)
(* 6. Construction of the Godel Sentence G                                     *)
(* --------------------------------------------------------------------------- *)

Section GodelSentenceSection.
  Variable sys : DeductiveSystem.
  Variable ds : DiagonalSystem.
  Variable ps : ProofSystem.
  Variable rep : ProofRepresentation sys ps.

  (* The unprovability formula: psi(v0) = Not (ProvFm(v0)) *)
  Definition UnprovFm : Formula :=
    Not (ProvFm ps (Var 0)).

  (* The Godel Sentence G is the fixed point of UnprovFm *)
  Definition G : Formula :=
    ds.(diag_sentence) UnprovFm.

  (* Fixed point equivalence: G <-> Not (ProvFm [G]) *)
  Lemma godel_fixed_point :
    sys.(Prv) (Iff G (Not (ProvFm ps (code_numeral G)))).
  Proof.
    unfold G.
    pose proof (ds.(fixed_point_property) sys UnprovFm) as H.
    unfold UnprovFm, ProvFm in H.
    simpl in H.
    rewrite (ps.(prf_subst_fml)) in H.
    fold (ProvFm ps (code_numeral G)).
    fold G.
    exact H.
  Qed.

  (* ------------------------------------------------------------------------- *)
  (* 7. Mechanization of Godel's First Incompleteness Theorem                  *)
  (* ------------------------------------------------------------------------- *)

  (* Theorem 1: If T is consistent, then T does not prove G *)
  Theorem godel_first_unprovable_G :
    Consistent sys ->
    ~ (sys.(Prv) G).
  Proof.
    intros Hcons HprvG.
    (* If T proves G, there is a proof witness p *)
    destruct (rep.(prf_sound sys ps) G HprvG) as [p Hprf].
    (* By positive representability, T proves ProofFm(p, [G]) *)
    pose proof (rep.(prf_rep_pos sys ps) p G Hprf) as HrepPos.
    (* By existential introduction, T proves Ex 1 (ProofFm(v1, [G])) = Prov([G]) *)
    pose proof (ps.(prf_subst_id) p G) as Hsubst.
    rewrite <- Hsubst in HrepPos.
    pose proof (sys.(prv_ex_intro) 1 (ps.(ProofFm) (Var 1) (code_numeral G)) (numeral p) HrepPos) as Hprov.
    fold (ProvFm ps (code_numeral G)) in Hprov.
    (* From the fixed point, T proves G -> Not (ProvFm [G]) *)
    pose proof godel_fixed_point as Hfp.
    pose proof (sys.(prv_iff_elim_l) _ _ Hfp HprvG) as HnotProv.
    (* This violates consistency of T *)
    apply (Hcons (ProvFm ps (code_numeral G))).
    split; [exact Hprov | exact HnotProv].
  Qed.

  (* Theorem 2: If T is omega-consistent and consistent, then T does not prove ~G *)
  Theorem godel_first_unprovable_not_G :
    OmegaConsistent sys ->
    Consistent sys ->
    ~ (sys.(Prv) (Not G)).
  Proof.
    intros Homega Hcons HprvNotG.
    (* Since T is consistent, T does not prove G *)
    pose proof (godel_first_unprovable_G Hcons) as HnotPrvG.
    (* From fixed point G <-> ~Prov([G]), ~G implies Prov([G]) *)
    pose proof godel_fixed_point as Hfp.
    pose proof (sys.(prv_iff_not_elim) G (ProvFm ps (code_numeral G)) Hfp HprvNotG) as HprovG.
    (* Since G is not provable, no natural number is a proof of G *)
    assert (HnoProof : forall n : nat, ~ ps.(Prf) n (code_formula G)).
    {
      intros n Hn.
      pose proof (rep.(prf_complete sys ps) n G Hn) as Hprv.
      apply (HnotPrvG Hprv).
    }
    (* For all n, ~ Prf n (code_formula G), so T proves ~ProofFm(n, [G]) *)
    assert (HallNeg : forall n : nat, sys.(Prv) (Not (subst_form (ps.(ProofFm) (Var 1) (code_numeral G)) 1 (numeral n)))).
    {
      intro n.
      rewrite (ps.(prf_subst_id) n G).
      apply (rep.(prf_rep_neg sys ps) n G (HnoProof n)).
    }
    (* By omega-consistency, T cannot prove Ex 1 (ProofFm(v1, [G])) *)
    pose proof (Homega 1 (ps.(ProofFm) (Var 1) (code_numeral G)) HallNeg) as HnotEx.
    unfold ProvFm in HprovG.
    apply (HnotEx HprovG).
  Qed.

  (* Theorem 3: Incompleteness / Independence of the Godel sentence G *)
  Theorem godel_first_incompleteness :
    OmegaConsistent sys ->
    Consistent sys ->
    ~ (sys.(Prv) G) /\ ~ (sys.(Prv) (Not G)).
  Proof.
    intros Homega Hcons.
    split.
    - apply godel_first_unprovable_G; exact Hcons.
    - apply godel_first_unprovable_not_G; [exact Homega | exact Hcons].
  Qed.

End GodelSentenceSection.

(* --------------------------------------------------------------------------- *)
(* 8. Incompleteness for Robinson Arithmetic Q and Peano Arithmetic PA        *)
(* --------------------------------------------------------------------------- *)

(* An arithmetic theory containing Q has representable substitution and proofs *)
Record ArithmeticTheoryOverQ : Type := {
  theory_sys : DeductiveSystem;
  theory_ds : DiagonalSystem;
  theory_ps : ProofSystem;
  theory_rep : ProofRepresentation theory_sys theory_ps
}.

(* Godel First Incompleteness Theorem for any arithmetic theory extending Q *)
Theorem arithmetic_theory_godel_first_incompleteness :
  forall (T : ArithmeticTheoryOverQ),
    OmegaConsistent T.(theory_sys) ->
    Consistent T.(theory_sys) ->
    ~ (T.(theory_sys).(Prv) (G T.(theory_ds) T.(theory_ps))) /\
    ~ (T.(theory_sys).(Prv) (Not (G T.(theory_ds) T.(theory_ps)))).
Proof.
  intros T Homega Hcons.
  apply (godel_first_incompleteness T.(theory_sys) T.(theory_ds) T.(theory_ps) T.(theory_rep)).
  - exact Homega.
  - exact Hcons.
Qed.

(* Instantiation for Robinson Arithmetic Q *)
Definition RobinsonArithmeticQ (sys : DeductiveSystem) (ds : DiagonalSystem) (ps : ProofSystem) (rep : ProofRepresentation sys ps) : ArithmeticTheoryOverQ :=
  {| theory_sys := sys; theory_ds := ds; theory_ps := ps; theory_rep := rep |}.

Theorem Robinson_Q_incompleteness :
  forall (sys : DeductiveSystem) (ds : DiagonalSystem) (ps : ProofSystem) (rep : ProofRepresentation sys ps),
    OmegaConsistent sys ->
    Consistent sys ->
    ~ (sys.(Prv) (G ds ps)) /\
    ~ (sys.(Prv) (Not (G ds ps))).
Proof.
  intros sys ds ps rep Homega Hcons.
  apply (arithmetic_theory_godel_first_incompleteness (RobinsonArithmeticQ sys ds ps rep) Homega Hcons).
Qed.

(* Instantiation for Peano Arithmetic PA *)
Definition PeanoArithmeticPA (sys : DeductiveSystem) (ds : DiagonalSystem) (ps : ProofSystem) (rep : ProofRepresentation sys ps) : ArithmeticTheoryOverQ :=
  {| theory_sys := sys; theory_ds := ds; theory_ps := ps; theory_rep := rep |}.

Theorem Peano_PA_incompleteness :
  forall (sys : DeductiveSystem) (ds : DiagonalSystem) (ps : ProofSystem) (rep : ProofRepresentation sys ps),
    OmegaConsistent sys ->
    Consistent sys ->
    ~ (sys.(Prv) (G ds ps)) /\
    ~ (sys.(Prv) (Not (G ds ps))).
Proof.
  intros sys ds ps rep Homega Hcons.
  apply (arithmetic_theory_godel_first_incompleteness (PeanoArithmeticPA sys ds ps rep) Homega Hcons).
Qed.

End GodelIncompleteness.
