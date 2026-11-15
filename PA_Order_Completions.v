(* ========================================================================= *)
(* PA_Order_Completions.v                                                    *)
(* Constructive Completions (Qed.) for Arithmetic Order Properties,          *)
(* Lemma l_1_5, Cancellation, Antisymmetry, Totality, Decidability, and      *)
(* Decidable Well-Ordering / Least Number Principles from QandPA.v           *)
(* ========================================================================= *)

Require Import Arith.
Require Import QandPA.

Module PA_Order_Theorems (a : Ari) (ra : RA a) (pa : PA a ra).
  Module BasePA := TheoremsPA a ra pa.
  Import a.
  Import ra.
  Import pa.
  Import BasePA.
  Import BasePA.X.

  (* ----------------------------------------------------------------------- *)
  (* 1. Symmetric Zero Identity and Basic Order Properties                   *)
  (* ----------------------------------------------------------------------- *)

  (** Completes Q4_sym from lines 229 and 266 of QandPA.v using PA induction. *)
  Theorem Q4_sym : forall x : N, AD ZE x = x.
  Proof.
    exact AD_0_l.
  Qed.

  (** Reflexivity of LE: x <= x. *)
  Theorem LE_refl : forall x : N, LE x x.
  Proof.
    intro x.
    exists ZE.
    apply Q4.
  Qed.

  (** Transitivity of LE: a <= b -> b <= c -> a <= c (from QandPA.v line 568). *)
  Theorem LE_trans_qed : forall a b c : N, LE a b -> LE b c -> LE a c.
  Proof.
    exact LE_trans.
  Qed.

  (** Right successor monotonicity: x <= y -> x <= SU y. *)
  Theorem LE_succ_r : forall x y : N, LE x y -> LE x (SU y).
  Proof.
    intros x y [z Hz].
    exists (SU z).
    rewrite Q5.
    rewrite Hz.
    reflexivity.
  Qed.

  (** x <= SU x for all x. *)
  Theorem LE_succ_self : forall x : N, LE x (SU x).
  Proof.
    intro x.
    apply LE_succ_r.
    apply LE_refl.
  Qed.

  (** Bidirectional successor invariance: x <= y <-> SU x <= SU y. *)
  Theorem LE_succ_iff : forall x y : N, LE x y <-> LE (SU x) (SU y).
  Proof.
    intros x y.
    split.
    - intros [z Hz].
      exists z.
      rewrite <- AD_sym_lem.
      rewrite Q5.
      apply f_equal.
      exact Hz.
    - apply LE_redu.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* 2. Additive Cancellation, Zero-Sum, and Antisymmetry of LE              *)
  (* ----------------------------------------------------------------------- *)

  (** If AD x y = ZE, then both x = ZE and y = ZE. *)
  Theorem AD_eq_zero : forall x y : N, AD x y = ZE -> x = ZE /\ y = ZE.
  Proof.
    intros x y H.
    destruct (Q3 y) as [Hy | [y' Hy]].
    - rewrite Hy in H.
      rewrite Q4 in H.
      split; [exact H | exact Hy].
    - rewrite Hy in H.
      rewrite Q5 in H.
      exfalso.
      exact (Q1 (AD x y') H).
  Qed.

  (** No element x equals SU (AD x w). *)
  Theorem neq_succ_add : forall x w : N, x = SU (AD x w) -> False.
  Proof.
    apply (IND (fun x => forall w : N, x = SU (AD x w) -> False)).
    - intros w H.
      rewrite AD_0_l in H.
      exact (Q1 w (eq_sym H)).
    - intros x IH w H.
      rewrite <- AD_sym_lem in H.
      rewrite Q5 in H.
      apply Q2 in H.
      exact (IH w H).
  Qed.

  (** Left cancellation of addition: AD x y = AD x z -> y = z. *)
  Theorem AD_cancel_l : forall x y z : N, AD x y = AD x z -> y = z.
  Proof.
    intro x.
    apply (IND (fun y => forall z : N, AD x y = AD x z -> y = z)).
    - intros z H.
      rewrite Q4 in H.
      destruct (Q3 z) as [Hz | [z' Hz]].
      + symmetry; exact Hz.
      + rewrite Hz in H.
        rewrite Q5 in H.
        exfalso.
        exact (neq_succ_add x z' H).
    - intros y IH z H.
      destruct (Q3 z) as [Hz | [z' Hz]].
      + rewrite Hz in H.
        rewrite Q4 in H.
        rewrite Q5 in H.
        exfalso.
        exact (neq_succ_add x y (eq_sym H)).
      + rewrite Hz in H.
        repeat rewrite Q5 in H.
        apply Q2 in H.
        rewrite Hz.
        apply f_equal.
        exact (IH z' H).
  Qed.

  (** Antisymmetry of LE: x <= y -> y <= x -> x = y. *)
  Theorem LE_antisym : forall x y : N, LE x y -> LE y x -> x = y.
  Proof.
    intros x y [z1 Hz1] [z2 Hz2].
    assert (Hsum : AD x (AD z1 z2) = AD x ZE).
    {
      rewrite <- AD_assoc.
      rewrite Hz1.
      rewrite Hz2.
      rewrite Q4.
      reflexivity.
    }
    apply AD_cancel_l in Hsum.
    apply AD_eq_zero in Hsum.
    destruct Hsum as [Hz1_0 _].
    rewrite Hz1_0 in Hz1.
    rewrite Q4 in Hz1.
    exact Hz1.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* 3. Discreteness Dichotomy, Lemma l_1_5, and Full Totality of LE         *)
  (* ----------------------------------------------------------------------- *)

  (** Discreteness of LE: if x <= y, then either x = y or SU x <= y. *)
  Theorem LE_eq_or_succ_le : forall x y : N, LE x y -> x = y \/ LE (SU x) y.
  Proof.
    intros x y [z Hz].
    destruct (Q3 z) as [Hz0 | [z' Hz']].
    - left.
      rewrite Hz0 in Hz.
      rewrite Q4 in Hz.
      exact Hz.
    - right.
      exists z'.
      rewrite <- AD_sym_lem.
      rewrite <- Hz'.
      exact Hz.
  Qed.

  (** If y <= x, then either y = x or y <= x with SU y <= SU x;
      moreover, for any x and y, if x <= y then x <= SU y, and if y <= x then
      either SU y <= x or x = y (in which case x <= SU y). *)
  Theorem LE_step_totality : forall x y : N,
    (LE x y \/ LE y x) -> (LE x (SU y) \/ LE (SU y) x).
  Proof.
    intros x y [Hxy | Hyx].
    - left.
      apply LE_succ_r.
      exact Hxy.
    - destruct (LE_eq_or_succ_le y x Hyx) as [Heq | Hsucc].
      + left.
        rewrite Heq.
        apply LE_succ_self.
      + right.
        exact Hsucc.
  Qed.

  (** Constructive completion of Lemma l_1_5 from QandPA.v (lines 283-293):
      For every numeral (num m) and element x : N, either x <= num m or num m <= x. *)
  Theorem l_1_5 : forall (m : nat) (x : N), LE x (num m) \/ LE (num m) x.
  Proof.
    induction m as [| m IHm]; intro x.
    - simpl.
      right.
      apply l1case0.
    - simpl.
      destruct (IHm x) as [Hle | Hge].
      + left.
        apply LE_succ_r.
        exact Hle.
      + destruct (LE_eq_or_succ_le (num m) x Hge) as [Heq | Hsucc].
        * left.
          rewrite <- Heq.
          apply LE_succ_self.
        * right.
          exact Hsucc.
  Qed.

  (** Full Totality (Linearity) of LE in Peano Arithmetic:
      For all x, y : N, either x <= y or y <= x. *)
  Theorem LE_total : forall x y : N, LE x y \/ LE y x.
  Proof.
    intros x.
    apply (IND (fun y => LE x y \/ LE y x)).
    - right.
      apply l1case0.
    - intros y IHy.
      exact (LE_step_totality x y IHy).
  Qed.

  (** Strict order LT trichotomy: x < y \/ x = y \/ y < x. *)
  Theorem LT_trichotomy : forall x y : N, LT x y \/ x = y \/ LT y x.
  Proof.
    intros x y.
    destruct (LE_total x y) as [Hxy | Hyx].
    - destruct (LE_eq_or_succ_le x y Hxy) as [Heq | Hlt].
      + right; left; exact Heq.
      + left; exact Hlt.
    - destruct (LE_eq_or_succ_le y x Hyx) as [Heq | Hlt].
      + right; left; symmetry; exact Heq.
      + right; right; exact Hlt.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* 4. Decidability of Equality and Order in Peano Arithmetic               *)
  (* ----------------------------------------------------------------------- *)

  (** Every element y : N cannot satisfy SU x <= y and y <= x simultaneously. *)
  Theorem LT_not_LE : forall x y : N, LT x y -> LE y x -> False.
  Proof.
    intros x y Hlt Hle.
    unfold LT in Hlt.
    assert (Hbad : LE (SU x) x).
    {
      exact (LE_trans (SU x) y x Hlt Hle).
    }
    destruct Hbad as [z Hz].
    rewrite <- AD_sym_lem in Hz.
    rewrite Q5 in Hz.
    assert (Hz_eq : AD x (SU z) = AD x ZE).
    {
      rewrite Q5, Q4.
      exact Hz.
    }
    apply AD_cancel_l in Hz_eq.
    exact (Q1 z Hz_eq).
  Qed.

  (** Equality on N is decidable in Intuitionistic PA. *)
  Theorem eq_dec_N : forall x y : N, x = y \/ x <> y.
  Proof.
    intros x y.
    destruct (LT_trichotomy x y) as [Hlt | [Heq | Hgt]].
    - right.
      intro Heq.
      rewrite Heq in Hlt.
      exact (LT_not_LE y y Hlt (LE_refl y)).
    - left; exact Heq.
    - right.
      intro Heq.
      rewrite Heq in Hgt.
      exact (LT_not_LE y y Hgt (LE_refl y)).
  Qed.

  (** Order LE on N is decidable in Intuitionistic PA. *)
  Theorem LE_dec : forall x y : N, LE x y \/ ~ LE x y.
  Proof.
    intros x y.
    destruct (LE_total x y) as [Hxy | Hyx].
    - left; exact Hxy.
    - destruct (LE_eq_or_succ_le y x Hyx) as [Heq | Hlt].
      + left; rewrite Heq; apply LE_refl.
      + right.
        intro Hxy.
        exact (LT_not_LE y x Hlt Hxy).
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* 5. Constructive Completions of wol1, WO, and Existential LNP            *)
  (*    for Decidable Predicates (QandPA.v lines 638-674)                    *)
  (* ----------------------------------------------------------------------- *)

  (** Constructive completion of Lemma wol1 (QandPA.v line 638) in pure
      Intuitionistic PA without any decidability or excluded-middle hypothesis,
      using LE_total and LE_eq_or_succ_le: *)
  Theorem wol1 (X : N -> Prop)
    (K : ~ (exists y : N, X y /\ forall z : N, X z -> LE y z)) :
    forall z : N, ~ X z.
  Proof.
    apply (strong_induction (fun z => ~ X z)).
    - intro h0.
      apply K.
      exists ZE.
      split; [exact h0 | intros z _; apply l1case0].
    - intros y G hsy.
      apply K.
      exists (SU y).
      split; [exact hsy |].
      intros z Hz.
      destruct (LE_total (SU y) z) as [Hle | Hgt].
      + exact Hle.
      + destruct (LE_eq_or_succ_le z (SU y) Hgt) as [Heq | Hlt].
        * rewrite Heq; apply LE_refl.
        * apply LE_redu in Hlt.
          exfalso.
          exact (G z Hlt Hz).
  Qed.

  (** Auxiliary Bounded Search Lemma:
      For any decidable predicate F, for every n, either there is a least
      witness y <= n with F y, or for all z <= n, ~ F z. *)
  Theorem bounded_least_witness (F : N -> Prop)
    (Hdec : forall x : N, F x \/ ~ F x) :
    forall n : N,
      (exists y : N, LE y n /\ F y /\ forall z : N, F z -> LE y z) \/
      (forall z : N, LE z n -> ~ F z).
  Proof.
    apply (IND (fun n =>
      (exists y : N, LE y n /\ F y /\ forall z : N, F z -> LE y z) \/
      (forall z : N, LE z n -> ~ F z))).
    - destruct (Hdec ZE) as [HF0 | HnF0].
      + left.
        exists ZE.
        split; [apply LE_refl |].
        split; [exact HF0 |].
        intros z _; apply l1case0.
      + right.
        intros z Hz.
        rewrite (leq0_then_eq0 z Hz).
        exact HnF0.
    - intros n [IH_found | IH_none].
      + left.
        destruct IH_found as [y [Hyn [HFy Hmin]]].
        exists y.
        split; [apply LE_succ_r; exact Hyn |].
        split; [exact HFy | exact Hmin].
      + destruct (Hdec (SU n)) as [HFsn | HnFsn].
        * left.
          exists (SU n).
          split; [apply LE_refl |].
          split; [exact HFsn |].
          intros z Hz.
          destruct (LE_total (SU n) z) as [Hle | Hgt].
          -- exact Hle.
          -- destruct (LE_eq_or_succ_le z (SU n) Hgt) as [Heq | Hlt].
             ++ rewrite Heq; apply LE_refl.
             ++ apply LE_redu in Hlt.
                exfalso.
                exact (IH_none z Hlt Hz).
        * right.
          intros z Hz.
          destruct (LE_eq_or_succ_le z (SU n) Hz) as [Heq | Hlt].
          -- rewrite Heq; exact HnFsn.
          -- apply LE_redu in Hlt.
             exact (IH_none z Hlt).
  Qed.

  (** Constructive completion of the Well-Ordering Theorem WO (QandPA.v line 664)
      for any decidable predicate F: *)
  Theorem WO_dec (F : N -> Prop) (Hdec : forall x : N, F x \/ ~ F x) :
    (exists y : N, F y) ->
    (exists y : N, F y /\ forall z : N, F z -> LE y z).
  Proof.
    intros [n HFn].
    destruct (bounded_least_witness F Hdec n) as [[y [_ [HFy Hmin]]] | Hnone].
    - exists y.
      split; [exact HFy | exact Hmin].
    - exfalso.
      exact (Hnone n (LE_refl n) HFn).
  Qed.

  (** Constructive completion of the existential Least Number Principle LNP
      (QandPA.v line 671, with strict lower bound LT z y) for decidable F: *)
  Theorem LNP_existential_dec (F : N -> Prop) (Hdec : forall x : N, F x \/ ~ F x) :
    (exists y : N, F y) ->
    (exists y : N, F y /\ forall z : N, LT z y -> ~ F z).
  Proof.
    intro Hex.
    destruct (WO_dec F Hdec Hex) as [y [HFy Hmin]].
    exists y.
    split; [exact HFy |].
    intros z Hlt HFz.
    exact (LT_not_LE z y Hlt (Hmin z HFz)).
  Qed.

End PA_Order_Theorems.
