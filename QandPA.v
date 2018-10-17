Require Import Arith.

Inductive Terms:Set :=
| ZE : Terms                   (*zero*)
| SU : Terms -> Terms          (*successor*)
| AD : Terms -> Terms -> Terms (*addition*)
| MU : Terms -> Terms -> Terms (*multiplication*)
.
Notation N := Terms. (* N is a set of terms *)
Inductive RD : Prop -> Prop := (* Derivable in Robinson Arithmetic *)
| R1 : RD (forall (x:N), not (SU x = ZE))
| R2 : RD (forall (x y:N), SU x = SU y -> x = y)
| R3 : RD (forall (y:N), (y = ZE) \/ exists x:N, y = SU x)
| R4 : RD (forall (x:N), AD x ZE = x)
| R5 : RD (forall (x y:N), AD x (SU y) = SU (AD x y))
| R6 : RD (forall (x:N), MU x ZE = ZE)
| R7 : RD (forall (x y:N), MU x (SU y) = AD (MU x y) x)
.
(*Notation Q := RD.*)

Section Arithmetic.
(*Context (N:Set) (ZE:N) (SU:N->N) (AD MU:N->N->N) (*EQ:N->N->Prop*).*)

Fixpoint num (x:nat) := 
 match x return N with
 | 0 => ZE
 | S y => SU (num y)
 end.
(*Coercion num: nat >-> N.*)

Section Robinson.
Context (Q1 : forall (x:N), not (SU x = ZE)).
Context (Q2 : forall (x y:N), SU x = SU y -> x = y).
Context (Q3 : forall (y:N), (y = ZE) \/ exists x:N, y = SU x).
Context (Q4 : forall (x:N), AD x ZE = x).
Context (Q5 : forall (x y:N), AD x (SU y) = SU (AD x y)).
Context (Q6 : forall (x:N), MU x ZE = ZE).
Context (Q7 : forall (x y:N), MU x (SU y) = AD (MU x y) x).

(* Lemma 1 *)

Lemma l1_1 : forall k m, not (k = m) -> not (num m = num k).
Proof.
induction k,m.
+ intro r. exfalso. apply r. reflexivity.
+ intros r H.
  simpl in H.
  pose (y:=Q1 (num m)).
  unfold not in y.
  apply (y H).
+ intros r H. symmetry in H.
  simpl in H.
  apply (Q1 (num k) H).
+ intros r.
  simpl in r |- *.
  intro q.
  pose (g:= Q2 _ _ q).
  unshelve eapply (IHk m).
  2 : exact g.
  intro j.
  apply r.
  apply f_equal_nat, j.
Defined.

Lemma Q4_sym_num (x:nat): AD ZE (num x) = (num x).
Proof. induction x. simpl. apply Q4. simpl.
rewrite Q5. apply f_equal. apply IHx.
Defined.

Lemma not_imp_or (A B:Prop):(A\/B)->((A->False)->B).
Proof.
intros a b.
destruct a.
+ exfalso. exact (b H).
+ exact H.
Defined.

Lemma l1_2 : forall m k, AD (num k) (num m) = num (k + m).
Proof.
induction m.
+ intro k. rewrite plus_0_r. simpl. apply Q4.
+ intro k. simpl. rewrite -> Q5. rewrite -> IHm.
change (SU (num (k + m))) with (num (S (k + m))).
auto with arith.
Defined.

Lemma sum_sym : forall k m, AD (num k) (num m) = AD (num m) (num k) .
Proof. intros.
rewrite l1_2, l1_2. auto with arith.
Defined.

Lemma summ_assoc : forall a b c,
AD (AD (num a) (num b)) (num c) = AD (num a) (AD (num b) (num c)).
Proof.
intros a b c.
rewrite l1_2, l1_2.
rewrite l1_2, l1_2.
auto with arith.
Defined.

Lemma l1_3 : forall m k, MU (num k) (num m) = num (k * m).
Proof.
induction m.
+ intro k. rewrite mult_0_r. simpl. apply Q6.
+ intro k. simpl. rewrite -> Q7. rewrite -> IHm.
rewrite l1_2. apply f_equal. auto with arith.
Defined.

Lemma mul_sym : forall k m, MU (num k) (num m) = MU (num m) (num k).
Proof. intros.
rewrite l1_3, l1_3. auto with arith.
Defined.

Definition IMP : forall (x:N), exists n:nat, x = (num n).
Proof.
intros.
induction x.
+ exists 0. trivial.
+ destruct IHx as [n H].
  exists (S n). simpl. rewrite <- H. trivial.
+ destruct IHx1 as [n1 H1], IHx2 as [n2 H2].
  exists (n1 + n2). rewrite H1, H2. apply l1_2.
+ destruct IHx1 as [n1 H1], IHx2 as [n2 H2].
  exists (n1 * n2). rewrite H1, H2. apply l1_3.
Defined.

Lemma Q4_sym : forall (x:N), AD ZE x = x.
Proof.
intro x. destruct (IMP x) as [n H].
rewrite -> H. apply Q4_sym_num.
Defined.

Definition LE (x y:N) := exists z, (AD x z = y).
Lemma l_1_5 : forall (m:nat) (x:N), (LE x (num m)) \/ (LE (num m) x).
induction m.
+ intro x. simpl. right. unfold LE. exists x. exact (Q4_sym x).
+ intro x.
  destruct (IHm x).
  * left.
    admit.
  * unfold LE in H |-*.
Admitted.

Section Peano.
Context (IND : forall (P:N->Prop),
(P ZE -> (forall y:N, P y -> P (SU y))-> forall y:N, P y)).
Check Q1. (* SU x <> ZE *)
Check Q2. (* SU - injective *)
Check Q3. (*forall y : N, y = ZE \/ (exists x : N, y = SU x)*)
Check Q4. (*  forall x : N, AD x ZE = x*)
Check Q5. (*: forall x y : N, AD x (SU y) = SU (AD x y)*)
Check Q6. (*: forall x : N, MU x ZE = ZE*)
Check Q7. (*: forall x y : N, MU x (SU y) = AD (MU x y) x*)

(* Well-ordering lemmas *)
Lemma l1case0 : forall z, LE ZE z.
Proof.
unfold LE.
intro z.
exists z. 
apply (IND (fun z => AD ZE z = z)).
apply Q4.
intros y H.
rewrite Q5.
apply f_equal.
exact H.
Defined.

Lemma wol0 (X:N->Prop) : (exists y, forall z, LE y z).
Proof.
exists ZE. exact l1case0.
Defined.

(* assume X has no least element. *)

Lemma wol1 (X:N->Prop)(K:~(exists y, X y /\ forall z, (X z -> LE y z))):
forall z, ~(X z).
Proof.
intros.
apply (IND (fun z=> ~(X z))).
+ unfold not.
  intro h.
  apply K.
  exists ZE.
  split. exact h.
  intros. apply l1case0.
+ intros y H q.
  apply K.
  exists (SU y).
  split. exact q.
  intros z0 H0.
Abort.

Theorem AD_sym_lem :forall (n m:N), AD m (SU n) = AD (SU m) n.
Proof.
pose (P:= (fun n:N=> forall m : N, AD m (SU n) = AD (SU m) n)).
intro n.
apply (IND P); unfold P.
+ intro m.
  rewrite -> Q5.
  repeat rewrite -> Q4. reflexivity.
+ intros y H m.
  rewrite -> Q5.
  rewrite -> H.
  rewrite <- Q5.
  reflexivity.
Defined.

Theorem AD_sym (y x:N) : AD x y = AD y x.
Proof.
pose (P:= (fun y:N=> forall x : N, AD x y = AD y x)).
apply (IND P); unfold P.
+ apply (IND (fun x0=> AD x0 ZE = AD ZE x0)).
  * reflexivity.
  * intros.
    symmetry.
    rewrite -> Q5.
    rewrite <- H.
    rewrite -> Q4.
    rewrite -> Q4.
    reflexivity.
+ intros y0 H x0.
    rewrite -> Q5.
    rewrite H.
    rewrite <- Q5.
    apply AD_sym_lem.
Defined.

Theorem leq0_then_eq0 (m:N) (H : LE m ZE) : m = ZE.
Proof.
unfold LE in H.
destruct H as [z e].
pose (dv := Q3 m).
destruct dv.
exact H.
destruct H as [u J].
rewrite J in e.
rewrite AD_sym in e.
rewrite Q5 in e.
inversion e.
Defined.
(*simpl in e.
apply (IND (fun m=>m=ZE)).
reflexivity.
unfold AD in H.
(*remember (2+2) as tpt.*)*)
Lemma LE_redu (a y:N): LE (SU a) (SU y)-> LE a y.
Proof.
unfold LE.
intro W.
destruct W as [z U].
rewrite AD_sym in U.
rewrite Q5 in U.
apply Q2 in U.
rewrite AD_sym in U.
exists z.
exact U.
Defined.

Lemma LE_trans (a b c:N): LE a b -> LE b c -> LE a c.
Proof.
unfold LE.
intros.
Admitted.

(* strong induction *)
Section StrongInd.
Context (P:N->Prop).
Hypotheses IH0 : P ZE.
Hypotheses IHn : forall y:N, (forall z, LE z y -> P z) -> P (SU y).
Lemma strong_induction_all : forall n,
(forall m, LE m n -> P m).
Proof.
apply (IND (fun n=> forall m:N,LE m n -> P m)).
+ intros m H.
  rewrite (leq0_then_eq0 m H).
  exact IH0.
+ intros y F m l.
  destruct (Q3 m) as [H|[a b]].
  * rewrite H; exact IH0.
  * rewrite b. apply IHn.
    intro z.
    intro J.
    apply F.
    rewrite b in l.
    apply LE_redu in l.
    apply (LE_trans z a y); assumption.
Defined.

Lemma strong_induction : forall n, P n.
Proof.
intro n.
destruct (Q3 n) as [e|[x e]].
+ rewrite e; exact IH0.
+ rewrite e. apply IHn. apply strong_induction_all.
Defined.

End StrongInd.


(* Well-ordering theorem *)
Theorem WO (F:N->Prop) : 
(exists y, F y) -> (exists y, F y /\ forall z, (F z) -> LE y z).
Proof.
intro e.
Abort.
(*rewrite Q2.
simpl.
rewrite sum_sym.*)

Theorem LNP (F:N->Prop): 
(exists y, F y) -> (exists y, F y /\ forall z, LE z y -> not (F z)).
Proof.
intro e.
destruct e as [y H].
(*(exists y, F y /\ forall z, LE z y -> not (F z))*)
unfold LE.

Abort.

End Peano.


End Robinson.

