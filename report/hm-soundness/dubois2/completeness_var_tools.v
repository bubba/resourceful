(* Author : Catherine Dubois *)


Require Import List.
Require Import Le.
Require Import tools.
Require Import langs.
Require Import type_scheme.
Require Import order_stamp.
Require Import max.
Require Import subst.
Require Import Plus.
Require Import generic_DB.
Require Import new_tv.



(*******************************************************************)
Fixpoint compute_subst (st : stamp) (l : list type) {struct l} :
 substitution :=
  match l return substitution with
  | nil =>
      (*nil*)  nil
  | t :: l' =>
      (*cons t l'*)  (st, t) :: compute_subst (succ_stamp st) l'
  end.

(*******************************************************************)

Lemma apply_subst_app :
 forall (s1 s2 : substitution) (st : stamp),
 assoc_stamp_in_subst st s1 = Ident_not_in_subst ->
 apply_substitution ( (*stamp*type*) s1 ++ s2) st = apply_substitution s2 st.
intros.
unfold apply_substitution in |- *.
elim (ident_in_subst_inv (assoc_stamp_in_subst st s2)).
intro Hyp; elim Hyp; clear Hyp; intros t Hyp; rewrite Hyp.
rewrite (assoc_stamp_in_subst_app s1 s2 st t); auto.

intro Hyp; rewrite Hyp.
rewrite (assoc_stamp_in_subst_app3 s1 s2 st H Hyp); auto.
Qed.

(*******************************************************************)
Lemma apply_app :
 forall (s1 s2 : substitution) (st : stamp) (t : type),
 assoc_stamp_in_subst st s1 = Ident_in_subst t ->
 apply_substitution ( (*stamp*type*) s1 ++ s2) st = t.

intros; unfold apply_substitution in |- *.
rewrite (assoc_stamp_in_subst_app2 s1 s2 st t H); auto.
Qed.
(*******************************************************************)

Lemma not_in_domain_compute :
 forall (sg : list type) (x st : stamp),
 lt_stamp x st ->
 assoc_stamp_in_subst x (compute_subst st sg) = Ident_not_in_subst.
Proof.
simple induction sg; auto.
do 5 intro; elim st; intros n Hyp; simpl in |- *; rewrite eq_stamp_diff; auto.
simpl in |- *; apply H; auto.
Qed.

(*******************************************************************)

Lemma apply_app_compute_subst :
 forall (s0 : substitution) (st s : stamp) (sg : list type),
 lt_stamp s st ->
 apply_substitution ( (*stamp*type*) compute_subst st sg ++ s0) s =
 apply_substitution s0 s.
Proof.
intros; apply apply_subst_app.
apply not_in_domain_compute; auto.
Qed.


(*******************************************************************)

Lemma nth_compute :
 forall p k st : nat,
 S k <= p ->
 nth k (fst (compute_generic_subst (Stamp st) p)) =
 Nth_in (Var (Stamp (st + k))).
Proof.
simple induction p.
simpl in |- *; intros; inversion H.

intros n ind k st.
rewrite Fst_compute_generic_subst.
case k; simpl in |- *.
rewrite plus_comm; auto.

intros; rewrite ind; auto with *.
simpl in |- *; rewrite (plus_comm st (S n0)).
simpl in |- *; rewrite (plus_comm n0 st); auto.
Qed.

(*******************************************************************)

Lemma compute_subst_cons_rwt :
 forall (st : stamp) (t : type) (sg : list type),
 compute_subst st ( (*type*) t :: sg) =
  (*stamp*type*) (st, t) :: compute_subst (succ_stamp st) sg.
auto.
Qed.


(********************************************************************)
Lemma assoc_stamp_compute :
 forall (i : nat) (sg : list type) (st : nat) (t : type),
 nth i sg = Nth_in t ->
 assoc_stamp_in_subst (Stamp (st + i)) (compute_subst (Stamp st) sg) =
 Ident_in_subst t.
Proof.
simple induction i.
simpl in |- *; intros sg st t.
rewrite <- plus_n_O.
case sg; simpl in |- *.
intros; discriminate H.
 
intros; rewrite eq_nat_reflexivity; simpl in |- *.
inversion H; auto.

intros n ind sg st t.
case sg.
simpl in |- *; intros pb; discriminate pb.

intros; rewrite compute_subst_cons_rwt.
simpl in |- *.
rewrite eq_nat_plus_p_Sn_and_p; simpl in |- *.
rewrite <- plus_Snm_nSm; auto.
Qed.
Hint Resolve assoc_stamp_compute.
(*used by Auto in t_is_app_T_aux*)


(********************************************************************)

Lemma t_is_app_T_aux :
 forall (TS : type_scheme) (T t : type) (s : substitution) 
   (p : nat) (st : stamp) (sg : list type),
 new_tv_type_scheme TS st ->
 max_gen_vars TS <= p ->
 apply_subst_gen (fst (compute_generic_subst st p)) TS = Some_subst_gen T ->
 apply_subst_gen sg (extend_subst_type_scheme s TS) = Some_subst_gen t ->
 t = extend_subst_type ( (*stamp*type*) compute_subst st sg ++ s) T.

Proof.
simple induction TS.
(*Nat_ts*)
simpl in |- *; intros.
inversion_clear H1; inversion_clear H2; auto.
(*Var x*)
simpl in |- *; intros x T t s p st sg tv_hyp le_hyp T_def.
inversion_clear T_def.
rewrite apply_subst_gen_type_to_type_scheme.
intro def_t; inversion_clear def_t.
inversion_clear tv_hyp.
simpl in |- *; rewrite apply_app_compute_subst; auto.
(*Gen x*)
intro x; elim x; simpl in |- *; intros a T t s p st; elim st;
 intros n sg tv_hyp le_hyp.
rewrite (nth_compute p a n le_hyp).
intro def_T; inversion_clear def_T; simpl in |- *.
elim (nth_answer_inv (nth a sg)); intro Hyp.
elim Hyp; clear Hyp; intros t0 t0_def; rewrite t0_def.
intro some_to_is_some_t; inversion some_to_is_some_t.
rewrite <- H0.
rewrite (apply_app (compute_subst (Stamp n) sg) s (Stamp (n + a)) t0); auto.
rewrite Hyp; intro pb; discriminate pb.
(*Arrow*)
intros ts1 ind1 ts2 ind2 T t s p st sg tv_hyp le_hyp Hyp.
simpl in le_hyp.
elim
 (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 T
    (fst (compute_generic_subst st p)) Hyp).
intro x; elim x; clear x; intros T1 T2 Hyp_Elim; elim Hyp_Elim;
 clear Hyp_Elim; intros Hyp_T1 Hyp_Elim; elim Hyp_Elim; 
 clear Hyp_Elim; intros Hyp_T2 def_T.
rewrite def_T; rewrite <- extend_subst_ts_arrow_rewrite; intro Hyp1.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (extend_subst_type_scheme s ts1)
    (extend_subst_type_scheme s ts2) t sg Hyp1).
intro x; elim x; clear x; intros t1 t2 Hyp_Elim; elim Hyp_Elim;
 clear Hyp_Elim; intros Hyp_t1 Hyp_Elim; elim Hyp_Elim; 
 clear Hyp_Elim; intros Hyp_t2 def_t.
rewrite def_t; simpl in |- *.
inversion_clear tv_hyp.
rewrite <- (ind1 T1 t1 s p st sg); auto.
rewrite <- (ind2 T2 t2 s p st sg); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.










