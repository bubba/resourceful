(* Author : Catherine Dubois *)

Require Import langs.
Require Import List.
Require Import Plus.
Require Import Le.
Require Import generic_DB.
Require Import new_tv.
Require Import subst.
Require Import order_stamp.
Require Import type_scheme.
Require Import tools.
Require Import env_poly.
Require Import max.
Require Import W.
Require Import W_inversion.
Require Import type_system.
Require Import unification.
Require Import more_general.
Require Import tools_stable.
Require Import completeness_var_tools.
Require Import s_gen_more_general_than_gen_s.

(******************************************************************)
Lemma max_gen_vars_Gen_var :
 forall n : nat, max_gen_vars (Gen_var (Stamp n)) = S n.
auto.
Qed.
(******************************************************************)

Lemma value_of_snd_compute_generic_subst :
 forall p n : nat, snd (compute_generic_subst (Stamp n) p) = Stamp (n + p).
Proof.
simple induction p.
simpl in |- *; intro; rewrite <- plus_n_O; auto.

intros; rewrite Snd_compute_generic_subst; simpl in |- *.
rewrite H; simpl in |- *.
rewrite (plus_comm n0 (S n)); simpl in |- *.
rewrite (plus_comm n0 n); auto.
Qed.

(********************************************************************)
Lemma new_tv_type_compute_generic_subst :
 forall (st : stamp) (ts : type_scheme) (t : type) (p : nat),
 new_tv_type_scheme ts st ->
 max_gen_vars ts <= p ->
 apply_subst_gen (fst (compute_generic_subst st p)) ts = Some_subst_gen t ->
 new_tv_type t (snd (compute_generic_subst st p)).

simple induction ts.
(*Nat*)
simpl in |- *; intros; inversion_clear H1; auto.

(*Var*)
elim st; intro n.
simpl in |- *; intros; inversion_clear H1; inversion_clear H.
rewrite value_of_snd_compute_generic_subst.
apply new_tv_type_trans_le with (x1 := Stamp n); auto with *.


(*Gen*)
do 3 intro; elim st; intro n; elim s; intros m hyp.
rewrite max_gen_vars_Gen_var; intro le_hyp.
unfold apply_subst_gen in |- *.
rewrite (nth_compute p m n); auto.
intro; inversion_clear H.
rewrite value_of_snd_compute_generic_subst; auto with *.

(*Arrow*)
elim st; intros n ts1 ind_ts1 ts2 ind_ts2 t p new_hyp le_hyp; simpl in le_hyp.
inversion_clear new_hyp.
intro apply_susbt_hyp.
elim
 (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 t
    (fst (compute_generic_subst (Stamp n) p)) apply_susbt_hyp).
intro x; elim x; intros tau1 tau2 y; elim y; intros.
elim H2; intros.
rewrite H4.
rewrite value_of_snd_compute_generic_subst; simpl in |- *.
apply new_tv_Arrow.
apply
 new_tv_type_trans_le with (x1 := snd (compute_generic_subst (Stamp n) p)).

apply ind_ts1; auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.

rewrite value_of_snd_compute_generic_subst; auto.

apply
 new_tv_type_trans_le with (x1 := snd (compute_generic_subst (Stamp n) p)).
apply ind_ts2; auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.

rewrite value_of_snd_compute_generic_subst; auto.
Qed.

(******************************************************************)

Inductive principal_type :
type -> substitution -> type -> substitution -> stamp -> Prop :=
    intro_princ_type :
      forall (T t : type) (S s : substitution) (st : stamp),
      {sigma : substitution |
      t = extend_subst_type sigma T /\
      (forall x : stamp,
       lt_stamp x st ->
       apply_substitution s x =
       extend_subst_type sigma (apply_substitution S x))} ->
      principal_type T S t s st.


(***********************************)
Inductive F : stamp -> environment -> expr -> type -> substitution -> Prop :=
    intro_F :
      forall (st : stamp) (env : environment) (e : expr) 
        (t : type) (s : substitution),
      {S_T_st' : substitution * type * stamp |
      let (S, T) return Prop := fst S_T_st' in
      W st env e = Some_infer T S (snd S_T_st') /\ principal_type T S t s st} ->
      F st env e t s.

(*******************************************************************)
Lemma stamp_increases_in_compute_generic_subst :
 forall (n : nat) (st : stamp),
 le_stamp st (snd (compute_generic_subst st n)).
Proof.
simple induction n; auto.

intros; elim st; intro m.
rewrite Snd_compute_generic_subst.
apply le_stamp_trans with (st2 := succ_stamp (Stamp m)); auto.
Qed.

(****************************************************************************)
Lemma stamp_increases_in_W :
 forall (e : expr) (st st' : stamp) (env : environment) 
   (t : type) (s : substitution),
 W st env e = Some_infer t s st' -> le_stamp st st'.
simple induction e.
(*NAT*)
simpl in |- *; intros.
inversion_clear H; auto.

(*VAR*)
intros.
elim (W_var_inversion st st' env i t s H).
intros ts and1; elim and1; intros H1 and2; elim and2; intros H2 and3;
 elim and3; intros H3 H4; clear and1 and2 and3.
rewrite <- H4; apply stamp_increases_in_compute_generic_subst.

(*Lambda i e*)
simple induction st; intros.
elim (W_lambda_inversion n st' env e0 i t s H0).  
intros t' and1; elim and1; intros H1 H2; clear and1.
apply le_stamp_trans with (st2 := Stamp (S n)); auto.
apply
 (H (Stamp (S n)) st' (add_environment env i (Var_ts (Stamp n))) t' s H1).

(*Rec  i i0 e0*)
simple induction st; intros.
elim (W_rec_inversion n st' env e0 i i0 t s H0).
intros tau_subst_U; elim tau_subst_U; intros tau subst_U; elim subst_U;
 intros subst U. 
intros and1; elim and1; intros H1 and2; elim and2; intros H2 and3; elim and3;
 intros H3 H4; clear and1 and2 and3.
apply le_stamp_trans with (st2 := Stamp (S (S n))); auto.
apply
 (H (Stamp (S (S n))) st'
    (add_environment (add_environment env i0 (Var_ts (Stamp n))) i
       (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n))))) tau subst H1).

(*apply e0 e1*)
intros.
elim (W_apply_inversion st st' env e0 e1 t s H1).
intros t1_S1_st1_t2_S2_n2_U; elim t1_S1_st1_t2_S2_n2_U;
 intros t1_S1_st1_t2_S2_n2 U; elim t1_S1_st1_t2_S2_n2;
 intros t1_S1_st1 t2_S2_n2; elim t1_S1_st1; intros t1_S1 st1; 
 elim t2_S2_n2; intros t2_S2 n2; elim t1_S1; intros t1 s1; 
 elim t2_S2; intros t2 s2.
intros and1; elim and1; intros H2 and2; elim and2; intros H3 and3; elim and3;
 intros H4 and4; elim and4; intros H5 and5; elim and5; 
 intros H6 H7; clear and1 and2 and3 and4 and5 H4 H5 H6.
rewrite H7.
apply le_stamp_trans with (st2 := Stamp n2); auto.
apply le_stamp_trans with (st2 := st1).
apply (H st st1 env t1 s1 H2).

apply (H0 st1 (Stamp n2) (apply_subst_env env s1) t2 s2 H3).

(*let*)
intros.
elim (W_let_inversion st st' env e0 e1 i t s H1).
intros t1_s1_st1_s2; elim t1_s1_st1_s2; intros t1_s1_st1 s2; elim t1_s1_st1;
 intros t1_s1 st1; elim t1_s1; intros t1 s1.
intros and1; elim and1; intros H2 and2; elim and2; intros H3 H4;
 clear and1 and2 H4.
apply le_stamp_trans with (st2 := st1).
apply (H st st1 env t1 s1 H2).
apply
 (H0 st1 st'
    (add_environment (apply_subst_env env s1) i
       (gen_type t1 (apply_subst_env env s1))) t s2 H3).
Qed.

(***********************************************************************)
Lemma new_tv_W :
 forall (e : expr) (st st' : stamp) (env : environment) 
   (t : type) (s : substitution),
 new_tv_env env st ->
 W st env e = Some_infer t s st' -> new_tv_type t st' /\ new_tv_subst s st'.
Proof.
simple induction e.
(*NAT*)
simpl in |- *; intros.
inversion_clear H0; auto.

(*VAR*)
intros.
elim (W_var_inversion st st' env i t s H0).
intros ts and1; elim and1; intros H1 and2; elim and2; intros H2 and3;
 elim and3; intros H3 H4; clear and1 and2 and3.
rewrite H1.
split; auto.
rewrite <- H4.
apply (new_tv_type_compute_generic_subst st ts t (max_gen_vars ts)); auto.
apply (new_tv_env_implies_new_tv_ts env ts st i H2 H).

(*Lambda*)
simple induction st; intros.
elim (W_lambda_inversion n st' env e0 i t s H1).  
intros t' and1; elim and1; intros Hyp1 Hyp2; clear and1.
elim (H (Stamp (S n)) st' (add_environment env i (Var_ts (Stamp n))) t' s);
 auto.
intros.
rewrite Hyp2; simpl in |- *; split; auto.
(* (new_tv_type (Arrow (apply_substitution s (Stamp n)) t') st')*)
apply new_tv_Arrow; auto.
apply new_tv_s_stamp; auto.

apply lt_le_stamp_trans with (st2 := Stamp (S n)); auto.
apply
 (stamp_increases_in_W e0 (Stamp (S n)) st'
    (add_environment env i (Var_ts (Stamp n))) t' s Hyp1).

apply new_tv_add_env; auto.
apply new_tv_env_trans_le with (st1 := Stamp n); auto.

(*Rec*)
simple induction st; intros.
elim (W_rec_inversion n st' env e0 i i0 t s H1).
intros tau_subst_U; elim tau_subst_U; intros tau subst_U; elim subst_U;
 intros subst U.
intros and1; elim and1; intros Hyp1 and2; elim and2; intros Hyp2 and3;
 elim and3; intros Hyp3 Hyp4; clear and1 and2 and3.
elim
 (H (Stamp (S (S n))) st'
    (add_environment (add_environment env i0 (Var_ts (Stamp n))) i
       (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n))))) tau subst); 
 auto.
intros new_tau_st' new_subst_st'.
generalize
 (stamp_increases_in_W e0 (Stamp (S (S n))) st'
    (add_environment (add_environment env i0 (Var_ts (Stamp n))) i
       (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n))))) tau subst Hyp1).
intro le_stamp_S_S_n_st'.
cut (new_tv_subst (compose_subst subst U) st'). 
intro new_tv_subst_compose_st'.

rewrite <- Hyp4; rewrite Hyp3; simpl in |- *; split.
apply new_tv_Arrow.
apply new_tv_s_stamp; auto.
apply lt_le_stamp_trans with (st2 := Stamp (S (S n))); auto.
apply new_tv_s_stamp; auto.

auto.

(*   (new_tv_subst (compose_subst subst U) st') *)
apply new_tv_compose_subst; auto.
apply (new_tv_mgu tau (extend_subst_type subst (Var (Stamp (S n)))) st' U);
 auto.
simpl in |- *; apply new_tv_s_stamp; auto.

(*
  (new_tv_env
     (add_environment (add_environment env i0 (Var_ts (Stamp n))) i
       (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n)))))
     (Stamp (S (S n))))
*)
apply new_tv_add_env; auto.
apply new_tv_add_env; auto.
apply new_tv_env_trans_le with (st1 := Stamp n); auto.

(*Apply*)
intros.
elim (W_apply_inversion st st' env e0 e1 t s H2).
intros t1_S1_st1_t2_S2_n2_U; elim t1_S1_st1_t2_S2_n2_U;
 intros t1_S1_st1_t2_S2_n2 U; elim t1_S1_st1_t2_S2_n2;
 intros t1_S1_st1 t2_S2_n2; elim t1_S1_st1; intros t1_S1 st1; 
 elim t2_S2_n2; intros t2_S2 n2; elim t1_S1; intros t1 s1; 
 elim t2_S2; intros t2 s2.
intros and1; elim and1; intros Hyp2 and2; elim and2; intros Hyp3 and3;
 elim and3; intros Hyp4 and4; elim and4; intros Hyp5 and5; 
 elim and5; intros Hyp6 Hyp7; clear and1 and2 and3 and4 and5.
elim (H st st1 env t1 s1 H1 Hyp2); intros.
generalize (stamp_increases_in_W e0 st st1 env t1 s1 Hyp2).
intro.
elim (H0 st1 (Stamp n2) (apply_subst_env env s1) t2 s2); auto.
intros.
generalize
 (stamp_increases_in_W e1 st1 (Stamp n2) (apply_subst_env env s1) t2 s2 Hyp3).
intro.
cut (new_tv_subst U (Stamp (S n2))).
intro.
cut (new_tv_subst (compose_subst (compose_subst s1 s2) U) (Stamp (S n2))). 
intro new_tv_subst_compose_st'.

rewrite Hyp6; rewrite Hyp7; rewrite Hyp5; split; auto.
(* (new_tv_type (extend_subst_type U (Var (Stamp n2))) (Stamp (S n2)))*)
simpl in |- *; apply new_tv_s_stamp; auto.

(*  (new_tv_subst (compose_subst (compose_subst s1 s2) U) (Stamp (S n2))) *)
apply new_tv_compose_subst; auto.
apply new_tv_compose_subst.
apply new_tv_subst_trans with (x1 := st1); auto.
apply le_stamp_trans with (st2 := Stamp n2); auto.

apply new_tv_subst_trans with (x1 := Stamp n2); auto.

(*  (new_tv_subst U (Stamp (S n2)))*)
apply
 (new_tv_mgu (extend_subst_type s2 t1) (Arrow t2 (Var (Stamp n2)))
    (Stamp (S n2)) U); auto.
apply new_tv_s_type.
apply (new_tv_type_trans_le t1 st1 (Stamp (S n2)) H3); auto.
apply le_stamp_trans with (st2 := Stamp n2); auto.
apply new_tv_subst_trans with (x1 := Stamp n2); auto.

apply new_tv_Arrow; auto.
apply new_tv_type_trans_le with (x1 := Stamp n2); auto.


(*   (new_tv_env (apply_subst_env env s1) st1)*)
apply new_tv_s_env; auto.
apply new_tv_env_trans_le with (st1 := st); auto.


(*Let*)
intros.
elim (W_let_inversion st st' env e0 e1 i t s H2).
intros t1_s1_st1_s2; elim t1_s1_st1_s2; intros t1_s1_st1 s2; elim t1_s1_st1;
 intros t1_s1 st1; elim t1_s1; intros t1 s1.
intros and1; elim and1; intros Hyp2 and2; elim and2; intros Hyp3 Hyp4;
 clear and1 and2.
elim (H st st1 env t1 s1 H1 Hyp2); intros.
generalize (stamp_increases_in_W e0 st st1 env t1 s1 Hyp2).
intro.
elim
 (H0 st1 st'
    (add_environment (apply_subst_env env s1) i
       (gen_type t1 (apply_subst_env env s1))) t s2); 
 auto.
intros.
(*Elim (stamp_increases_in_W e1 ..
Cut (le_stamp st1 st')
Intro.
*)
rewrite Hyp4; split; auto.
(*(new_tv_subst (compose_subst s1 s2) st')*)
apply new_tv_compose_subst; auto.
apply new_tv_subst_trans with (x1 := st1); auto.
(*(le_stamp st1 st')*)
apply
 (stamp_increases_in_W e1 st1 st'
    (add_environment (apply_subst_env env s1) i
       (gen_type t1 (apply_subst_env env s1))) t s2 Hyp3).
(*   (new_tv_env
     (add_environment (apply_subst_env env s1) i
       (gen_type t1 (apply_subst_env env s1))) st1)
*)
apply new_tv_add_env.
apply new_tv_s_env; auto.
apply new_tv_env_trans_le with (st1 := st); auto.

(*(new_tv_type_scheme (gen_type t1 (apply_subst_env env s1)) st1)*)
apply new_tv_gen_type; auto.
apply new_tv_s_env; auto.
apply new_tv_env_trans_le with (st1 := st); auto.

Qed.


(************************************************************************)
Lemma completeness_lambda :
 forall (i : identifier) (e : expr),
 (forall (env : environment) (t : type) (s : substitution) (st : stamp),
  type_of (apply_subst_env env s) e t -> new_tv_env env st -> F st env e t s) ->
 forall (env : environment) (t : type) (s : substitution) (st : stamp),
 type_of (apply_subst_env env s) (Lambda i e) t ->
 new_tv_env env st -> F st env (Lambda i e) t s.
Proof.
do 7 intro; elim st; intro n; intros.
inversion_clear H0.
cut
 (F (Stamp (S n)) (add_environment env i (Var_ts (Stamp n))) e t'
    (add_subst s (Stamp n) t0)).
intro Hyp_cut; inversion_clear Hyp_cut.
elim H0; clear H0.
intro Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut.
intro n_uplet; elim n_uplet; clear n_uplet.
intros S' T' st0; simpl in |- *.
intros Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros.
apply intro_F.
exists (S', Arrow (extend_subst_type S' (Var (Stamp n))) T', st0).
simpl in |- *; rewrite H0.
split; auto.
inversion_clear H3.
elim H4; clear H4; intros sigma Hyp; elim Hyp; clear Hyp.
intros.
apply intro_princ_type.
exists sigma; split; simpl in |- *.
rewrite <- H3; rewrite <- H4.
rewrite add_subst_rewrite_for_modified_stamp; auto.

auto.

intros; rewrite <- (add_subst_rewrite_for_unmodified_stamp s (Stamp n) x t0).
apply H4; auto.

apply lt_stamp_n_m_diff; auto.

apply
 (H (add_environment env i (Var_ts (Stamp n))) t' (add_subst s (Stamp n) t0)
    (Stamp (S n))).
rewrite add_subst_add_env; auto.

apply new_tv_add_env; auto.
apply new_tv_env_trans_le with (st1 := Stamp n); auto.
Qed.

(********************************************************************)
Lemma completeness_rec :
 forall (i i0 : identifier) (e : expr),
 (forall (env : environment) (t : type) (s : substitution) (st : stamp),
  type_of (apply_subst_env env s) e t -> new_tv_env env st -> F st env e t s) ->
 forall (env : environment) (t : type) (s : substitution) (st : stamp),
 type_of (apply_subst_env env s) (Rec i i0 e) t ->
 new_tv_env env st -> F st env (Rec i i0 e) t s.
Proof.
do 8 intro; elim st; intro n; intros.
inversion_clear H0.
(* *)cut
      (F (Stamp (S (S n)))
         (add_environment
            (add_environment env i0 (type_to_type_scheme (Var (Stamp n)))) i
            (type_to_type_scheme (Arrow (Var (Stamp n)) (Var (Stamp (S n))))))
         e t' (add_subst (add_subst s (Stamp n) t0) (Stamp (S n)) t')).
intro Hyp_cut; inversion_clear Hyp_cut.
elim H0; clear H0.
intro Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut.
intro n_uplet; elim n_uplet; clear n_uplet.
intros S' T' st0; simpl in |- *.
intros Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros.
inversion_clear H3.
elim H4; clear H4; intros sigma Hyp; elim Hyp; clear Hyp; intros.
(* *)cut (has_mgu T' (apply_substitution S' (Stamp (S n))) sigma).
intro mgu_exists; inversion_clear mgu_exists.
elim H5; clear H5; intro n_uplet; elim n_uplet; clear n_uplet; intros mu psi;
 simpl in |- *.
intros Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros.
apply intro_F.
(* *)exists
      (compose_subst S' mu,
      extend_subst_type (compose_subst S' mu)
        (Arrow (Var (Stamp n)) (Var (Stamp (S n)))), st0).
simpl in |- *; rewrite H0; rewrite H5.
split; auto.
apply intro_princ_type.
exists psi; simpl in |- *.
do 2 rewrite composition_of_substitutions_stamp.
rewrite <- (mgu_is_correct T' (apply_substitution S' (Stamp (S n))) mu H5).
do 2 rewrite <- composition_of_substitutions_type.
rewrite <- H6; rewrite <- H3.
rewrite <- H4; auto.
rewrite add_subst_rewrite_for_unmodified_stamp; auto.
rewrite add_subst_rewrite_for_modified_stamp; auto.
split; auto.

intros; rewrite composition_of_substitutions_stamp.
rewrite <- composition_of_substitutions_type.
rewrite <- H6; rewrite <- H4; auto.
rewrite add_subst_rewrite_for_unmodified_stamp; auto.
rewrite add_subst_rewrite_for_unmodified_stamp; auto.
apply lt_stamp_n_m_diff; auto.

(*  (has_mgu T' (S' (Stamp (S n))) sigma) *)
apply mgu_is_complete.
(* sigma unifies T'  and  (S' (Stamp (S n))) *)
apply unifier_intro.
rewrite <- H3; rewrite <- H4; auto.
rewrite add_subst_rewrite_for_modified_stamp; auto.

(*Induction hypothesis*)
apply H.
rewrite subst_add_type.
rewrite subst_add_type.
rewrite apply_add_subst_env.
rewrite apply_add_subst_env; auto.
simpl in |- *.
rewrite add_subst_rewrite_for_unmodified_stamp; auto.
rewrite add_subst_rewrite_for_modified_stamp.
rewrite add_subst_rewrite_for_modified_stamp; auto.

apply new_tv_env_trans_le with (st1 := Stamp n); auto.

simpl in |- *; auto.
apply new_tv_add_env; auto.
apply new_tv_add_env; auto.
apply new_tv_env_trans_le with (st1 := Stamp n); auto.

Qed.

(************************************)

Lemma completeness_apply :
 forall e : expr,
 (forall (env : environment) (t : type) (s : substitution) (st : stamp),
  type_of (apply_subst_env env s) e t -> new_tv_env env st -> F st env e t s) ->
 forall e0 : expr,
 (forall (env : environment) (t : type) (s : substitution) (st : stamp),
  type_of (apply_subst_env env s) e0 t ->
  new_tv_env env st -> F st env e0 t s) ->
 forall (env : environment) (t : type) (s : substitution) (st : stamp),
 type_of (apply_subst_env env s) (Apply e e0) t ->
 new_tv_env env st -> F st env (Apply e e0) t s.
Proof.
do 9 intro; elim st; intro n; intros.
inversion_clear H1.
(*induction hypothesis on e *)
generalize (H env (Arrow t0 t) s (Stamp n) H3 H2).
intro F_e; inversion_clear F_e.
elim H1; clear H1.
do 2 (intros n_uplet; elim n_uplet; clear n_uplet).
intros S1 T1 st1; simpl in |- *.
intro Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros W_e T1_princ_type.
inversion_clear T1_princ_type.
elim H1; clear H1; intros psi1 Hyp; elim Hyp; clear Hyp;
 intros T1_psi1 s_psi1_S1.
(*introduction of the properties of st1*)
generalize (stamp_increases_in_W e (Stamp n) st1 env T1 S1 W_e).
intro st_le_st1.
elim (new_tv_W e (Stamp n) st1 env T1 S1 H2 W_e).
intros st1_new_for_T1 st1_new_for_S1.
generalize
 (new_tv_s_env st1 S1 env
    (new_tv_env_trans_le env (Stamp n) st1 H2 st_le_st1) st1_new_for_S1).
intro st1_new_for_S1_env.
(*induction hypothesis on e0 *)
cut (F st1 (apply_subst_env env S1) e0 t0 psi1).
intro Hyp_cut; inversion_clear Hyp_cut.
elim H1; clear H1.
do 2 (intro n_uplet; elim n_uplet; clear n_uplet).
intros S2 T2 st2; elim st2; clear st2; intro n2; simpl in |- *.
intros Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros W_e0 T2_princ_type.
inversion_clear T2_princ_type.
elim H1; clear H1; intros psi2 Hyp; elim Hyp; clear Hyp;
 intros T2_psi2 psi1_psi2_S2.
(*introduction of the properties of st2*)
generalize
 (stamp_increases_in_W e0 st1 (Stamp n2) (apply_subst_env env S1) T2 S2 W_e0).
intro st1_le_st2.
elim
 (new_tv_W e0 st1 (Stamp n2) (apply_subst_env env S1) T2 S2
    st1_new_for_S1_env W_e0).
intros st2_new_for_T2 st2_new_for_S2.
(* *)cut
      (has_mgu (extend_subst_type S2 T1) (Arrow T2 (Var (Stamp n2)))
         (add_subst psi2 (Stamp n2) t)).
intro mgu_cut; inversion_clear mgu_cut.
elim H1; clear H1; intro n_uplet; elim n_uplet; clear n_uplet; intros mu psi;
 simpl in |- *.
intros Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros mgu_exists a_unifier.
apply intro_F.
(* *)
exists
 (compose_subst (compose_subst S1 S2) mu,
 extend_subst_type mu (Var (Stamp n2)), Stamp (S n2)); 
 simpl in |- *.
rewrite W_e; rewrite W_e0; rewrite mgu_exists.
split; auto.
apply intro_princ_type.
(*psi convienient for principal_type*)
exists psi; simpl in |- *; split.
change (t = extend_subst_type psi (extend_subst_type mu (Var (Stamp n2))))
 in |- *.
rewrite <- composition_of_substitutions_type; rewrite <- a_unifier.
simpl in |- *; rewrite add_subst_rewrite_for_modified_stamp; auto.
(*snd property of psi*)
intros; do 2 rewrite composition_of_substitutions_stamp.
generalize
 (new_tv_s_type st1 S1 (Var x)
    (new_tv_Var_stamp x st1 (lt_le_stamp_trans x (Stamp n) st1 H1 st_le_st1))
    st1_new_for_S1).
intro st1_new_for_s1_x.
rewrite <- composition_of_substitutions_type; rewrite <- a_unifier.
rewrite add_subst_new_tv_type.
rewrite <-
 (new_tv_compose_subst_type psi1 S2 psi2 st1 (apply_substitution S1 x)
    psi1_psi2_S2); auto.
(* (new_tv_type (extend_subst_type S2 (S1 x)) (Stamp n2)) *)
apply new_tv_s_type; auto.
apply new_tv_type_trans_le with (x1 := st1); auto.
(*(has_mgu (extend_subst_type S2 T1) (Arrow T2 (Var (Stamp n2)))
     (add_subst psi2 (Stamp n2) t))
*)
apply mgu_is_complete.
(*  (add_subst psi2 (Stamp n2) t) unifies (extend_subst_type S2 T1)  and  
 (Arrow T2 (Var (Stamp n2)) *)
apply unifier_intro; simpl in |- *.
rewrite add_subst_rewrite_for_modified_stamp.
rewrite (add_subst_new_tv_type psi2 (Stamp n2) T2 t st2_new_for_T2).
rewrite <- T2_psi2.
rewrite <-
 (new_tv_compose_subst_type psi1 S2 (add_subst psi2 (Stamp n2) t) st1 T1)
 ; auto.
intros; rewrite add_subst_new_tv_type; auto.
change (new_tv_type (extend_subst_type S2 (Var x)) (Stamp n2)) in |- *.
apply new_tv_s_type; auto.
apply new_tv_Var_stamp; apply lt_le_stamp_trans with (st2 := st1); auto.
(*  (F st1 (apply_subst_env env S1) e0 t0 psi1) *)
apply H0; auto.
rewrite <- (new_tv_compose_subst_env s S1 psi1 (Stamp n) env s_psi1_S1); auto.
Qed.

(**************************************************************************)
Lemma assoc_subst_exists :
 forall (env : environment) (i : identifier) (s : substitution)
   (ts : type_scheme),
 assoc_ident_in_env i (apply_subst_env env s) = Ident_in_env ts ->
 {TS : type_scheme |
 assoc_ident_in_env i env = Ident_in_env TS /\
 ts = extend_subst_type_scheme s TS}.
Proof.
simple induction env.

simpl in |- *; intros; discriminate H.

do 6 intro; elim a; intros y y0; simpl in |- *.
elim (identifier_dec i y); intro eq_i_y.
rewrite eq_i_y; rewrite eq_identifier_reflexivity; simpl in |- *.
intro; exists y0.
split; auto.
injection H0; auto.

rewrite eq_identifier_diff; auto.
simpl in |- *; intro.
elim (H i s ts H0).
intros x Hyp; elim Hyp; clear Hyp; intros.
exists x; auto.
Qed.
(**************************************************************************)


(*******************************************************************)
Lemma apply_compute_generic_subst :
 forall (st : stamp) (TS : type_scheme) (p : nat),
 max_gen_vars TS <= p ->
 {T : type |
 apply_subst_gen (fst (compute_generic_subst st p)) TS = Some_subst_gen T}.

simple induction TS.
(*Nat_ts*)
simpl in |- *; exists Nat; auto.

(*Var_ts*)
simpl in |- *; intros; exists (Var s); auto.

(*Gen_var*)
elim st; intros n s p; elim s; intro m.
rewrite max_gen_vars_Gen_var; intro hyp.
unfold apply_subst_gen in |- *; rewrite (nth_compute p m n); auto.
exists (Var (Stamp (n + m))); auto.

(*Arrow_ts*)
elim st; intros n ts1 ind_ts1 ts2 ind_ts2 p; simpl in |- *; intro le_hyp.
elim (ind_ts1 p).
intros t1 def_t1; rewrite def_t1.
elim (ind_ts2 p).
intros t2 def_t2; rewrite def_t2.
exists (Arrow t1 t2); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.

apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.

(*******************************************************************)
Lemma completeness_var :
 forall (i : identifier) (env : environment) (t : type) 
   (s : substitution) (st : stamp),
 type_of (apply_subst_env env s) (Variabl i) t ->
 new_tv_env env st -> F st env (Variabl i) t s.
Proof.
intros; inversion_clear H; apply intro_F.
elim (assoc_subst_exists env i s ts H1).
intros TS Hyp; elim Hyp; clear Hyp; intros TS_is_assoc_env ts_is_s_TS.
simpl in |- *; rewrite TS_is_assoc_env.
elim (list_type_and_stamp_inv (compute_generic_subst st (max_gen_vars TS))).
intro x; elim x; clear x; intros a b y1; rewrite <- y1.
elim (apply_compute_generic_subst st TS (max_gen_vars TS)); auto.
rewrite <- y1; simpl in |- *; intros T T_def.
rewrite T_def.
exists (empty_subst, T, b).
simpl in |- *.
split; auto.

(*   (principal_type T empty_subst t s st)  *)
inversion_clear H2.
elim H; clear H; intros sg H.
apply intro_princ_type; simpl in |- *.
exists (compute_subst st sg ++ s).
split.
apply (t_is_app_T_aux TS T t s (max_gen_vars TS) st sg); auto.
apply (new_tv_env_implies_new_tv_ts env TS st i TS_is_assoc_env H0).

rewrite <- y1; auto.

rewrite <- ts_is_s_TS; auto.
       
(*   (x:stamp)
    (lt_stamp x st)
     ->(apply_substitution s x)
        =(apply_substitution (app stamp*type (compute_subst st sg) s) x)*)
intros; rewrite apply_app_compute_subst; auto.

Qed.

(*******************************************************************)
Lemma completeness_let :
 forall (i : identifier) (e : expr),
 (forall (env : environment) (t : type) (s : substitution) (st : stamp),
  type_of (apply_subst_env env s) e t -> new_tv_env env st -> F st env e t s) ->
 forall e0 : expr,
 (forall (env : environment) (t : type) (s : substitution) (st : stamp),
  type_of (apply_subst_env env s) e0 t ->
  new_tv_env env st -> F st env e0 t s) ->
 forall (env : environment) (t : type) (s : substitution) (st : stamp),
 type_of (apply_subst_env env s) (Let_in i e e0) t ->
 new_tv_env env st -> F st env (Let_in i e e0) t s.

intros; inversion_clear H1.
(*induction hypothesis on e *)
generalize (H env t0 s st H3 H2). 
intro F_e; inversion_clear F_e; elim H1; clear H1.
do 2 (intro n_uplet; elim n_uplet; clear n_uplet).
intros S1 T1 st1; simpl in |- *.
intros Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros W_e T1_princ_type.
inversion_clear T1_princ_type.
elim H1; clear H1; intros psi1 Hyp; elim Hyp; clear Hyp;
 intros T1_psi1 s_psi1_S1.
(*introduction of the properties of st1*)
generalize (stamp_increases_in_W e st st1 env T1 S1 W_e).
intro st_le_st1.
elim (new_tv_W e st st1 env T1 S1 H2 W_e).
intros st1_new_for_T1 st1_new_for_S1.
generalize
 (new_tv_s_env st1 S1 env (new_tv_env_trans_le env st st1 H2 st_le_st1)
    st1_new_for_S1).
intro st1_new_for_S1_env.
(*induction hypothesis on e0 *)
cut
 (F st1
    (add_environment (apply_subst_env env S1) i
       (gen_type T1 (apply_subst_env env S1))) e0 t psi1).
intro Hyp_cut; inversion_clear Hyp_cut; elim H1; clear H1.
do 2 (intros n_uplet; elim n_uplet; clear n_uplet).
intros S2 T2 st2; simpl in |- *.
intro Hyp_Cut; elim Hyp_Cut; clear Hyp_Cut; intros W_e0 T2_princ_type.
inversion_clear T2_princ_type.
elim H1; clear H1; intros psi2 Hyp; elim Hyp; clear Hyp;
 intros T2_psi2 psi1_psi2_S2.
(* *)
apply intro_F.
exists (compose_subst S1 S2, T2, st2); simpl in |- *.
rewrite W_e; rewrite W_e0.
split; auto.
apply intro_princ_type.
(*psi2 convienient for principal_type*)
exists psi2; simpl in |- *; split; auto.
(*snd property of psi2*)
intros; rewrite composition_of_substitutions_stamp.
rewrite <-
 (new_tv_compose_subst_type psi1 S2 psi2 st1 (apply_substitution S1 x)
    psi1_psi2_S2); auto.
change (new_tv_type (extend_subst_type S1 (Var x)) st1) in |- *.
apply new_tv_s_type; auto.
apply new_tv_Var_stamp.
apply lt_le_stamp_trans with (st2 := st); auto.
(*   (F st1
     (add_environment (apply_subst_env env S1) i
       (gen_type T1 (apply_subst_env env S1))) e0 t psi1)
*)
apply H0.
rewrite subst_add_type_scheme.
apply
 typing_in_a_more_general_env
  with
    (env2 := add_environment (apply_subst_env (apply_subst_env env S1) psi1)
               i
               (gen_type (extend_subst_type psi1 T1)
                  (apply_subst_env (apply_subst_env env S1) psi1))).
apply more_general_env_add_ts; auto.
apply s_gen_t_more_general_than_gen_s_t.

rewrite <- T1_psi1.
rewrite <- (new_tv_compose_subst_env s S1 psi1 st env s_psi1_S1); auto.
apply new_tv_add_env; auto.
unfold gen_type in |- *; apply new_tv_gen_type_aux; auto.
Qed.
(*******************************************************************)
Lemma completeness :
 forall (e : expr) (env : environment) (t : type) (s : substitution)
   (st : stamp),
 type_of (apply_subst_env env s) e t -> new_tv_env env st -> F st env e t s.
Proof.
simple induction e.
(*Const*)
intros; inversion_clear H; apply intro_F.
exists (empty_subst, Nat, st); simpl in |- *; split; auto.
apply intro_princ_type; exists s; auto.
(*Var*)
intros; apply completeness_var; auto.
(*Lambda*)
intros; apply completeness_lambda; auto.
(*Rec*)
intros; apply completeness_rec; auto.
(*apply*)
intros; apply completeness_apply; auto.
(*Let*)
intros; apply completeness_let; auto.
Qed.