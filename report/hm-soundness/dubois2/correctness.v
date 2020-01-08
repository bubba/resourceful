(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import langs.
Require Import type_system.
Require Import env_poly.
Require Import type_scheme.
Require Import unification.
Require Import DB_gen_stable.
Require Import generic_DB.
Require Import W.
Require Import subst.
Require Import tools_stable.
Require Import stable.
Require Import W_inversion.
Require Import s_env_when_s_disjoint_with_env3.
Require Import tools_correctness.

Lemma correctness_variable :
 forall (st st' : stamp) (env : environment) (i : identifier) 
   (t : type) (s : substitution),
 W st env (Variabl i) = Some_infer t s st' ->
 type_of (apply_subst_env env s) (Variabl i) t.

Proof.
intros.
elim (W_var_inversion st st' env i t s H).
intros ts and1; elim and1; intros H1 and2; elim and2; intros H2 and3;
 elim and3; intros H3 H4; clear H and1 and2 and3 H4.
rewrite H1; rewrite empty_subst_is_identity_on_env.
apply (type_of_var env i t ts H2).
apply (compute_generic_subst_create_generic_instance ts st t H3).
Qed.

Lemma correctness_lambda :
 forall (i : identifier) (e0 : expr),
 (forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
  W st env e0 = Some_infer t s st' -> type_of (apply_subst_env env s) e0 t) ->
 forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
 W st env (Lambda i e0) = Some_infer t s st' ->
 type_of (apply_subst_env env s) (Lambda i e0) t.

Proof.
simple induction st; intros.
elim (W_lambda_inversion n st' env e0 i t s H0).  
intros t' and1; elim and1; intros H1 H2.
rewrite H2.
apply
 (type_of_lambda (apply_subst_env env s) i e0
    (apply_substitution s (Stamp n)) t').
rewrite (apply_subst_stp_rewrite s (Stamp n)).
elim (subst_add_type env i s (Var (Stamp n))).
apply
 (H (Stamp (S n)) st'
    (add_environment env i (type_to_type_scheme (Var (Stamp n)))) t' s);
 simpl in |- *; assumption.
Qed.

Lemma correctness_rec :
 forall (e : expr) (f x : identifier),
 (forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
  W st env e = Some_infer t s st' -> type_of (apply_subst_env env s) e t) ->
 forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
 W st env (Rec f x e) = Some_infer t s st' ->
 type_of (apply_subst_env env s) (Rec f x e) t.

Proof.
simple induction st; intros.
elim (W_rec_inversion n st' env e f x t s H0).
intros tau_subst_U; elim tau_subst_U; intros tau subst_U; elim subst_U;
 intros subst U. 
intros and1; elim and1; intros H1 and2; elim and2; intros H2 and3; elim and3;
 intros H3 H4; clear and1 and2 and3.
elim H4; simpl in |- *; apply type_of_rec_fun.
elim (subst_add_type_var env x s (Stamp n)).
rewrite apply_subst_arrow_rewrite2.
rewrite type_to_type_scheme_commutes_with_subst.
elim
 (subst_add_type_scheme
    (add_environment env x (type_to_type_scheme (Var (Stamp n)))) f s
    (type_to_type_scheme (Arrow (Var (Stamp n)) (Var (Stamp (S n)))))).
rewrite H3.
rewrite composition_of_substitutions_env. 
rewrite composition_of_substitutions_stamp.
elim (mgu_is_correct tau (apply_substitution subst (Stamp (S n))) U H2).
apply typage_is_stable_by_substitution.
apply (H (Stamp (S (S n))) st'); assumption.
Qed.

Lemma correctness_apply :
 forall e0 : expr,
 (forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
  W st env e0 = Some_infer t s st' -> type_of (apply_subst_env env s) e0 t) ->
 forall e1 : expr,
 (forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
  W st env e1 = Some_infer t s st' -> type_of (apply_subst_env env s) e1 t) ->
 forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
 W st env (Apply e0 e1) = Some_infer t s st' ->
 type_of (apply_subst_env env s) (Apply e0 e1) t.

Proof.
intros.
elim (W_apply_inversion st st' env e0 e1 t s H1).
intros t1_S1_st1_t2_S2_n2_U; elim t1_S1_st1_t2_S2_n2_U;
 intros t1_S1_st1_t2_S2_n2 U; elim t1_S1_st1_t2_S2_n2;
 intros t1_S1_st1 t2_S2_n2; elim t1_S1_st1; intros t1_S1 st1; 
 elim t2_S2_n2; intros t2_S2 n2; elim t1_S1; intros t1 s1; 
 elim t2_S2; intros t2 s2.
intros and1; elim and1; intros H2 and2; elim and2; intros H3 and3; elim and3;
 intros H4 and4; elim and4; intros H5 and5; elim and5; 
 intros H6 H7; clear and1 and2 and3 and4 and5.
rewrite H5; rewrite H6.
do 2 rewrite composition_of_substitutions_env.
apply type_of_app with (t := extend_subst_type U t2).
rewrite (apply_subst_arrow_rewrite U t2 (Var (Stamp n2))).
elim (mgu_is_correct (extend_subst_type s2 t1) (Arrow t2 (Var (Stamp n2))) U);
 auto.
do 2 apply typage_is_stable_by_substitution.
apply H with (st := st) (st' := st1); auto.
apply typage_is_stable_by_substitution.
apply H0 with (st := st1) (st' := Stamp n2); auto.
Qed.

Lemma correctness_let :
 forall (i : identifier) (e : expr),
 (forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
  W st env e = Some_infer t s st' -> type_of (apply_subst_env env s) e t) ->
 forall e0 : expr,
 (forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
  W st env e0 = Some_infer t s st' -> type_of (apply_subst_env env s) e0 t) ->
 forall (st st' : stamp) (env : environment) (t : type) (s : substitution),
 W st env (Let_in i e e0) = Some_infer t s st' ->
 type_of (apply_subst_env env s) (Let_in i e e0) t.

Proof.
intros.
elim (W_let_inversion st st' env e e0 i t s H1).
intros t1_s1_st1_s2; elim t1_s1_st1_s2; intros t1_s1_st1 s2; elim t1_s1_st1;
 intros t1_s1 st1; elim t1_s1; intros t1 s1.
intros and1; elim and1; intros H2 and2; elim and2; intros H3 H4;
 clear and1 and2.
rewrite H4.
rewrite composition_of_substitutions_env.
elim
 (exists_renaming_not_concerned_with2 (gen_vars t1 (apply_subst_env env s1))
    (FV_env (apply_subst_env env s1)) (FV_subst s2)).
intros r ren.
apply
 type_of_let_in
  with (t := extend_subst_type s2 (extend_subst_type (rename_to_subst r) t1)).
apply typage_is_stable_by_substitution.
elim
 (s_env_when_s_disjoint_with_env3 (rename_to_subst r)
    (apply_subst_env env s1)).
apply typage_is_stable_by_substitution.
apply H with (st := st) (st' := st1); auto.
inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H6; apply free_and_bound_are_disjoints.
elim gen_in_subst_env2.
elim subst_add_type_scheme.
apply H0 with (st := st1) (st' := st').
inversion ren.
rewrite <- gen_alpha4_bis; try rewrite H6; auto.
apply renaming_not_concerned_with_gen_vars; auto.
apply gen_vars_is_a_set.
Qed.

Lemma correctness :
 forall (e : expr) (st st' : stamp) (env : environment) 
   (t : type) (s : substitution),
 W st env e = Some_infer t s st' -> type_of (apply_subst_env env s) e t.

Proof.
simple induction e.
(* Const_nat *)
simpl in |- *; intros.
inversion H.
apply type_of_int_const.
(* Variable *)
intros.
apply (correctness_variable st st' env i t s H).
(* Lambda *)
intros.
apply (correctness_lambda i e0 H st st' env t s H0).
(* Rec *)
intros.
apply (correctness_rec e0 i i0 H st st' env t s H0).
(* Apply *)
intros.
apply (correctness_apply e0 H e1 H0 st st' env t s H1).
(* Let *)
intros.
apply (correctness_let i e0 H e1 H0 st st' env t s H1).
Qed.