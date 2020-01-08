(* Author : Catherine Dubois *)

Require Import List.
Require Import langs.
Require Import tools.
Require Import env_poly.
Require Import type_scheme.
Require Import subst.
Require Import type_system.
Require Import stable.
Require Import new_tv.
Require Import completeness.
Require Import ds.
Require Import completeness_var_tools.
Require Import tools_correctness.
Require Import generic_DB.
Require Import tools_more_general.
(*Require  max_list.*)

Inductive type_of_val : val -> type -> Prop :=
  | type_num : forall n : nat, type_of_val (Num n) Nat
  | type_closure :
      forall (i : identifier) (e : expr) (c : ctx) 
        (env : environment) (t1 t2 : type),
      ctx_env_match c env ->
      type_of env (Lambda i e) (Arrow t1 t2) ->
      type_of_val (Closure i e c) (Arrow t1 t2)
  | type_rec_closure :
      forall (f i : identifier) (e : expr) (c : ctx) 
        (env : environment) (t1 t2 : type),
      ctx_env_match c env ->
      type_of env (Rec f i e) (Arrow t1 t2) ->
      type_of_val (Rec_closure f i e c) (Arrow t1 t2)
with ctx_env_match : ctx -> environment -> Prop :=
  | match_nil : ctx_env_match Cnil nil
  | match_cons :
      forall (c : ctx) (env : environment) (i : identifier)
        (ts : type_scheme) (v : val),
      sem_gen v ts ->
      ctx_env_match c env -> ctx_env_match (Ccons i v c) ((i, ts) :: env)
with sem_gen : val -> type_scheme -> Prop :=
    sem_gen_def :
      forall (v : val) (ts : type_scheme),
      (forall t : type, is_gen_instance t ts -> type_of_val v t) ->
      sem_gen v ts.

Hint Resolve type_num.
Hint Resolve type_closure.
Hint Resolve type_rec_closure.
Hint Resolve sem_gen_def.
Hint Resolve match_nil.

(********************************************************************)
Lemma type_val_gen_instance :
 forall (c : ctx) (env : environment) (i : identifier) 
   (v : val) (t : type) (ts : type_scheme),
 ctx_env_match c env ->
 assoc_ident_in_ctx i c = Ident_in_ctx v ->
 assoc_ident_in_env i env = Ident_in_env ts ->
 is_gen_instance t ts -> type_of_val v t.
simple induction c.
simpl in |- *; do 6 intro; intro pb; discriminate pb.

intros j u c0 Hyp_ind env i v t ts hyp_match.
inversion_clear hyp_match.
elim (identifier_dec i j); intro eq_i_j.
(* i = j*)
rewrite eq_i_j; simpl in |- *; rewrite eq_identifier_reflexivity;
 simpl in |- *.
intro Ident_in_ctx_v_u; injection Ident_in_ctx_v_u; intro u_eq_v;
 rewrite <- u_eq_v.
intro Ident_in_env_ts0_ts; injection Ident_in_env_ts0_ts; intro ts0_eq_ts;
 rewrite <- ts0_eq_ts.
inversion_clear H. (* H : (sem_gen u ts0) *)
auto.
(*  ~i=j *)
simpl in |- *; rewrite eq_identifier_diff; auto.
simpl in |- *; intros.
apply (Hyp_ind env0 i v t ts); auto.
Qed.

(*********************************************************************)
(* a verifier duplication et replacer dans fichier qui convient*)
Lemma gen_instance_type_to_type_scheme_inv :
 forall t t0 : type, is_gen_instance t0 (type_to_type_scheme t) -> t0 = t.
intros; inversion_clear H.
elim H0.
intro sg; rewrite apply_subst_gen_type_to_type_scheme.
intro y; inversion_clear y; auto.
Qed.

(*********************************************************************)
Lemma sem_gen_type_to_type_scheme :
 forall (u : val) (t : type),
 type_of_val u t -> sem_gen u (type_to_type_scheme t).
Proof.
intros.
apply sem_gen_def.
intros.
rewrite (gen_instance_type_to_type_scheme_inv t t0 H0); auto.
Qed.

(*********************************************************************)

Scheme val_ctx_rec := Induction for val Sort Prop
  with ctx_val_rec := Induction for ctx Sort Prop.

Lemma type_of_val_stable_subst :
 forall (v : val) (t : type) (s : substitution),
 type_of_val v t -> type_of_val v (extend_subst_type s t).
Proof.
intro v; pattern v in |- *.
apply
 val_ctx_rec
  with
    (P0 := fun c : ctx =>
           forall (env : environment) (s : substitution),
           ctx_env_match c env -> ctx_env_match c (apply_subst_env env s)).

(*  (Num n) *)
intros; inversion_clear H; auto.

(* (Closure i e c) *)
intros; inversion_clear H0; simpl in |- *.
apply type_closure with (env := apply_subst_env env s); auto.

rewrite apply_subst_arrow_rewrite.
apply typage_is_stable_by_substitution; auto.

(* (Rec_closure i i0 e c) *)
intros; inversion_clear H0; simpl in |- *.
apply type_rec_closure with (env := apply_subst_env env s); auto.

rewrite apply_subst_arrow_rewrite.
apply typage_is_stable_by_substitution; auto.

(*Cnil*)
intros; inversion_clear H; auto.

(*Ccons*)
intros; inversion_clear H1.
simpl in |- *; apply match_cons; auto.
(*(sem_gen v0 (extend_subst_type_scheme s ts))*)
apply sem_gen_def; intros.
inversion_clear H1.
elim H4; clear H4; intros sg def_t.
generalize (find_new_tv_type_scheme2 ts).
intro Hyp_cut; elim Hyp_cut; clear Hyp_cut; intros st st_new_ts.
elim (apply_compute_generic_subst st ts (max_gen_vars ts)); auto.
intros T T_def.
rewrite (t_is_app_T_aux ts T t s (max_gen_vars ts) st sg); auto.
apply H.
inversion_clear H2.
apply H1.
apply compute_generic_subst_create_generic_instance with (st := st); auto.
Qed.

(*********************************************************************)

Lemma sem_gen_gen_type :
 forall (u : val) (t : type) (env : environment),
 type_of_val u t -> sem_gen u (gen_type t env).
Proof.
intros; apply sem_gen_def.
intros.
inversion_clear H0.
elim H1; clear H1; intro sg; unfold gen_type in |- *; intro def_t0.
elim (product_list_exists t env sg); eauto.
intros phi def_phi.
rewrite <-
 (gen_subst_to_subst_aux_4 env t t0 nil (snd (gen_aux t env nil)) sg phi)
 ; auto.
apply type_of_val_stable_subst; auto.
Qed.


(*************************************************************************
                          SUBJECT REDUCTION THEOREM 
***************************************************************************)

Lemma subject_reduction_theorem :
 forall (e : expr) (v : val) (c : ctx),
 val_of c e v ->
 forall (env : environment) (t : type),
 type_of env e t -> ctx_env_match c env -> type_of_val v t.
simple induction 1; intros.

inversion_clear H0; auto.

inversion_clear H1.
apply (type_val_gen_instance c0 env i v0 t ts); auto.

inversion_clear H0.
apply type_closure with (env := env); auto.
apply type_of_lambda; auto.

inversion_clear H0.
apply type_rec_closure with (env := env); auto.
apply type_of_rec_fun; auto.

inversion_clear H6.
generalize (H1 env (Arrow t0 t) H8 H7).
intro type_clos.
inversion_clear type_clos. (*H6 and H10*)
inversion_clear H10. (*H11*)
apply (H5 (add_environment env0 i (type_to_type_scheme t0)) t H11).
unfold add_environment in |- *.
apply match_cons; auto.
apply sem_gen_type_to_type_scheme.
apply H3 with (env := env); auto.

inversion_clear H6.
generalize (H1 env (Arrow t0 t) H8 H7).
intro type_clos.
inversion type_clos. (*H11 and H16*)
inversion_clear H16. (*H17*)
apply
 (H5
    (add_environment (add_environment env0 i (type_to_type_scheme t0)) f
       (type_to_type_scheme (Arrow t0 t))) t H17).
unfold add_environment in |- *.
apply match_cons; auto.
apply sem_gen_type_to_type_scheme.
assumption.
apply match_cons; auto.
apply sem_gen_type_to_type_scheme.
apply H3 with (env := env); auto.

inversion_clear H4.
apply H3 with (env := add_environment env i (gen_type t0 env)); auto.
unfold add_environment in |- *.
apply match_cons; auto.
apply sem_gen_gen_type.
apply H1 with (env := env); auto.
Qed.