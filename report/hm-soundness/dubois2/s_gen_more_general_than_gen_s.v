(* Author : Catherine Dubois *)

Require Import type_scheme.
Require Import disjoints.
Require Import List.
Require Import tools_bool.
Require Import FV.
Require Import subst.
Require Import langs.
Require Import env_poly.
Require Import more_general.
Require Import subset_FV_env.
Require Import tools_more_general.
Require Import more_general.
Require Import generic_DB.
Require Import DB_stable_gen_instance.
Require Import DB_gen_stable.
Require Import tools_more_general.
Require Import max.



(**********************************************************************)
Lemma s_gen_aux_7 :
 forall (env : environment) (tau t0 : type) (phi s : substitution)
   (l_gv_t l_gv_st L P : list stamp) (sg : list type),
 are_disjoints (FV_env env) l_gv_t ->
 are_disjoints (FV_env (apply_subst_env env s)) l_gv_st ->
 apply_subst_gen sg
   (fst (gen_aux (extend_subst_type s tau) (apply_subst_env env s) l_gv_st)) =
 Some_subst_gen t0 ->
 is_prefixe_free2 (FV_env (apply_subst_env env s))
   (snd (gen_aux (extend_subst_type s tau) (apply_subst_env env s) l_gv_st))
   L ->
 product_list L sg = Some_product phi ->
 is_prefixe_free2 (FV_env env) (snd (gen_aux tau env l_gv_t)) P ->
 apply_subst_gen
   (map_extend_subst_type (type_from_stamp_list P) (compose_subst s phi))
   (extend_subst_type_scheme s (fst (gen_aux tau env l_gv_t))) =
 Some_subst_gen t0.
simple induction tau.
simpl in |- *; intros.
injection H1; intros; rewrite H5; auto.


do 9 intro; simpl in |- *.
intros disjoint1 disjoint2.
elim (bool_dec (in_list_stamp s (FV_env env))); intro y; rewrite y;
 simpl in |- *.
rewrite
 (is_not_generalizable_aux (apply_subst_env env s0) 
    (apply_substitution s0 s) l_gv_st (subset_FV_env env s0 s y))
 .
simpl in |- *.
do 2 rewrite apply_subst_gen_type_to_type_scheme.
intros.
injection H; intros; rewrite <- H3; auto.

do 3 intro.
elim (index_answer_dec (index l_gv_t s)).
intro s_in_l; elim s_in_l; intro n0; clear s_in_l; intros s_in_l;
 rewrite s_in_l; simpl in |- *; intro.
inversion_clear H2.
elim H3; clear H3; intros P2 Hyp.
elim Hyp; clear Hyp; intros Def_P disjoint3; rewrite Def_P.
rewrite (type_from_stamp_list_app l_gv_t P2).
rewrite
 (map_extend_app (compose_subst s0 phi) (type_from_stamp_list l_gv_t)
    (type_from_stamp_list P2)).
rewrite
 (nth_app
    (map_extend_subst_type (type_from_stamp_list l_gv_t)
       (compose_subst s0 phi))
    (map_extend_subst_type (type_from_stamp_list P2) (compose_subst s0 phi))
    n0).
rewrite
 (nth_map (compose_subst s0 phi) (type_from_stamp_list l_gv_t) n0 (Var s))
 .
rewrite composition_of_substitutions_type.
simpl in |- *.
rewrite
 (gen_subst_to_subst_aux_4 (apply_subst_env env s0) 
    (apply_substitution s0 s) t0 l_gv_st L sg phi); 
 auto.

apply index_nth; auto.

rewrite length_map.
rewrite length_type_from_stamp_list.
apply (index_lt l_gv_t s n0 s_in_l).

intros s_in_l; rewrite s_in_l; simpl in |- *; intro.
inversion_clear H2.
elim H3; clear H3.
intros P2 Hyp.
elim Hyp; clear Hyp; intros Def_P disjoint4.
rewrite Def_P.
rewrite (type_from_stamp_list_app (l_gv_t ++ s :: nil) P2).
rewrite
 (map_extend_app (compose_subst s0 phi)
    (type_from_stamp_list (l_gv_t ++ s :: nil)) (type_from_stamp_list P2))
 .
rewrite
 (nth_app
    (map_extend_subst_type (type_from_stamp_list (l_gv_t ++ s :: nil))
       (compose_subst s0 phi))
    (map_extend_subst_type (type_from_stamp_list P2) (compose_subst s0 phi))
    (length l_gv_t)).
rewrite
 (nth_map (compose_subst s0 phi) (type_from_stamp_list (l_gv_t ++ s :: nil))
    (length l_gv_t) (Var s)).
rewrite composition_of_substitutions_type.
simpl in |- *;
 rewrite
  (gen_subst_to_subst_aux_4 (apply_subst_env env s0)
     (apply_substitution s0 s) t0 l_gv_st L sg phi)
  ; auto.

rewrite type_from_stamp_list_app; simpl in |- *.
rewrite <- length_type_from_stamp_list; auto.

rewrite length_map2; rewrite length_app_cons; auto.

do 12 intro; intros disjoint1 disjoint2.
rewrite <- apply_subst_arrow_rewrite; rewrite fst_gen_aux_arrow_rewrite;
 intro.
elim
 (apply_subst_gen_arrow_is_some_inversion3
    (fst (gen_aux (extend_subst_type s t) (apply_subst_env env s) l_gv_st))
    (fst
       (gen_aux (extend_subst_type s t0) (apply_subst_env env s)
          (snd
             (gen_aux (extend_subst_type s t) (apply_subst_env env s) l_gv_st))))
    t1 sg); auto.
intro x; elim x; clear x; do 2 intro; clear H1.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro rwt_t2; rewrite rwt_t2.
rewrite snd_gen_aux_arrow_rewrite; do 2 intro.
rewrite snd_gen_aux_arrow_rewrite.
rewrite fst_gen_aux_arrow_rewrite.
rewrite <- extend_subst_ts_arrow_rewrite; intro.
simpl in |- *.
rewrite (H a phi s l_gv_t l_gv_st L P sg); eauto.
rewrite
 (H0 b phi s (snd (gen_aux t env l_gv_t))
    (snd (gen_aux (extend_subst_type s t) (apply_subst_env env s) l_gv_st)) L
    P sg); auto.
Qed.

(*************************************************************************)

Lemma s_gen_t_more_general_than_gen_s_t :
 forall (s : substitution) (env : environment) (t : type),
 more_general (extend_subst_type_scheme s (gen_type t env))
   (gen_type (extend_subst_type s t) (apply_subst_env env s)).
Proof.
intros; apply more_general_intro; intros.
inversion_clear H; elim H0; clear H0; intro sg.
unfold gen_type in |- *; intros.
elim (product_list_exists (extend_subst_type s t) (apply_subst_env env s) sg);
 eauto.
intros phi def_phi.
apply gen_instance_intro.
exists
 (map_extend_subst_type (type_from_stamp_list (snd (gen_aux t env nil)))
    (compose_subst s phi)).
rewrite
 (s_gen_aux_7 env t t0 phi s nil nil
    (snd (gen_aux (extend_subst_type s t) (apply_subst_env env s) nil))
    (snd (gen_aux t env nil)) sg); auto.
Qed.
