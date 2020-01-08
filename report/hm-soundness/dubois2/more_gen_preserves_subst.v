(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import langs.
Require Import type_scheme.
Require Import order_stamp.
Require Import max.
Require Import FV.
Require Import more_general.
Require Import tools_correctness.
Require Import completeness.
Require Import subst.
Require Import completeness_var_tools.
Require Import not_in_FV_env.
Require Import new_tv.
Require Import generic_DB.
Require Import DB_stable_gen_instance.


Lemma apply_substitution_app :
 forall (s : substitution) (sg : list type) (s0 st : stamp),
 lt_stamp s0 st ->
 apply_substitution s s0 = apply_substitution (compute_subst st sg ++ s) s0.
simple induction sg; auto.
intros a l Hyp s0 st; elim st; intros n lt_hyp; simpl in |- *.
rewrite apply_subst_cons2; auto.
Qed.

Lemma extend_subst_type_scheme_app :
 forall (ts : type_scheme) (st : stamp) (sg : list type) (s : substitution),
 new_tv_type_scheme ts st ->
 extend_subst_type_scheme s ts =
 extend_subst_type_scheme (compute_subst st sg ++ s) ts.
simple induction ts; auto.

(*var*)
simpl in |- *; intros; inversion_clear H.
rewrite <- apply_substitution_app; auto.

(*arrow*)
intros; simpl in |- *.
inversion_clear H1.
rewrite <- H; auto.
rewrite <- H0; auto.
Qed.

Lemma max_list_stamp_nil : max_list_stamp nil = Stamp 0.
auto.
Qed.

Lemma max_stamp_O : forall st : stamp, max_stamp (Stamp 0) st = st.
intro st; elim st; intro.
unfold max_stamp in |- *; rewrite max_O_m; auto.
Qed.


Lemma le_stamp_succ_succ :
 forall st st' : stamp,
 le_stamp st st' -> le_stamp (succ_stamp st) (succ_stamp st').
intros st st'; elim st; intro n; elim st'; intro m.
simpl in |- *; auto with *.
Qed.

Lemma find_new_tv_type_scheme :
 forall ts1 ts2 : type_scheme,
 {st : stamp | new_tv_type_scheme ts1 st /\ new_tv_type_scheme ts2 st}.
intros ts1 ts2.
exists
 (succ_stamp
    (max_stamp (max_list_stamp (FV_type_scheme ts1))
       (max_list_stamp (FV_type_scheme ts2)))).
split.
apply
 new_tv_ts_trans_le
  with (st1 := succ_stamp (max_list_stamp (FV_type_scheme ts1))); 
 auto.
apply le_stamp_succ_succ; auto.

apply
 new_tv_ts_trans_le
  with (st1 := succ_stamp (max_list_stamp (FV_type_scheme ts2))); 
 auto.
apply le_stamp_succ_succ; auto.
Qed.

Lemma more_general_preserves_subst :
 forall (ts1 ts2 : type_scheme) (s : substitution),
 more_general ts1 ts2 ->
 more_general (extend_subst_type_scheme s ts1)
   (extend_subst_type_scheme s ts2).
intros ts1 ts2 s more_gen_hyp.
apply more_general_intro.
intros t t_gen_inst_s_ts2.
inversion_clear t_gen_inst_s_ts2.
elim H; intros sg t_def.
generalize (find_new_tv_type_scheme ts1 ts2).
intro Hyp_cut; elim Hyp_cut; clear Hyp_cut; intros st Hyp_cut; elim Hyp_cut;
 clear Hyp_cut; intros st_new_st1 st_new_st2.
generalize (apply_compute_generic_subst st ts2 (max_gen_vars ts2)).
intro H1; elim H1; auto.
clear H1; intros T T_def.
generalize
 (t_is_app_T_aux ts2 T t s (max_gen_vars ts2) st sg st_new_st2
    (le_n (max_gen_vars ts2)) T_def t_def).
intro new_t_def.
generalize (compute_generic_subst_create_generic_instance ts2 st T T_def).
intro T_gen_inst_ts2.
inversion_clear more_gen_hyp. (*H0*)
generalize (H0 T T_gen_inst_ts2).
intro T_gen_inst_ts1.
inversion_clear T_gen_inst_ts1; elim H1; intros phi T_def_phi.

apply gen_instance_intro.
exists (map_extend_subst_type phi (compute_subst st sg ++ s)).
rewrite (extend_subst_type_scheme_app ts1 st sg s st_new_st1).
rewrite new_t_def.
apply generic_compose; auto.
Qed.
