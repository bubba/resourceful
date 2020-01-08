(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import tools_bool.
Require Import tools.
Require Import langs.
Require Import type_scheme.
Require Import order_stamp.
Require Import env_poly.
Require Import type_system.
Require Import subset.
Require Import FV.
Require Import generic_DB.
Require Import subst.
Require Import disjoints.
Require Import DB_gen_stable.
Require Import DB_stable_gen_instance.
Require Import tools_stable.
Require Import s_env_when_s_disjoint_with_env3.
Require Import max.


Lemma domain_of_substitution_rename_to_subst :
 forall r : list (stamp * stamp),
 domain_of_substitution (rename_to_subst r) = domain_of_rename_subst r.

Proof.
simple induction r.
(* r=[] *)
auto.
(* r=a::l *)
simple induction a; intros; simpl in |- *; rewrite H; auto.
Qed.

Fixpoint compute_renaming2 (N : stamp) (l : list stamp) {struct l} :
 list (stamp * stamp) :=
  match l with
  | nil => nil (A:=stamp * stamp)
  | p :: l' => (p, N) :: compute_renaming2 (succ_stamp N) l'
  end.

Lemma domain_of_compute_renaming :
 forall (l : list stamp) (N : stamp),
 domain_of_rename_subst (compute_renaming2 N l) = l.

Proof.
simple induction l.
(* l=[] *)
auto.
(* l=a::l0 *)
intros; simpl in |- *; rewrite (H (succ_stamp N)); auto.
Qed.

Lemma range_compute_renaming :
 forall (x : stamp) (l : list stamp) (N : stamp),
 lt_stamp x N ->
 in_list_stamp x (range_of_rename_subst (compute_renaming2 N l)) = false.

Proof.
simple induction l.
(* l=[] *)
auto.
(* l=a::l0 *)
intros; simpl in |- *.
apply if_true_false_inversion.
apply (eq_stamp_diff x N (lt_stamp_n_m_diff x N H0)).
apply
 (H (succ_stamp N) (lt_stamp_trans x N (succ_stamp N) H0 (lt_succ_stamp N))).
Qed.

Lemma is_subset_gen_vars2 :
 forall (r : list (stamp * stamp)) (env : environment) (t : type),
 is_rename_subst r ->
 are_disjoints (domain_of_rename_subst r) (FV_env env) ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 is_subset_list_stamp (gen_vars t env) (domain_of_rename_subst r) ->
 is_subset_list_stamp
   (gen_vars (extend_subst_type (rename_to_subst r) t) env)
   (range_of_rename_subst r).

Proof.
simple induction t.
(* Nat *)
auto.
(* Var s *)
intros s; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))).
(* (in_list_stamp s (FV_env env))=true *)
intros s_free_in_env; rewrite s_free_in_env; simpl in |- *.
elim (domain_of_substitution_rename_to_subst r); intros.
rewrite
 (is_not_in_domain_subst s (rename_to_subst r)
    (disjoint_inversion2 (domain_of_substitution (rename_to_subst r))
       (FV_env env) s H0 s_free_in_env)); simpl in |- *.
rewrite s_free_in_env; simpl in |- *; auto.
(* (in_list_stamp s (FV_env env))=false *)
intros s_not_free_in_env; rewrite s_not_free_in_env; simpl in |- *.
intros.
rewrite (apply_substitution_rename_to_subst_rewrite s r); simpl in |- *.
elim
 (domain_range_rename_subst r s
    (subset_cons_subset s (domain_of_rename_subst r) nil H2)); 
 intros x y. 
elim y; intros; rewrite H4.
elim (bool_dec (in_list_stamp x (FV_env env))).
(* (in_list_stamp x (FV_env env)))=true *)
intros x_free_in_env; rewrite x_free_in_env; simpl in |- *; auto.
(* (in_list_stamp x (FV_env env)))=false *)
intros x_not_free_in_env; rewrite x_not_free_in_env; simpl in |- *.
apply
 (subset_cons_inv nil (range_of_rename_subst r) x
    (nil_is_subset (range_of_rename_subst r)) H3).
(* Arrow t t0 *)
intros t0 H0 t1 H1 H2 H3 H4; simpl in |- *; intros.
apply union_subset.
apply
 (H0 H2 H3 H4
    (subset_of_union_inversion1 (domain_of_rename_subst r) 
       (gen_vars t0 env) (gen_vars t1 env) H)).
apply
 (H1 H2 H3 H4
    (subset_of_union_inversion2 (domain_of_rename_subst r) 
       (gen_vars t0 env) (gen_vars t1 env) H)).
Qed.

Lemma is_subset_gen_vars3 :
 forall (r : list (stamp * stamp)) (s : substitution) 
   (env : environment) (t : type),
 is_rename_subst r ->
 domain_of_rename_subst r = gen_vars t env ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 is_subset_list_stamp
   (gen_vars (extend_subst_type (rename_to_subst r) t) env)
   (range_of_rename_subst r).

Proof.
intros.
apply (is_subset_gen_vars2 r env t H); auto.
rewrite H0; apply free_and_bound_are_disjoints.
rewrite H0; apply (subset_reflexivity (gen_vars t env)).
Qed.

Inductive is_a_set_of_stamps : list stamp -> Prop :=
  | nil_is_set : is_a_set_of_stamps nil
  | cons_is_set :
      forall (l : list stamp) (a : stamp),
      is_a_set_of_stamps l ->
      in_list_stamp a l = false -> is_a_set_of_stamps (a :: l).
Hint Resolve nil_is_set.

Lemma range_lt_stamp :
 forall (l : list stamp) (N b : stamp),
 in_list_stamp b (range_of_rename_subst (compute_renaming2 N l)) = true ->
 le_stamp N b.

Proof.
simple induction l.
(* l=[] *)
simpl in |- *; intros; discriminate H.
(* l=a::l0 *)
do 5 intro; simpl in |- *.
elim (stamp_dec b N).
(* b=N *)
intros eq_b_N; rewrite eq_b_N; rewrite eq_stamp_reflexivity; auto.
(* b <> N *)
intros neq_b_N; rewrite (eq_stamp_diff b N neq_b_N); simpl in |- *; intros.
apply lt_le_stamp.
apply lt_le_stamp_trans with (st2 := succ_stamp N); auto.
Qed.

Lemma compute_injective :
 forall (l : list stamp) (N : stamp),
 lt_stamp (max_list_stamp l) N ->
 is_a_set_of_stamps l ->
 forall x y : stamp,
 in_list_stamp x l = true ->
 in_list_stamp y l = true ->
 x <> y ->
 apply_rename_subst (compute_renaming2 N l) x <>
 apply_rename_subst (compute_renaming2 N l) y.

Proof.

simple induction l.
(* l = [] *)
auto.
(* l=a::l0 *)
do 8 intro.
elim (stamp_dec x a).
(* x=a *)
intros eq_x_a; simpl in |- *; rewrite eq_x_a; rewrite eq_stamp_reflexivity;
 simpl in |- *.
intros.
generalize H3; rewrite (eq_stamp_diff y a); simpl in |- *; intros.
elim (domain_range_rename_subst (compute_renaming2 (succ_stamp N) l0) y).
intros x0 Px0; elim Px0; intros.
rewrite H7.
hnf in |- *; intros.
apply
 (lt_stamp_n_m_diff N x0
    (lt_le_stamp_trans N (succ_stamp N) x0 (lt_succ_stamp N)
       (range_lt_stamp l0 (succ_stamp N) x0 H6))).
assumption.
rewrite (domain_of_compute_renaming l0 (succ_stamp N)); assumption.
auto.
(* x <> a*)
intros neq_x_a; simpl in |- *; rewrite (eq_stamp_diff x a neq_x_a);
 simpl in |- *.
elim (stamp_dec y a).
(* y=a *)
intros eq_y_a; rewrite eq_y_a; rewrite eq_stamp_reflexivity; simpl in |- *;
 intros.
elim (domain_range_rename_subst (compute_renaming2 (succ_stamp N) l0) x).
intros x0 Px0; elim Px0; intros.
rewrite H6.
hnf in |- *; intros.
elim
 (lt_stamp_n_m_diff N x0
    (lt_le_stamp_trans N (succ_stamp N) x0 (lt_succ_stamp N)
       (range_lt_stamp l0 (succ_stamp N) x0 H5))); 
 auto.
rewrite (domain_of_compute_renaming l0 (succ_stamp N)); assumption.
(* y <> a*)
intros neq_y_a; simpl in |- *; rewrite (eq_stamp_diff y a neq_y_a);
 simpl in |- *.
intros; apply (H (succ_stamp N)).
generalize H0; simpl in |- *; intros.
apply (le_lt_stamp_trans (max_list_stamp l0) N (succ_stamp N)).
apply (lt_le_stamp (max_list_stamp l0) N).
apply
 (le_lt_stamp_trans (max_list_stamp l0) (max_stamp a (max_list_stamp l0)) N
    (le_stamp_max_r a (max_list_stamp l0)) H5).
apply (lt_succ_stamp N).
inversion H1; auto.
assumption.
assumption.
assumption.
Qed.

Lemma compute_renaming_is_rename_subst2 :
 forall (l : list stamp) (N : stamp),
 lt_stamp (max_list_stamp l) N ->
 is_a_set_of_stamps l -> is_rename_subst (compute_renaming2 N l).

Proof.
intros; unfold is_rename_subst in |- *.
(* first part of is_rename_subst *)
rewrite domain_of_compute_renaming; split.
unfold are_disjoints in |- *.
intros.
apply
 (range_compute_renaming x l N
    (le_lt_stamp_trans x (max_list_stamp l) N (lt_max_list l x H1) H)).
(* second part of is_rename_subst *)
intros; apply (compute_injective l N H); auto.
Qed.

Lemma union_is_a_set :
 forall l1 l2 : list stamp,
 is_a_set_of_stamps l1 ->
 is_a_set_of_stamps l2 -> is_a_set_of_stamps (union_list_stamp l1 l2).

Proof.
simple induction l1.
(* l1=[] *)
auto.
(* l1=a::l *)
intros; simpl in |- *.
inversion H0.
elim (bool_dec (in_list_stamp a l2)).
(* (in_list_stamp a l2)=true *)
intros is_in_list; rewrite is_in_list; simpl in |- *; apply (H l2 H4 H1).
(* (in_list_stamp a l2)=false *)
intros not_in_list; rewrite not_in_list; simpl in |- *.
apply
 (cons_is_set (union_list_stamp l l2) a (H l2 H4 H1)
    (not_in_list_union_inversion l l2 a H5 not_in_list)).
Qed.

Lemma gen_vars_is_a_set :
 forall (t : type) (env : environment), is_a_set_of_stamps (gen_vars t env).

Proof.
simple induction t.
(* Nat *)
auto.
(* Var s*)
simpl in |- *; intros.
elim (bool_dec (in_list_stamp s (FV_env env))).
(* (in_list_stamp s (FV_env env))=true *)
intros s_free_in_env; rewrite s_free_in_env; simpl in |- *; auto.
(* (in_list_stamp s (FV_env env))=false *)
intros s_not_free_in_env; rewrite s_not_free_in_env; simpl in |- *.
apply cons_is_set; auto.
(* Arrow t1 t2 *)
intros; simpl in |- *.
apply (union_is_a_set (gen_vars t0 env) (gen_vars t1 env) (H env) (H0 env)).
Qed.
 
Lemma exists_renaming_not_concerned_with2 :
 forall l l1 l2 : list stamp,
 is_a_set_of_stamps l ->
 {r : list (stamp * stamp) | renaming_of_not_concerned_with r l l1 l2}.

Proof.
intros.
exists
 (compute_renaming2
    (succ_stamp
       (max_stamp (max_list_stamp l)
          (max_stamp (max_list_stamp l1) (max_list_stamp l2)))) l).
apply renaming_of_not_concerned_with_intro.
(* first subgoal for renaming_of_not_concerned_with *)
apply compute_renaming_is_rename_subst2; auto.
apply
 le_lt_stamp_trans
  with
    (st2 := max_stamp (max_list_stamp l)
              (max_stamp (max_list_stamp l1) (max_list_stamp l2))); 
 auto.
(* second subgoal for renaming_of_not_concerned_with *)
apply domain_of_compute_renaming.
(* third subgoal for renaming_of_not_concerned_with *)
unfold are_disjoints in |- *; intros.
apply range_compute_renaming.
apply le_lt_stamp_trans with (st2 := max_list_stamp l1); auto.
apply
 le_lt_stamp_trans
  with
    (st2 := max_stamp (max_list_stamp l)
              (max_stamp (max_list_stamp l1) (max_list_stamp l2))); 
 auto.
apply
 le_stamp_trans
  with (st2 := max_stamp (max_list_stamp l1) (max_list_stamp l2)); 
 auto.
(* fourth subgoal for renaming_of_not_concerned_with *)
apply are_disjoints_symetry.
unfold are_disjoints in |- *; intros.
apply range_compute_renaming.
apply le_lt_stamp_trans with (st2 := max_list_stamp l2); auto.
apply
 le_lt_stamp_trans
  with
    (st2 := max_stamp (max_list_stamp l)
              (max_stamp (max_list_stamp l1) (max_list_stamp l2))); 
 auto.
apply
 le_stamp_trans
  with (st2 := max_stamp (max_list_stamp l1) (max_list_stamp l2)); 
 auto.
Qed.
 
Lemma renaming_not_concerned_with_gen_vars :
 forall (r : list (stamp * stamp)) (s : substitution) 
   (env : environment) (t : type),
 renaming_of_not_concerned_with r (gen_vars t env) (FV_env env) (FV_subst s) ->
 are_disjoints (FV_subst s)
   (gen_vars (extend_subst_type (rename_to_subst r) t) env).

Proof.
intros; inversion H; unfold FV_subst in |- *.
unfold FV_subst in H3.
apply disjoint_list_and_union.
apply
 (disjoint_subset_bis (domain_of_substitution s) (range_of_rename_subst r)
    (gen_vars (extend_subst_type (rename_to_subst r) t) env)).
apply
 (disjoint_list_and_union_inversion1 (range_of_rename_subst r)
    (domain_of_substitution s) (range_of_substitution s)); 
 auto.
apply (is_subset_gen_vars3 r s env t H0 H1 H2).

apply
 (disjoint_subset_bis (range_of_substitution s) (range_of_rename_subst r)
    (gen_vars (extend_subst_type (rename_to_subst r) t) env)).
apply
 (disjoint_list_and_union_inversion2 (range_of_rename_subst r)
    (domain_of_substitution s) (range_of_substitution s)); 
 auto.
apply (is_subset_gen_vars3 r s env t H0 H1 H2).
Qed.

Lemma typage_is_stable_by_substitution :
 forall (e : expr) (t : type) (env : environment) (s : substitution),
 type_of env e t -> type_of (apply_subst_env env s) e (extend_subst_type s t). 

Proof.
simple induction e.
(* Const_nat *)
intros; inversion H; auto.
(* Variable i *)
intros; inversion H.
apply type_of_var with (ts := extend_subst_type_scheme s ts).
apply (Ident_in_apply_subst_env env i s ts H1).
apply (is_gen_instance_stable_by_substitution ts s t H3).
(* Lambda i e *)
intros; inversion H0.
simpl in |- *; apply type_of_lambda.
elim (subst_add_type env i s t0).
apply (H t' (add_environment env i (type_to_type_scheme t0)) s H5).
(* Rec i i0 e *)
intros; inversion H0.
simpl in |- *; apply type_of_rec_fun.
elim (subst_add_type env i0 s t0).
rewrite (apply_subst_arrow_rewrite s t0 t').
elim
 (subst_add_type (add_environment env i0 (type_to_type_scheme t0)) i s
    (Arrow t0 t')).
apply
 (H t'
    (add_environment (add_environment env i0 (type_to_type_scheme t0)) i
       (type_to_type_scheme (Arrow t0 t'))) s H6).
(* Apply e0 e1 *)
intros; inversion H1.
apply
 (type_of_app (apply_subst_env env s) e0 e1 (extend_subst_type s t0)
    (extend_subst_type s t)).
rewrite apply_subst_arrow_rewrite.
apply (H (Arrow t0 t) env s H5).
apply (H0 t0 env s H7).
(* Let_in i e0 e1 *)
intros; inversion H1.
elim
 (exists_renaming_not_concerned_with2 (gen_vars t0 env) 
    (FV_env env) (FV_subst s) (gen_vars_is_a_set t0 env)). intros r ren.
apply
 (type_of_let_in (apply_subst_env env s) e0 e1 i
    (extend_subst_type (compose_subst (rename_to_subst r) s) t0)
    (extend_subst_type s t)).
(*   (type_of (apply_subst_env env s) e0
     (extend_subst_type (compose_subst (rename_to_subst r) s) t0))
*)
elim (s_env_when_s_disjoint_with_env3 (rename_to_subst r) env).
elim (composition_of_substitutions_env (rename_to_subst r) s env).
apply (H t0 env (compose_subst (rename_to_subst r) s) H7).
(*   (are_disjoints (domain_of_substitution (rename_to_subst r))
     (FV_env env))
*)
inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H10; apply free_and_bound_are_disjoints.
(*   (type_of (add_environment (apply_subst_env env s) i
       (gen_type (extend_subst_type (compose_subst (rename_to_subst r) s) t0)
         (apply_subst_env env s))) e1 (extend_subst_type s t))
*)
rewrite composition_of_substitutions_type.
elim
 (gen_in_subst_env2 env s (extend_subst_type (rename_to_subst r) t0)
    (renaming_not_concerned_with_gen_vars r s env t0 ren)).
inversion ren.
rewrite <- gen_alpha4_bis; try rewrite H10; auto.
elim subst_add_type_scheme.
apply (H0 t (add_environment env i (gen_type t0 env)) s H8).
Qed.
