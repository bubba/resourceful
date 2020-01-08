(* Author : Catherine Dubois *)

Require Import List.
Require Import langs.
Require Import type_scheme.
Require Import env_poly.
Require Import DB_gen_stable.
Require Import disjoints.
Require Import FV.
Require Import subst.

Lemma s_ts_when_s_disjoint_with_ts :
 forall (s : substitution) (ts : type_scheme),
 are_disjoints (domain_of_substitution s) (FV_type_scheme ts) ->
 extend_subst_type_scheme s ts = ts.
 
Proof.
simple induction ts.
(* Nat_ts *)
auto.
(* Var_ts *)
simpl in |- *; intros.
rewrite is_not_in_domain_subst; auto.
apply disjoint_inversion2 with (l' := s0 :: nil); auto.
(* Gen_var *)
auto.
(* Arrow_ts *)
simpl in |- *; intros.
rewrite H.
rewrite H0; auto.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type_scheme t); auto.
apply disjoint_list_and_union_inversion1 with (l2 := FV_type_scheme t0); auto.
Qed.

Lemma s_env_when_s_disjoint_with_env3 :
 forall (s : substitution) (env : environment),
 are_disjoints (domain_of_substitution s) (FV_env env) ->
 apply_subst_env env s = env.

Proof.
simple induction env.
(* env=[] *)
auto.
(* env=a::l *)
simple induction a; intros x y; simpl in |- *; intros; simpl in |- *.
rewrite s_ts_when_s_disjoint_with_ts.
rewrite H; auto.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type_scheme y); auto.
apply disjoint_list_and_union_inversion1 with (l2 := FV_env l); auto.
Qed.
