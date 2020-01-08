(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import tools_bool.
Require Import tools.
Require Import langs.
Require Import subset.
Require Import FV.
Require Import subst.
Require Import type_scheme.
Require Import env_poly.

Lemma subset_FV_type :
 forall (t : type) (s : substitution) (s0 : stamp),
 in_list_stamp s0 (FV_type t) = true ->
 is_subset_list_stamp (FV_type (apply_substitution s s0))
   (FV_type (extend_subst_type s t)).

Proof.
do 3 intro; elim t.
(*Nat*)
simpl in |- *; intros; discriminate H.
(*Var*)
intro; simpl in |- *.
intros H; apply is_subset_intro. 
elim (if_false_true (eq_stamp s0 s1) true H); intros.
elim (eq_stamp_equality s0 s1); auto.
(*Arrow*)
intros t0 H0 t1 H1.
simpl in |- *; intros H.
elim (in_union_list_stamp (FV_type t0) (FV_type t1) s0 H); intros.
(* (in_list_stamp s0 (FV_type t0))=true *)
apply
 (subset_of_union1 (FV_type (apply_substitution s s0))
    (FV_type (extend_subst_type s t0)) (FV_type (extend_subst_type s t1))
    (H0 H2)).
(* (in_list_stamp s0 (FV_type t1))=true *)
apply
 (subset_of_union2 (FV_type (apply_substitution s s0))
    (FV_type (extend_subst_type s t0)) (FV_type (extend_subst_type s t1))
    (H1 H2)).
Qed.

Lemma FV_type_scheme_type_to_type_scheme :
 forall t : type, FV_type_scheme (type_to_type_scheme t) = FV_type t.

Proof.
simple induction t; auto.
intros; simpl in |- *.
rewrite H; rewrite H0; auto.
Qed.

Lemma subset_FV_type_scheme :
 forall (s : substitution) (ts : type_scheme) (s0 : stamp),
 in_list_stamp s0 (FV_type_scheme ts) = true ->
 is_subset_list_stamp (FV_type (apply_substitution s s0))
   (FV_type_scheme (extend_subst_type_scheme s ts)).

Proof.
do 3 intro; elim ts.
(*Nat*)
simpl in |- *; intros; discriminate H.
(*Var*)
simpl in |- *; intros; apply is_subset_intro. 
elim (if_false_true (eq_stamp s0 s1) true H); intros.
elim (eq_stamp_equality s0 s1 H0).
rewrite FV_type_scheme_type_to_type_scheme; auto.
(*Gen_var*)
simpl in |- *; intros; discriminate H.
(*Arrow*)
intros t0 H0 t1 H1.
simpl in |- *; intros H.
elim (in_union_list_stamp (FV_type_scheme t0) (FV_type_scheme t1) s0 H);
 intros.
(* (in_list_stamp s0 (FV_type_scheme t0))=true *)
apply
 (subset_of_union1 (FV_type (apply_substitution s s0))
    (FV_type_scheme (extend_subst_type_scheme s t0))
    (FV_type_scheme (extend_subst_type_scheme s t1)) 
    (H0 H2)).
(* (in_list_stamp s0 (FV_type_scheme t1))=true *)
apply
 (subset_of_union2 (FV_type (apply_substitution s s0))
    (FV_type_scheme (extend_subst_type_scheme s t0))
    (FV_type_scheme (extend_subst_type_scheme s t1)) 
    (H1 H2)).
Qed.

Lemma subset_FV_env :
 forall (env : environment) (s : substitution) (s0 : stamp),
 in_list_stamp s0 (FV_env env) = true ->
 is_subset_list_stamp (FV_type (apply_substitution s s0))
   (FV_env (apply_subst_env env s)).

Proof.
simple induction env.
(* env=[] *)
simpl in |- *; intros; discriminate H.
(* env=a::l *)
intro a; elim a; clear a; intros x ts; simpl in |- *; intros.
elim (in_union_list_stamp (FV_type_scheme ts) (FV_env l) s0 H0); intros.
(* (in_list_stamp s0 (FV_type_scheme ts))=true *)
apply
 (subset_of_union1 (FV_type (apply_substitution s s0))
    (FV_type_scheme (extend_subst_type_scheme s ts))
    (FV_env (apply_subst_env l s)) (subset_FV_type_scheme s ts s0 H1)).
(* (in_list_stamp s0 (FV_env l))=true *)
apply
 (subset_of_union2 (FV_type (apply_substitution s s0))
    (FV_type_scheme (extend_subst_type_scheme s ts))
    (FV_env (apply_subst_env l s)) (H s s0 H1)).
Qed.







