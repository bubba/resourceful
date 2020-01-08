(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import langs.
Require Import List.
Require Import subst.
Require Import FV.
Require Import tools.
Require Import env_poly.
Require Import type_scheme.
Require Import subset_FV_env.

Lemma apply_subst_cons :
 forall (l : substitution) (y0 : type) (y : stamp),
 apply_substitution ( (*stamp*type*) (y, y0) :: l) y = y0.

Proof.
unfold apply_substitution in |- *; simpl in |- *.
intros; rewrite (eq_stamp_reflexivity y); auto.
Qed.

Lemma apply_subst_cons2 :
 forall (l : substitution) (y0 : type) (x y : stamp),
 x <> y -> apply_substitution ((y, y0) :: l) x = apply_substitution l x.

Proof.
unfold apply_substitution in |- *; simpl in |- *.
intros; rewrite (eq_stamp_diff x y); auto.
Qed.

Lemma not_in_range :
 forall (s : substitution) (st x : stamp),
 st <> x ->
 in_list_stamp st (range_of_substitution s) = false ->
 in_list_stamp st (FV_type (apply_substitution s x)) = false.

Proof.
simple induction s.
(* s=[] *)
simpl in |- *; intros; rewrite (eq_stamp_diff st x H); simpl in |- *; auto.
(* s=a::l *)
intros a l H st x H0.
elim a; intros y y0; simpl in |- *.
elim (stamp_dec x y).
(* x=y *)
intro eq_x_y; rewrite eq_x_y; simpl in |- *; intros.
rewrite apply_subst_cons.
elim (not_in_list_union (FV_type y0) (range_of_substitution l) st); auto.
(* x <> y *)
intro neq_x_y; rewrite (apply_subst_cons2 l y0 x y neq_x_y).
intros H1; apply (H st x H0).
elim (not_in_list_union (FV_type y0) (range_of_substitution l) st); auto.
Qed.

Lemma not_in_FV_type :
 forall (st : stamp) (s : substitution) (t : type),
 in_list_stamp st (range_of_substitution s) = false ->
 in_list_stamp st (FV_type t) = false ->
 in_list_stamp st (FV_type (extend_subst_type s t)) = false.

Proof.
simple induction t.
(* Nat *)
auto.
(*Var st'*)
intro st'; elim (stamp_dec st st'); intro eq.
(*st'=st*)
rewrite eq; simpl in |- *; rewrite (eq_stamp_reflexivity st'); simpl in |- *;
 intros.
discriminate H0.
(*st'<>st*)
intros; simpl in |- *.
apply not_in_range; auto.
(*Arrow*)
simpl in |- *; intros.
elim (not_in_list_union (FV_type t0) (FV_type t1) st H2).
intros.
apply not_in_list_union_inversion; auto.
Qed.

Lemma not_in_FV_type_scheme :
 forall (st : stamp) (s : substitution) (ts : type_scheme),
 in_list_stamp st (range_of_substitution s) = false ->
 in_list_stamp st (FV_type_scheme ts) = false ->
 in_list_stamp st (FV_type_scheme (extend_subst_type_scheme s ts)) = false.

Proof.
simple induction ts.
(* Nat_ts *)
auto.
(*Var_ts*)
intro s0; simpl in |- *.
elim (stamp_dec st s0); intro eq.
rewrite eq; rewrite eq_stamp_reflexivity; simpl in |- *.
intros; discriminate H0.
rewrite eq_stamp_diff; auto.
simpl in |- *; rewrite FV_type_scheme_type_to_type_scheme.
intros; apply not_in_range; auto.
(* Gen_var *)
auto.
(*Arrow_ts*)
simpl in |- *; intros.
apply not_in_list_union_inversion.
elim (not_in_list_union (FV_type_scheme t) (FV_type_scheme t0) st H2); intros;
 apply (H H1 H3).
elim (not_in_list_union (FV_type_scheme t) (FV_type_scheme t0) st H2); intros;
 apply (H0 H1 H4).
Qed.

Lemma not_in_FV_env :
 forall (st : stamp) (s : substitution) (env : environment),
 in_list_stamp st (range_of_substitution s) = false ->
 in_list_stamp st (FV_env env) = false ->
 in_list_stamp st (FV_env (apply_subst_env env s)) = false.

Proof.
simple induction env.
(* env=[] *)
auto.
(* env=a::l *)
simple induction a; intros x ts; simpl in |- *; intros.
elim (not_in_list_union (FV_type_scheme ts) (FV_env l) st H1); intros.
apply not_in_list_union_inversion.
apply not_in_FV_type_scheme; auto.
apply H; auto.
Qed.

