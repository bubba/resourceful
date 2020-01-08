(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import tools_bool.
Require Import tools.
Require Import List.
Require Import langs.
Require Import FV.
Require Import subst.
Require Import env_poly.
Require Import type_scheme.
Require Import generic_DB.
Require Import not_in_FV_env.
Require Import subset.
Require Import disjoints.
Require Import subset_FV_env.

Definition FV_subst (s : substitution) :=
  union_list_stamp (domain_of_substitution s) (range_of_substitution s).


Fixpoint domain_of_rename_subst (r : list (stamp * stamp)) : 
 list stamp :=
  match r with
  | nil => nil (A:=stamp)
  | a :: l' => fst a :: domain_of_rename_subst l'
  end.

Fixpoint range_of_rename_subst (r : list (stamp * stamp)) : 
 list stamp :=
  match r with
  | nil => nil (A:=stamp)
  | a :: l' => snd a :: range_of_rename_subst l'
  end.

Fixpoint apply_rename_subst (r : list (stamp * stamp)) 
 (v : stamp) {struct r} : stamp :=
  match r with
  | nil => v
  | vt :: l =>
      if_ stamp (eq_stamp v (fst vt)) (snd vt) (apply_rename_subst l v)
  end.

Fixpoint rename_to_subst (r : list (stamp * stamp)) : substitution :=
  match r with
  | nil => nil (A:=stamp * type)
  | vt :: l => (fst vt, Var (snd vt)) :: rename_to_subst l
  end.

(*substitution de renommage = liste de stamp*stamp*)
Definition is_rename_subst (r : list (stamp * stamp)) :=
  are_disjoints (domain_of_rename_subst r) (range_of_rename_subst r) /\
  (forall x y : stamp,
   in_list_stamp x (domain_of_rename_subst r) = true ->
   in_list_stamp y (domain_of_rename_subst r) = true ->
   x <> y -> apply_rename_subst r x <> apply_rename_subst r y).

(*map apply_rename_subst*)
Fixpoint apply_rename_list (r : list (stamp * stamp)) 
 (l : list stamp) {struct l} : list stamp :=
  match l with
  | nil => nil (A:=stamp)
  | v :: l0 => apply_rename_subst r v :: apply_rename_list r l0
  end.

Lemma length_apply_rename_list :
 forall (l : list stamp) (r : list (stamp * stamp)),
 length (apply_rename_list r l) = length l.
Proof.
simple induction l; auto.
intros; simpl in |- *; rewrite H; auto.
Qed.

Lemma app_apply_rename_list :
 forall (l : list stamp) (r : list (stamp * stamp)) (s : stamp),
 apply_rename_list r (l ++ s :: nil) =
  (*stamp*) apply_rename_list r l ++  (*stamp*) apply_rename_subst r s :: nil.
Proof.
simple induction l; auto.
intros; simpl in |- *; rewrite H; auto.
Qed.


Lemma subset_cons :
 forall (l l0 : list stamp) (a : stamp),
 is_subset_list_stamp (a :: l0) l -> is_subset_list_stamp l0 l.

Proof.
intros; apply is_subset_intro; intros.
inversion H; apply H1.
simpl in |- *; apply if_same_results_true; auto.
Qed.

Lemma index_rename :
 forall (r : list (stamp * stamp)) (x : stamp) (l : list stamp),
 is_rename_subst r ->
 is_subset_list_stamp l (domain_of_rename_subst r) ->
 in_list_stamp x (domain_of_rename_subst r) = true ->
 index l x = index (apply_rename_list r l) (apply_rename_subst r x).

Proof.
simple induction l.
(* l=[] *)
auto.
(* l=a::l0 *)
intros; simpl in |- *; elim (stamp_dec x a).
(*x=a*)
intros eq_x_a; rewrite eq_x_a. 
do 2 rewrite eq_stamp_reflexivity; auto.
(*x<>a*)
intros neq_x_a; rewrite (eq_stamp_diff x a neq_x_a); simpl in |- *.
elim (H H0 (subset_cons (domain_of_rename_subst r) l0 a H1) H2).
unfold is_rename_subst in H0; elim H0; clear H0; intros H3 H4.
rewrite
 (eq_stamp_diff (apply_rename_subst r x) (apply_rename_subst r a)
    (H4 x a H2 (subset_cons_subset a (domain_of_rename_subst r) l0 H1)
       neq_x_a)).
simpl in |- *; auto.
Qed.


Lemma apply_substitution_rename_to_subst_rewrite :
 forall (s : stamp) (r : list (stamp * stamp)),
 apply_substitution (rename_to_subst r) s = Var (apply_rename_subst r s).

Proof.
simple induction r.
(* r=[] *)
auto.
(* r=a::l *)
simple induction a; intro y; intro; simpl in |- *.
elim (stamp_dec s y).
(* s=y *)
intros eq_s_y; rewrite eq_s_y; rewrite eq_stamp_reflexivity; simpl in |- *.
unfold apply_substitution in |- *; simpl in |- *.
rewrite (eq_stamp_reflexivity y); auto.
(* s <> y *)
intros neq_s_y; rewrite (eq_stamp_diff s y neq_s_y).
unfold apply_substitution in |- *; simpl in |- *.
rewrite (eq_stamp_diff s y neq_s_y); auto.
Qed.

Lemma domain_range_rename_subst :
 forall (r : list (stamp * stamp)) (s : stamp),
 in_list_stamp s (domain_of_rename_subst r) = true ->
 {y : stamp |
 in_list_stamp y (range_of_rename_subst r) = true /\
 apply_rename_subst r s = y}.

Proof.
simple induction r.
(* r=[] *)
simpl in |- *; intros; discriminate H.
(* r=a::l *)
simple destruct a. intros s s0 l H s1 H0.
elim (stamp_dec s1 s).
(* s=s1 *)
intro eq_s_s1; rewrite eq_s_s1.
exists s0; simpl in |- *.
rewrite eq_stamp_reflexivity; simpl in |- *.
rewrite eq_stamp_reflexivity; auto.
(* s <> s1 *)
intro neq_s_s1; simpl in |- *; rewrite (eq_stamp_diff s1 s neq_s_s1);
 simpl in |- *.
elim (H s1).
intros x Hyp_x. decompose [and] Hyp_x.
exists x.
rewrite
 (if_same_results_true (eq_stamp x s0) true
    (in_list_stamp x (range_of_rename_subst l))); auto.
simpl in H0.
rewrite (eq_stamp_diff s1 s neq_s_s1) in H0; simpl in |- *; auto.
Qed.

Lemma rename_range :
 forall (s : stamp) (r : list (stamp * stamp)) (l : list stamp),
 is_rename_subst r ->
 are_disjoints l (range_of_rename_subst r) ->
 in_list_stamp s (domain_of_rename_subst r) = true ->
 in_list_stamp (apply_rename_subst r s) l = false.

Proof.
intros.
elim (domain_range_rename_subst r s H1); intros st Pst.
elim Pst; intros.
rewrite H3.
apply disjoint_inversion2 with (l' := range_of_rename_subst r); auto.
Qed.

Lemma is_not_in_domain :
 forall (x : stamp) (r : list (stamp * stamp)),
 in_list_stamp x (domain_of_rename_subst r) = false ->
 apply_rename_subst r x = x.

Proof.
simple induction r.
(* r=[] *)
auto.
(* r=a::l *)
simple induction a; simpl in |- *; intros y y0 l H.
elim (stamp_dec x y).
(* x=y *)
intros eq_x_y; rewrite eq_x_y; rewrite eq_stamp_reflexivity; simpl in |- *.
intros pb; discriminate pb.
(* x<>y *)
intros neq_x_y; rewrite eq_stamp_diff; auto.
Qed.

Lemma snd_gen_aux_arrow_rewrite :
 forall (t0 t1 : type) (env : environment) (l : list stamp),
 snd (gen_aux (Arrow t0 t1) env l) =
 snd (gen_aux t1 env (snd (gen_aux t0 env l))).
Proof.
intros; simpl in |- *.
elim (gen_aux t0 env l); intros ts0 l0; simpl in |- *.
elim (gen_aux t1 env l0); intros ts1 l'; auto.
Qed.

Lemma fst_gen_aux_arrow_rewrite :
 forall (t0 t1 : type) (env : environment) (l : list stamp),
 fst (gen_aux (Arrow t0 t1) env l) =
 Arrow_ts (fst (gen_aux t0 env l))
   (fst (gen_aux t1 env (snd (gen_aux t0 env l)))).
Proof.
intros; simpl in |- *.
elim (gen_aux t0 env l); intros ts0 l0; simpl in |- *.
elim (gen_aux t1 env l0); intros ts1 l'; auto.
Qed.


Lemma is_subset_gen_aux2 :
 forall (env : environment) (r : list (stamp * stamp)) 
   (t : type) (l l' : list stamp),
 is_rename_subst r ->
 are_disjoints (domain_of_rename_subst r) (FV_env env) ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 is_subset_list_stamp l (domain_of_rename_subst r) ->
 is_subset_list_stamp (gen_vars t env) (domain_of_rename_subst r) ->
 is_subset_list_stamp (snd (gen_aux t env l)) (domain_of_rename_subst r).
Proof.
simple induction t.
(* Nat *)
auto.
(* Var s *)
intros; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro s_free_in_env;
 rewrite s_free_in_env; simpl in |- *; auto.
elim (index l s); simpl in |- *; intros; auto.
apply subset_app_inv; auto.
inversion H3; apply H4.
simpl in |- *; rewrite s_free_in_env; simpl in |- *;
 rewrite eq_stamp_reflexivity; auto.
(* Arrow t0 t1 *)
intros; rewrite snd_gen_aux_arrow_rewrite.
apply H0; auto.
apply H; auto.
apply subset_of_union_inversion1 with (l2 := gen_vars t1 env); auto.
apply subset_of_union_inversion2 with (l1 := gen_vars t0 env); auto.
Qed.

Lemma gen_aux_alpha2 :
 forall (env : environment) (r : list (stamp * stamp)) 
   (t : type) (l : list stamp),
 is_rename_subst r ->
 is_subset_list_stamp (gen_vars t env) (domain_of_rename_subst r) ->
 are_disjoints (domain_of_rename_subst r) (FV_env env) ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 is_subset_list_stamp l (domain_of_rename_subst r) ->
 gen_aux (extend_subst_type (rename_to_subst r) t) env
   (apply_rename_list r l) =
 (fst (gen_aux t env l), apply_rename_list r (snd (gen_aux t env l))).

Proof.
simple induction t.
(* Nat *)
auto.
(* Var s *)
do 3 intro; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intros s_free_in_env;
 rewrite s_free_in_env; simpl in |- *.
intros; rewrite apply_substitution_rename_to_subst_rewrite.
rewrite is_not_in_domain; simpl in |- *.
rewrite s_free_in_env; auto.
apply disjoint_inversion2 with (l' := FV_env env); auto.
intros; rewrite apply_substitution_rename_to_subst_rewrite; simpl in |- *.
elim (index_rename r s l); auto.
rewrite rename_range; auto.
elim (index l s); auto.
simpl in |- *; rewrite length_apply_rename_list;
 rewrite <- app_apply_rename_list; auto.

inversion H0; apply H4; simpl in |- *; rewrite eq_stamp_reflexivity; auto.

inversion H0; apply H4; simpl in |- *; rewrite eq_stamp_reflexivity; auto.
(* Arrow t0 t1 *)
intros; simpl in |- *.
rewrite (H l); auto.
rewrite (H0 (snd (gen_aux t0 env l))); auto.
elim (gen_aux t0 env l); intro; intro y0; simpl in |- *.
elim (gen_aux t1 env y0); auto.
apply subset_of_union_inversion2 with (l1 := gen_vars t0 env); auto.
apply is_subset_gen_aux2; auto.
apply subset_of_union_inversion1 with (l2 := gen_vars t1 env); auto.
apply subset_of_union_inversion1 with (l2 := gen_vars t1 env); auto.
Qed.

Inductive renaming_of_not_concerned_with :
list (stamp * stamp) -> list stamp -> list stamp -> list stamp -> Prop :=
    renaming_of_not_concerned_with_intro :
      forall (r : list (stamp * stamp)) (l l1 l2 : list stamp),
      is_rename_subst r ->
      domain_of_rename_subst r = l ->
      are_disjoints l1 (range_of_rename_subst r) ->
      are_disjoints (range_of_rename_subst r) l2 ->
      renaming_of_not_concerned_with r l l1 l2.

Lemma gen_alpha4_bis :
 forall (env : environment) (r : list (stamp * stamp)) (t : type),
 is_rename_subst r ->
 domain_of_rename_subst r = gen_vars t env ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 gen_type t env = gen_type (extend_subst_type (rename_to_subst r) t) env.
Proof.
intros; unfold gen_type in |- *.
inversion H.
change
  (fst (gen_aux t env nil) =
   fst
     (gen_aux (extend_subst_type (rename_to_subst r) t) env
        (apply_rename_list r nil))) in |- *.
rewrite gen_aux_alpha2; try rewrite H0; auto.
apply free_and_bound_are_disjoints.
Qed.

Lemma is_not_generalizable_aux :
 forall (env : environment) (t : type) (l : list stamp),
 is_subset_list_stamp (FV_type t) (FV_env env) ->
 gen_aux t env l = (type_to_type_scheme t, l).

Proof.
do 3 intro; elim t; auto.
simpl in |- *; intros; inversion H.
rewrite H0; auto.
simpl in |- *; intros.
rewrite H. 
rewrite H0; auto.
apply subset_of_union_inversion2 with (l1 := FV_type t0); auto.
apply subset_of_union_inversion1 with (l2 := FV_type t1); auto.
(*Apply subset_of_union_inversion2 with l1:=(FV_type t0);  Auto.*)
Qed.

Lemma is_not_in_domain_subst :
 forall (x : stamp) (s : substitution),
 in_list_stamp x (domain_of_substitution s) = false ->
 apply_substitution s x = Var x.

Proof.
simple induction s.
(* s=[] *)
auto.
(* s=a::l *)
simple induction a; simpl in |- *; intros st t l H.
elim (stamp_dec x st).
(* x=st *)
intros eq_x_st; rewrite eq_x_st; rewrite eq_stamp_reflexivity; simpl in |- *.
intro pb; discriminate pb.
(* x<>st *)
intros neq_x_st; rewrite (eq_stamp_diff x st neq_x_st); simpl in |- *.
unfold apply_substitution in |- *; simpl in |- *.
rewrite (eq_stamp_diff x st neq_x_st); auto.
Qed.

Lemma gen_aux_in_subst_env :
 forall (env : environment) (s : substitution) (t : type) (l : list stamp),
 are_disjoints (domain_of_substitution s) (gen_vars t env) ->
 are_disjoints (range_of_substitution s) (gen_vars t env) ->
 gen_aux (extend_subst_type s t) (apply_subst_env env s) l =
 (extend_subst_type_scheme s (fst (gen_aux t env l)), snd (gen_aux t env l)).

Proof.
simple induction t.
(* Nat *)
auto.
(* Var s0 *)
simpl in |- *; intro.
elim (bool_dec (in_list_stamp s0 (FV_env env))); intros s_free_in_env;
 rewrite s_free_in_env; simpl in |- *.
intros; rewrite is_not_generalizable_aux; auto.
apply subset_FV_env; auto.
intros; rewrite is_not_in_domain_subst.
simpl in |- *; rewrite not_in_FV_env; auto.
simpl in |- *; elim (index l s0); auto.
apply disjoint_inversion2 with (l' := s0 :: nil); auto.
apply disjoint_inversion2 with (l' := s0 :: nil); auto.
(* Arrow t0 t1 *)
intros; simpl in |- *.
rewrite (H l); auto.
elim (gen_aux t0 env l); intro; intro y0; simpl in |- *.
rewrite (H0 y0); auto.
elim (gen_aux t1 env y0); intros; auto.
apply disjoint_list_and_union_inversion2 with (l1 := gen_vars t0 env); auto.
apply disjoint_list_and_union_inversion2 with (l1 := gen_vars t0 env); auto.
apply disjoint_list_and_union_inversion1 with (l2 := gen_vars t1 env); auto.
apply disjoint_list_and_union_inversion1 with (l2 := gen_vars t1 env); auto.
Qed.

Lemma gen_in_subst_env2 :
 forall (env : environment) (s : substitution) (t : type),
 are_disjoints (FV_subst s) (gen_vars t env) ->
 extend_subst_type_scheme s (gen_type t env) =
 gen_type (extend_subst_type s t) (apply_subst_env env s).

Proof.
intros; simpl in |- *.
unfold gen_type in |- *; unfold FV_subst in H.
rewrite gen_aux_in_subst_env; auto.
apply are_disjoints_symetry.
apply disjoint_list_and_union_inversion1 with (l2 := range_of_substitution s).
apply are_disjoints_symetry; auto.
apply are_disjoints_symetry.
apply
 disjoint_list_and_union_inversion2 with (l1 := domain_of_substitution s).
apply are_disjoints_symetry; auto.
Qed.

