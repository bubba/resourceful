(* Author : Catherine Dubois *)

Require Import List.
Require Import Lt.
Require Import generic_DB.
Require Import subst.
Require Import langs.
Require Import type_scheme.
Require Import tools.
Require Import tools_bool.
Require Import order_stamp.
Require Import env_poly.
Require Import DB_gen_stable.
Require Import tools_stable.
Require Import FV.
Require Import subset.
Require Import unification.
Require Import tools_correctness.
Require Import max.
(**************************************************************************)
Lemma FV_subset_range :
 forall (s : substitution) (st : stamp),
 in_list_stamp st (domain_of_substitution s) = true ->
 is_subset_list_stamp (FV_type (extend_subst_type s (Var st)))
   (range_of_substitution s).
simple induction s.
simpl in |- *; intros st pb; discriminate pb.

intro a; elim a; intros x T l ind_hyp st.
simpl in |- *; unfold apply_substitution in |- *.
elim (stamp_dec st x); intro eq1; simpl in |- *.
rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; intro Hyp.
change
  (is_subset_list_stamp (FV_type (extend_subst_type l (Var st)))
     (union_list_stamp (FV_type T) (range_of_substitution l))) 
 in |- *.
apply subset_of_union2; auto.
Qed.


(**************************************************************************)

Lemma FV_type_subset :
 forall (s : substitution) (t : type),
 is_subset_list_stamp (FV_type (extend_subst_type s t))
   (union_list_stamp (FV_type t) (range_of_substitution s)).
simple induction t; auto.
(*Var st*)
intro st.
elim (bool_dec (in_list_stamp st (domain_of_substitution s)));
 intro st_mem_dom_s.
(*(in_list_stamp st (domain_of_substitution s))=true*)
apply
 (subset_of_union2 (FV_type (extend_subst_type s (Var st)))
    (FV_type (Var st)) (range_of_substitution s)
    (FV_subset_range s st st_mem_dom_s)).
(*(in_list_stamp st (domain_of_substitution s))=false*)
unfold extend_subst_type in |- *; rewrite is_not_in_domain_subst; auto.
(*Arrow*)
intros; simpl in |- *; apply union_subset.
apply
 subset_trans
  with
    (l2 := union_list_stamp
             (union_list_stamp (FV_type t0) (range_of_substitution s))
             (FV_type t1)); auto.
apply
 subset_trans
  with (l2 := union_list_stamp (FV_type t0) (range_of_substitution s)); 
 auto.
apply
 subset_trans
  with
    (l2 := union_list_stamp (FV_type t0)
             (union_list_stamp (FV_type t1) (range_of_substitution s))); 
 auto.
apply
 subset_trans
  with (l2 := union_list_stamp (FV_type t1) (range_of_substitution s)); 
 auto.
Qed.

(*************************************************************)
Inductive new_tv_type : type -> stamp -> Prop :=
  | new_tv_Nat : forall st : stamp, new_tv_type Nat st
  | new_tv_Var :
      forall n m : nat, n < m -> new_tv_type (Var (Stamp n)) (Stamp m)
  | new_tv_Arrow :
      forall (t1 t2 : type) (st : stamp),
      new_tv_type t1 st -> new_tv_type t2 st -> new_tv_type (Arrow t1 t2) st.

Hint Resolve new_tv_Nat.
Hint Resolve new_tv_Var.
Hint Resolve new_tv_Arrow.

Lemma new_tv_Var_stamp :
 forall st1 st2 : stamp, lt_stamp st1 st2 -> new_tv_type (Var st1) st2.
do 2 intro; case st1; case st2.
auto.
Qed.
Hint Resolve new_tv_Var_stamp.

(*equivalent definition*)
Lemma new_tv_type_FV :
 forall (st : stamp) (t : type),
 new_tv_type t st ->
 forall x : stamp, in_list_stamp x (FV_type t) = true -> lt_stamp x st.
Proof.
simple induction t.
(*Nat*)
simpl in |- *; intros.
discriminate H0.
(*Var*)
simpl in |- *; do 2 intro.
inversion_clear H.
intro.
elim (stamp_dec x (Stamp n)); intro eq.
rewrite eq; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; intro true_is_false; discriminate true_is_false.
(*Arrow*)
simpl in |- *; do 5 intro.
inversion_clear H1.
intros.
elim (in_union_list_stamp (FV_type t0) (FV_type t1) x H1); auto.
Qed.




Lemma FV_new_tv_type :
 forall (st : stamp) (t : type),
 (forall x : stamp, in_list_stamp x (FV_type t) = true -> lt_stamp x st) ->
 new_tv_type t st.
Proof.
simple induction t.
(*Nat*)
auto.
(*Var*)
simpl in |- *; intros.
apply new_tv_Var_stamp.
apply H.
rewrite eq_stamp_reflexivity; auto.
(*Arrow*)
simpl in |- *; intros.
apply new_tv_Arrow.
apply H; intros.
apply H1.
apply in_first_componant_union_list_stamp; auto.
apply H0; intros.
apply H1.
apply in_second_componant_union_list_stamp; auto.
Qed.
(*******************************************************************)
Inductive new_tv_type_scheme : type_scheme -> stamp -> Prop :=
  | new_tv_ts_Nat : forall st : stamp, new_tv_type_scheme Nat_ts st
  | new_tv_ts_Var :
      forall st st' : stamp,
      lt_stamp st st' -> new_tv_type_scheme (Var_ts st) st'
  | new_tv_ts_Gen :
      forall st st' : stamp, new_tv_type_scheme (Gen_var st) st'
  | new_tv_ts_Arrow :
      forall (ts1 ts2 : type_scheme) (st : stamp),
      new_tv_type_scheme ts1 st ->
      new_tv_type_scheme ts2 st -> new_tv_type_scheme (Arrow_ts ts1 ts2) st.
Hint Resolve new_tv_ts_Nat.
Hint Resolve new_tv_ts_Var.
Hint Resolve new_tv_ts_Arrow.
Hint Resolve new_tv_ts_Gen.



(*
Inductive new_tv_env : environment -> stamp -> Prop :=
new_tv_env_intro :  (env : environment) (st : stamp)
( (x : stamp) (in_list_stamp x (FV_env env))=true -> (lt_stamp x st)) ->
     (new_tv_env env st).
*)

Inductive new_tv_env : environment -> stamp -> Prop :=
  | new_tv_env_nil : forall st : stamp, new_tv_env nil st
  | new_tv_env_cons :
      forall (env : environment) (i : identifier) (ts : type_scheme)
        (st : stamp),
      new_tv_env env st ->
      new_tv_type_scheme ts st ->
      new_tv_env ( (*identifier*type_scheme*) (i, ts) :: env) st.
Hint Resolve new_tv_env_nil.
Hint Resolve new_tv_env_cons.
(*
Lemma  new_tv_cons_env : 
(i : identifier) (ts : type_scheme) (l0 : (list identifier*type_scheme)) 
(st : stamp)
(new_tv_env  (cons identifier*type_scheme (i,ts) l0) st)
  -> (new_tv_env l0 st).
Proof.
Intros i ts l0 st Hyp.
Inversion_clear Hyp.
Apply new_tv_env_intro; Intros.
Apply H;Simpl.
Apply in_second_componant_union_list_stamp; Auto.
Qed.



Lemma new_tv_cons_type_scheme : 
(i : identifier) (ts : type_scheme) (l0 : (list identifier*type_scheme)) (st : stamp)
(new_tv_env (cons identifier*type_scheme (i,ts) l0) st)
  ->  (new_tv_type_scheme ts st).
Induction ts; Auto.

(*Var st*)
Intros;Inversion_clear H.
Apply new_tv_ts_Var.
Apply H0.
Simpl.
Elim (bool_dec (in_list_stamp s (FV_env l0))); Intro eq1;Rewrite  eq1;Simpl;Auto.
Rewrite -> eq_stamp_reflexivity; Auto.

(*Arrow_ts*)
Intros.
Inversion_clear H1.
Apply new_tv_ts_Arrow.
Apply (H l0 st).
Apply new_tv_env_intro.
Simpl;Intros.
Apply H2.
Generalize (subset_union_ass3 (FV_type_scheme t) (FV_env l0)
             (FV_type_scheme t0)) .
Intro th_subset_union_ass3.
Inversion_clear th_subset_union_ass3.
Apply H3.
Apply in_first_componant_union_list_stamp; Auto.

Apply (H0 l0 st).
Apply new_tv_env_intro.
Simpl;Intros.
Apply H2.
Generalize (subset_union_ass2  (FV_type_scheme t) 
                               (FV_type_scheme t0) (FV_env l0)).
Intro th_subset_union_ass2.
Inversion_clear th_subset_union_ass2.
Apply H3.
Apply in_second_componant_union_list_stamp; Auto.
Qed.
par inversion
*)
(*******************************************************************)
(*********************************************************)
Inductive new_tv_subst : substitution -> stamp -> Prop :=
    new_tv_subst_intro :
      forall (st : stamp) (s : substitution),
      (forall x : stamp, in_list_stamp x (FV_subst s) = true -> lt_stamp x st) ->
      new_tv_subst s st.

Lemma new_tv_empty_subst : forall st' : stamp, new_tv_subst empty_subst st'.
Proof.
intro; apply new_tv_subst_intro; intros.
simpl in H; discriminate H.
Qed.
Hint Resolve new_tv_empty_subst.

Lemma new_tv_s_stamp :
 forall (st st' : stamp) (s : substitution),
 new_tv_subst s st ->
 lt_stamp st' st -> new_tv_type (apply_substitution s st') st.
intros; apply FV_new_tv_type.
intro.
elim (bool_dec (in_list_stamp st' (domain_of_substitution s))).
intros y H1.
generalize (FV_subset_range s st' y).
intro th_FV_subset_range.
inversion_clear th_FV_subset_range.
inversion_clear H.
apply H3.
unfold FV_subst in |- *.
apply in_second_componant_union_list_stamp; auto.

intro; rewrite is_not_in_domain_subst; auto.
simpl in |- *.
elim (stamp_dec x st'); intro eq1.
rewrite eq1; simpl in |- *; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; intro pb; discriminate pb.
Qed.
(*******************************************************)
Lemma new_tv_s_type :
 forall (st : stamp) (s : substitution) (t : type),
 new_tv_type t st ->
 new_tv_subst s st -> new_tv_type (extend_subst_type s t) st.

Proof.
simple induction t.
(*Nat*)
auto.
(*Var*)
do 2 intro; inversion_clear H; intros; simpl in |- *.
apply new_tv_s_stamp; auto.
(*Arrow*)
intros; simpl in |- *.
inversion_clear H1.
apply new_tv_Arrow; auto.
Qed.
(*******************************************************)
Lemma new_tv_ts_t2ts :
 forall (t : type) (st : stamp),
 new_tv_type t st -> new_tv_type_scheme (type_to_type_scheme t) st.
simple induction t; auto.
intros; inversion_clear H.
simpl in |- *; apply new_tv_ts_Var; auto.

intros; inversion_clear H1.
simpl in |- *; apply new_tv_ts_Arrow; auto.
Qed.

Lemma new_tv_s_type_scheme :
 forall (st : stamp) (s : substitution) (ts : type_scheme),
 new_tv_type_scheme ts st ->
 new_tv_subst s st -> new_tv_type_scheme (extend_subst_type_scheme s ts) st.
Proof.
simple induction ts; auto.
(*Var_ts*)
do 2 intro; inversion_clear H; intros; simpl in |- *.
apply new_tv_ts_t2ts.
change (new_tv_type (extend_subst_type s (Var s0)) st) in |- *.
apply new_tv_s_type; auto.

(*Arrow*)
simpl in |- *; intros; inversion_clear H1; auto.
Qed.

Hint Resolve new_tv_s_type_scheme.
 
(*****************************************************************)

Lemma new_tv_s_env :
 forall (st : stamp) (s : substitution) (env : environment),
 new_tv_env env st ->
 new_tv_subst s st -> new_tv_env (apply_subst_env env s) st.
simple induction env; auto.
intro a; elim a; intros i ts l ind_hyp hyp_new_tv_env_cons new_tv_s.
simpl in |- *; inversion_clear hyp_new_tv_env_cons.
apply new_tv_env_cons; auto.
Qed.

(************************************************************)
Lemma domain_app_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (domain_of_substitution ( (*stamp*type*) s1 ++ s2))
   (union_list_stamp (domain_of_substitution s1) (domain_of_substitution s2)).
intros s1 s2.
apply is_subset_intro; intro st; elim s1.
auto.

intro a; elim a; intros st1 t1.
do 2 intro.
elim (stamp_dec st st1); intro eq1.
(*st=st1*)
rewrite eq1; intro; simpl in |- *.
elim (bool_dec (in_list_stamp st1 (domain_of_substitution s2)));
 intros st1_in_s2; rewrite st1_in_s2; simpl in |- *.
apply
 (in_second_componant_union_list_stamp (domain_of_substitution l)
    (domain_of_substitution s2) st1 st1_in_s2).

rewrite eq_stamp_reflexivity; auto.

(*st<>st1*)
simpl in |- *; rewrite eq_stamp_diff; auto.
simpl in |- *; intro Hyp.
elim (bool_dec (in_list_stamp st1 (domain_of_substitution s2)));
 intros st1_in_s2; rewrite st1_in_s2; simpl in |- *.
auto.

rewrite eq_stamp_diff; auto.
Qed.
(**************************************************************************)

Lemma domain_apply_subst_list :
 forall s1 s2 : substitution,
 domain_of_substitution (apply_subst_list s1 s2) = domain_of_substitution s1.
simple induction s1; auto.

intros; simpl in |- *.
elim a; intros x t; simpl in |- *.
rewrite H; auto.
Qed.
(**************************************************************************)

Lemma domain_diff_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (domain_of_substitution (subst_diff s2 s1))
   (domain_of_substitution s2).
intros; apply is_subset_intro; intro st.
elim s2; auto.

intro a; elim a; intros x t l ind; simpl in |- *.
elim (bool_dec (mem_assoc x s1)); intro cond; rewrite cond; simpl in |- *.
elim (stamp_dec st x); intro eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; auto.
rewrite eq_stamp_diff; auto.

elim (stamp_dec st x); intro eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; auto.
rewrite eq_stamp_diff; auto.
Qed.
(**************************************************************************)


Lemma domain_compose_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (domain_of_substitution (compose_subst s1 s2))
   (union_list_stamp (domain_of_substitution s1) (domain_of_substitution s2)).
intros s1 s2; apply is_subset_intro; intro st.
unfold compose_subst in |- *; intro.
generalize (domain_app_subset (subst_diff s2 s1) (apply_subst_list s1 s2)).
rewrite domain_apply_subst_list; intro.
inversion_clear H0.
generalize (H1 st H); intro.
elim
 (in_union_list_stamp (domain_of_substitution (subst_diff s2 s1))
    (domain_of_substitution s1) st H0).
intro.
apply in_second_componant_union_list_stamp.
generalize (domain_diff_subset s1 s2).
intro.
inversion_clear H3; auto.

intro; apply in_first_componant_union_list_stamp; auto.
Qed.
(**************************************************************************)

Lemma range_diff_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (range_of_substitution (subst_diff s2 s1))
   (range_of_substitution s2).
Proof.
intros; apply is_subset_intro; intro st.
elim s2; auto.

intro a; elim a; intros x t l ind; simpl in |- *.
elim (bool_dec (mem_assoc x s1)); intro cond; rewrite cond; simpl in |- *.
intro; apply in_second_componant_union_list_stamp; auto.

intro.
elim
 (in_union_list_stamp (FV_type t) (range_of_substitution (subst_diff l s1))
    st H).
intro; apply in_first_componant_union_list_stamp; auto.

intro; apply in_second_componant_union_list_stamp; auto.
Qed.
(**************************************************************************)

Lemma range_app_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (range_of_substitution ( (*stamp*type*) s1 ++ s2))
   (union_list_stamp (range_of_substitution s1) (range_of_substitution s2)).
intros s1 s2; elim s1; auto.
intros; simpl in |- *; elim a; intros x t; simpl in |- *.
apply
 subset_trans
  with
    (l2 := union_list_stamp (FV_type t)
             (union_list_stamp (range_of_substitution l)
                (range_of_substitution s2))); auto.
apply is_subset_intro; intros.
elim
 (in_union_list_stamp (FV_type t)
    (range_of_substitution ( (*stamp*type*) l ++ s2)) st H0).
intro; apply in_first_componant_union_list_stamp; auto.

intro; inversion_clear H; apply in_second_componant_union_list_stamp; auto.
Qed.
(**************************************************************************)

Lemma range_apply_subst_list_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (range_of_substitution (apply_subst_list s1 s2))
   (union_list_stamp (range_of_substitution s1) (range_of_substitution s2)).
intros s1 s2; elim s1; auto.
intros; simpl in |- *; elim a; intros x t; simpl in |- *.
apply union_subset.
apply
 subset_trans
  with
    (l2 := union_list_stamp
             (union_list_stamp (FV_type t) (range_of_substitution s2))
             (range_of_substitution l)); auto.
apply
 subset_trans
  with (l2 := union_list_stamp (FV_type t) (range_of_substitution s2)).
apply FV_type_subset.

auto.

apply
 subset_trans
  with
    (l2 := union_list_stamp (range_of_substitution l)
             (range_of_substitution s2)); auto.
apply union_subset_union; auto.
Qed.


(************************************************************************)

Lemma range_compose_subset :
 forall s1 s2 : substitution,
 is_subset_list_stamp (range_of_substitution (compose_subst s1 s2))
   (union_list_stamp (range_of_substitution s1) (range_of_substitution s2)).
Proof.
intros s1 s2; unfold compose_subst in |- *.
generalize (range_app_subset (subst_diff s2 s1) (apply_subst_list s1 s2)).
intro.
apply
 subset_trans
  with
    (l2 := union_list_stamp (range_of_substitution (subst_diff s2 s1))
             (range_of_substitution (apply_subst_list s1 s2))).
apply range_app_subset.

apply union_subset.
apply subset_trans with (l2 := range_of_substitution s2); auto.
apply range_diff_subset.

apply range_apply_subst_list_subset.
Qed.


(************************************************************************)

Lemma new_tv_compose_subst :
 forall (s1 s2 : substitution) (st : stamp),
 new_tv_subst s1 st ->
 new_tv_subst s2 st -> new_tv_subst (compose_subst s1 s2) st.
Proof.
intros s1 s2 st new_s1 new_s2.
apply new_tv_subst_intro; intro x.
unfold FV_subst in |- *.
intro Hyp.
inversion_clear new_s1; inversion_clear new_s2.
unfold FV_subst in H; unfold FV_subst in H0.
elim
 (in_union_list_stamp (domain_of_substitution (compose_subst s1 s2))
    (range_of_substitution (compose_subst s1 s2)) x Hyp).
(*x in (domain_of_substitution (compose_subst s1 s2))*)
generalize (domain_compose_subset s1 s2).
intro domain_compose.
inversion_clear domain_compose.
intro x_in_domain.
generalize (H1 x x_in_domain).
intro x_in_union.
elim
 (in_union_list_stamp (domain_of_substitution s1) (domain_of_substitution s2)
    x x_in_union).
intro x_in_dom_s1.
apply H.
apply in_first_componant_union_list_stamp; auto.

intro x_in_dom_s2.
apply H0.
apply in_first_componant_union_list_stamp; auto.

(*x in (range_of_substitution (compose_subst s1 s2))*)
generalize (range_compose_subset s1 s2).
intro range_compose.
inversion_clear range_compose.
intro x_in_range.
generalize (H1 x x_in_range).
intro x_in_union.
elim
 (in_union_list_stamp (range_of_substitution s1) (range_of_substitution s2) x
    x_in_union).
intro x_in_range_s1.
apply H.
apply in_second_componant_union_list_stamp; auto.

intro x_in_range_s2.
apply H0.
apply in_second_componant_union_list_stamp; auto.
Qed.

(*************************************************************)
Lemma new_tv_subst_trans :
 forall (s : substitution) (x1 x2 : stamp),
 new_tv_subst s x1 -> le_stamp x1 x2 -> new_tv_subst s x2.
Proof.
intros; apply new_tv_subst_intro; intros.
inversion H.
apply lt_le_stamp_trans with (st2 := x1); auto.
Qed.
(*************************************************************)


Definition add_subst (s : substitution) (x : stamp) 
  (t : type) : substitution :=  (*stamp*type*) (x, t) :: s.


Lemma add_subst_rewrite_for_modified_stamp :
 forall (s : substitution) (st : stamp) (t : type),
 apply_substitution (add_subst s st t) st = t.
intros; unfold add_subst in |- *.
unfold apply_substitution in |- *; simpl in |- *;
 rewrite (eq_stamp_reflexivity st); auto.
Qed.

Lemma add_subst_rewrite_for_unmodified_stamp :
 forall (s : substitution) (st st' : stamp) (t : type),
 st' <> st ->
 apply_substitution (add_subst s st t) st' = apply_substitution s st'.
intros; unfold add_subst in |- *.
unfold apply_substitution in |- *; simpl in |- *;
 rewrite (eq_stamp_diff st' st); auto.
Qed.

Lemma add_subst_new_tv_type :
 forall (s : substitution) (st : stamp) (t t' : type),
 new_tv_type t st ->
 extend_subst_type (add_subst s st t') t = extend_subst_type s t.
Proof.
simple induction t.
(*Nat*)
auto.
(*Var*)
simpl in |- *; intros.
inversion_clear H.
apply add_subst_rewrite_for_unmodified_stamp; auto.
(*Arrow*)
simpl in |- *; intros.
inversion_clear H1.
rewrite H; auto.
rewrite H0; auto.
Qed.

Lemma add_subst_new_tv_type_scheme :
 forall (ts : type_scheme) (s : substitution) (st : stamp) (t' : type),
 new_tv_type_scheme ts st ->
 extend_subst_type_scheme (add_subst s st t') ts =
 extend_subst_type_scheme s ts.
simple induction ts; auto.
(*Var*)
intros; simpl in |- *.
inversion_clear H.
change
  (type_to_type_scheme (extend_subst_type (add_subst s0 st t') (Var s)) =
   type_to_type_scheme (extend_subst_type s0 (Var s))) 
 in |- *.
rewrite add_subst_new_tv_type; auto.
(*Arrow*)
simpl in |- *; intros.
inversion_clear H1.
rewrite H; auto.
rewrite H0; auto.
Qed.


Lemma apply_add_subst_env :
 forall (env : environment) (s : substitution) (st : stamp) (t : type),
 new_tv_env env st ->
 apply_subst_env env (add_subst s st t) = apply_subst_env env s.
simple induction env; auto.

intro a; elim a; intros x ts l ind_hyp s st t hyp_new_tv_env_cons.
simpl in |- *; inversion_clear hyp_new_tv_env_cons.
rewrite ind_hyp; auto.
rewrite add_subst_new_tv_type_scheme; auto.
Qed.


Lemma add_subst_add_env :
 forall (env : environment) (s : substitution) (i : identifier) 
   (st : stamp) (t : type),
 new_tv_env env st ->
 apply_subst_env (add_environment env i (Var_ts st)) (add_subst s st t) =
 add_environment (apply_subst_env env s) i (type_to_type_scheme t).
intros.
change
  (apply_subst_env (add_environment env i (type_to_type_scheme (Var st)))
     (add_subst s st t) =
   add_environment (apply_subst_env env s) i (type_to_type_scheme t)) 
 in |- *.
rewrite subst_add_type; simpl in |- *;
 rewrite add_subst_rewrite_for_modified_stamp.
rewrite apply_add_subst_env; auto.
Qed.


Lemma new_tv_compose_subst_type :
 forall (s s1 s2 : substitution) (st : stamp) (t : type),
 (forall x : stamp,
  lt_stamp x st ->
  apply_substitution s x = extend_subst_type s2 (apply_substitution s1 x)) ->
 new_tv_type t st ->
 extend_subst_type s t = extend_subst_type s2 (extend_subst_type s1 t).
Proof.
simple induction t.
(*Nat*)
auto.
(*Var*)
elim st; intro n; intros; simpl in |- *.
apply H.
inversion_clear H0; auto.
(*Arrow t t0*)
intros; simpl in |- *.
inversion_clear H2.
rewrite H; auto.
rewrite H0; auto.
Qed.

Lemma new_tv_compose_subst_type_scheme :
 forall (s s1 s2 : substitution) (st : stamp) (ts : type_scheme),
 (forall x : stamp,
  lt_stamp x st ->
  apply_substitution s x = extend_subst_type s2 (apply_substitution s1 x)) ->
 new_tv_type_scheme ts st ->
 extend_subst_type_scheme s ts =
 extend_subst_type_scheme s2 (extend_subst_type_scheme s1 ts).
Proof.
simple induction ts; auto.
(*Var*)
elim st; intros; simpl in |- *.
rewrite H; auto.
rewrite type_to_type_scheme_commutes_with_subst; auto.

inversion_clear H0; auto.

(*Arrow*)
intros; simpl in |- *.
inversion_clear H2.
rewrite H; auto.
rewrite H0; auto.
Qed.

(*****************************************************************)

(************************************************************************)

Lemma new_tv_compose_subst_env :
 forall (s s1 s2 : substitution) (st : stamp) (env : environment),
 (forall x : stamp,
  lt_stamp x st ->
  apply_substitution s x = extend_subst_type s2 (apply_substitution s1 x)) ->
 new_tv_env env st ->
 apply_subst_env env s = apply_subst_env (apply_subst_env env s1) s2.
Proof.
simple induction env; auto.

intro a; elim a; intros i ts; intros; simpl in |- *.
inversion_clear H1.
rewrite <- (new_tv_compose_subst_type_scheme s s1 s2 st ts); auto.
rewrite H; auto.
Qed.


(*******************************************************************)

(*


Lemma add_subst_add_env :  
(env : environment) (s : substitution) (i : identifier)(st : stamp)(t : type)
 (new_tv_env env st) ->
   (apply_subst_env (add_environment env i (Var st)) (add_subst s st t)) =
      (add_environment  (apply_subst_env env s) i t).
Intros;Rewrite -> subst_add_type.
Simpl;Rewrite -> add_subst_rewrite_for_modified_stamp.
Rewrite -> apply_add_subst_env;Auto.
Qed.
*)

(*****************************************************************)
Lemma new_tv_ts_trans_le :
 forall (ts : type_scheme) (st1 st2 : stamp),
 new_tv_type_scheme ts st1 -> le_stamp st1 st2 -> new_tv_type_scheme ts st2.
simple induction ts; auto.
(*Var_ts*)
intros; inversion_clear H.
apply new_tv_ts_Var; apply lt_le_stamp_trans with (st2 := st1); auto.

(*Arrow_ts*)
intros; inversion_clear H1.
apply new_tv_ts_Arrow.
apply (H st1 st2 H3 H2).

apply (H0 st1 st2 H4 H2).
Qed.
Hint Resolve new_tv_ts_trans_le.
(*used by Eauto in the next lemma new_tv_env_trans_le*)

Lemma new_tv_env_trans_le :
 forall (env : environment) (st1 st2 : stamp),
 new_tv_env env st1 -> le_stamp st1 st2 -> new_tv_env env st2.
Proof.
simple induction env; auto.
intros; inversion_clear H0.
apply new_tv_env_cons; eauto.
Qed.

Lemma new_tv_type_trans_le :
 forall (t : type) (x1 x2 : stamp),
 new_tv_type t x1 -> le_stamp x1 x2 -> new_tv_type t x2.
Proof.
intros.
apply FV_new_tv_type; intros.
apply lt_le_stamp_trans with (st2 := x1); auto.
apply (new_tv_type_FV x1 t H); auto.
Qed.



(***********************************************************)
Lemma new_tv_mgu :
 forall (t1 t2 : type) (st : stamp) (U : substitution),
 new_tv_type t1 st ->
 new_tv_type t2 st -> unify (t1, t2) = Some_unifier U -> new_tv_subst U st.
Proof.
intros; apply new_tv_subst_intro; intros.
elim (in_union_list_stamp (FV_type t1) (FV_type t2) x).
intros; apply (new_tv_type_FV st t1 H); auto.

intro; apply (new_tv_type_FV st t2 H0); auto.

apply (member_FV_mgu t1 t2 U x); auto.
Qed.

(***********************************************************)
(*Lemma FV_new_tv_type_scheme :
(st : stamp) (ts : type_scheme) 
( (x:stamp) (in_list_stamp x (FV_type_scheme ts))=true -> (lt_stamp x st)) ->
           (new_tv_type_scheme ts st).
Proof.
Induction ts;Auto.
(*Var*)
Intros;Apply new_tv_ts_Var.
Apply H.
Simpl;Rewrite  eq_stamp_reflexivity;Auto.
(*Arrow*)
Simpl;Intros.
Apply new_tv_ts_Arrow.
Apply H;Intros.
Apply H1.
Apply in_first_componant_union_list_stamp;Auto.
Apply H0;Intros.
Apply H1.
Apply in_second_componant_union_list_stamp;Auto.
Qed.
*)

(************************************************************************)
Lemma new_tv_gen_type_aux :
 forall (t : type) (env : environment) (st : stamp) (l : list stamp),
 new_tv_type t st ->
 new_tv_env env st -> new_tv_type_scheme (fst (gen_aux t env l)) st.
Proof.
simple induction t; auto.
(*Var*)
intros.
inversion_clear H.
elim (bool_dec (in_list_stamp (Stamp n) (FV_env env))); intro eq_in_list;
 simpl in |- *; rewrite eq_in_list; simpl in |- *.
auto.

elim (index l (Stamp n)); simpl in |- *; auto.

(*Arrow*)
intros.
inversion_clear H1.
rewrite fst_gen_aux_arrow_rewrite.
apply new_tv_ts_Arrow; auto.
Qed.

Lemma new_tv_gen_type :
 forall (t : type) (env : environment) (st : stamp),
 new_tv_type t st ->
 new_tv_env env st -> new_tv_type_scheme (gen_type t env) st.
Proof.
intros; simpl in |- *.
unfold gen_type in |- *.
apply new_tv_gen_type_aux; auto.
Qed.

(************************************************************************)
Lemma new_tv_env_implies_new_tv_ts :
 forall (env : environment) (ts : type_scheme) (st : stamp) (i : identifier),
 assoc_ident_in_env i env = Ident_in_env ts ->
 new_tv_env env st -> new_tv_type_scheme ts st.
simple induction env.
simpl in |- *; intros ts st i pb; discriminate pb.

intro a; elim a; intros x ts l ind_hyp TS st i; simpl in |- *.
elim (identifier_dec i x); intro eq1.
rewrite eq1; rewrite eq_identifier_reflexivity; simpl in |- *.
intro ts_TS; inversion_clear ts_TS; intro Hyp; inversion_clear Hyp.
auto.

rewrite (eq_identifier_diff i x eq1); simpl in |- *; intros;
 inversion_clear H0.
apply (ind_hyp TS st i H H1).
Qed.


Lemma new_tv_add_env :
 forall (env : environment) (st1 : stamp) (i : identifier) (ts : type_scheme),
 new_tv_env env st1 ->
 new_tv_type_scheme ts st1 -> new_tv_env (add_environment env i ts) st1.
unfold add_environment in |- *.
auto.
Qed.

Lemma new_tv_ts_new_def :
 forall (ts : type_scheme) (st : stamp),
 new_tv_type_scheme ts st ->
 forall x : stamp,
 in_list_stamp x (FV_type_scheme ts) = true -> lt_stamp x st.
simple induction ts; auto.
simpl in |- *; intros; discriminate H0.

simpl in |- *; do 4 intro.
elim (stamp_dec x s); intros dec.
rewrite dec; rewrite eq_stamp_reflexivity; simpl in |- *.
inversion_clear H; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; intros pb; discriminate pb.

simpl in |- *; intros; discriminate H0.

intros; inversion_clear H1.
simpl in H2.
elim (in_union_list_stamp (FV_type_scheme t) (FV_type_scheme t0) x H2); auto.
Qed.


Lemma new_tv_env_new_def :
 forall (env : environment) (st : stamp),
 new_tv_env env st ->
 forall x : stamp, in_list_stamp x (FV_env env) = true -> lt_stamp x st.
simple induction env.
simpl in |- *; intros; discriminate H0.

intro a; elim a; intros x ts l ind_hyp st new_tv_env_hyp;
 inversion_clear new_tv_env_hyp; simpl in |- *; intros.
elim (in_union_list_stamp (FV_type_scheme ts) (FV_env l) x0 H1); auto.
intro; apply (new_tv_ts_new_def ts st H0 x0 H2).
Qed.



Lemma new_tv_env_plus :
 forall (env : environment) (m n : nat),
 new_tv_env env (Stamp m) ->
 in_list_stamp (Stamp (m + n)) (FV_env env) = false.
intros.
generalize (new_tv_env_new_def env (Stamp m) H); intro Hyp_deriv.
elim (bool_dec (in_list_stamp (Stamp (m + n)) (FV_env env))); auto.
intro y.
generalize (Hyp_deriv (Stamp (m + n)) y); intro.
simpl in H0.
generalize (lt_asym (m + n) m H0); intro.
absurd (m + n < m); auto with *.
Qed.

(***********************************************************************)
Lemma new_tv_max :
 forall ts : type_scheme,
 new_tv_type_scheme ts (succ_stamp (max_list_stamp (FV_type_scheme ts))).
simple induction ts; auto.
(*var*)
simpl in |- *; intro st; apply new_tv_ts_Var.
case st; intro n; simpl in |- *.
rewrite <- max_O; auto.
(*arrow*)
intros; apply new_tv_ts_Arrow; simpl in |- *;
 rewrite max_list_stamp_union_list.
apply
 new_tv_ts_trans_le
  with (st1 := succ_stamp (max_list_stamp (FV_type_scheme t))); 
 auto.

apply le_stamp_succ_succ; auto.

apply
 new_tv_ts_trans_le
  with (st1 := succ_stamp (max_list_stamp (FV_type_scheme t0))); 
 auto.

apply le_stamp_succ_succ; auto.
Qed.
Hint Resolve new_tv_max.

Lemma find_new_tv_type_scheme2 :
 forall ts : type_scheme, {st : stamp | new_tv_type_scheme ts st}.
intro ts.
exists (succ_stamp (max_list_stamp (FV_type_scheme ts))).
apply
 new_tv_ts_trans_le
  with (st1 := succ_stamp (max_list_stamp (FV_type_scheme ts))); 
 auto.
Qed.