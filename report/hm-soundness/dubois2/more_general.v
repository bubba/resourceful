(* Author : Catherine Dubois*)

Require Import Le.
Require Import tools_bool.
Require Import List.
Require Import generic_DB.
Require Import subset.
Require Import langs.
Require Import FV.
Require Import tools.
Require Import max.
Require Import disjoints.
Require Import subst.
Require Import env_poly.
Require Import DB_stable_gen_instance.
Require Import DB_gen_stable.
Require Import type_system.
Require Import tools_more_general.
Require Import type_scheme.

(***********************************************************************)
Inductive more_general : type_scheme -> type_scheme -> Prop :=
    more_general_intro :
      forall ts1 ts2 : type_scheme,
      (forall t : type, is_gen_instance t ts2 -> is_gen_instance t ts1) ->
      more_general ts1 ts2.


(***********************************************************************)

Lemma more_general_refl : forall ts : type_scheme, more_general ts ts.
intro; apply more_general_intro; auto.
Qed.
Hint Resolve more_general_refl.

(***********************************************************************)
Fixpoint make_constant_gen_subst (n : nat) (t : type) {struct n} :
 list type :=
  match n with
  | O => nil (A:=type)
  | S p => t :: make_constant_gen_subst p t
  end.

(*********************************************************************)
Fixpoint find_generic_instance (ts : type_scheme) (t : type) {struct ts} :
 type :=
  match ts with
  | Nat_ts => Nat
  | Var_ts st => Var st
  | Gen_var st => t
  | Arrow_ts ts1 ts2 =>
      Arrow (find_generic_instance ts1 t) (find_generic_instance ts2 t)
  end.
(***********************************************************************)
Lemma length_make_constant_gen_subst :
 forall (n : nat) (t : type), length (make_constant_gen_subst n t) = n.
simple induction n; auto.
intros; simpl in |- *; rewrite H; auto.
Qed.
(*********************************************************************)
Lemma nth_succeeds :
 forall (sg : list type) (n : nat),
 S n <= length sg -> {t : type | nth n sg = Nth_in t}.
simple induction sg.
simpl in |- *; intros.
absurd (S n <= 0); auto with *.

intros t l hyp_ind n; elim n.
simpl in |- *; exists t; auto.

intros; simpl in H0.
simpl in |- *; apply hyp_ind.
apply le_S_n; auto.

Qed.
(*********************************************************************)

Lemma nth_make_constant_gen_subst3 :
 forall (p n : nat) (t : type),
 S n <= p -> nth n (make_constant_gen_subst p t) = Nth_in t.
simple induction p.
intros n t hyp_le; inversion hyp_le.

simpl in |- *; intros n ind_hyp n0 t.
case n0; auto with *.
Qed.
(*********************************************************************)
Lemma apply_subst_gen_make_constant_gen_subst :
 forall (ts : type_scheme) (t : type) (p : nat),
 max_gen_vars ts <= p ->
 apply_subst_gen (make_constant_gen_subst p t) ts =
 Some_subst_gen (find_generic_instance ts t).
simple induction ts; auto.
(*Gen*)
intro st; elim st; intros n t p le_hyp.
unfold max_gen_vars in |- *; unfold apply_subst_gen in |- *.
simpl in le_hyp.
rewrite (nth_make_constant_gen_subst3 p n t le_hyp); auto.
(*Arrow_ts*)
intros ts1 ind_hyp_ts1 ts2 ind_hyp_ts2 t p le_hyp; simpl in |- *.
rewrite (ind_hyp_ts1 t p).
rewrite (ind_hyp_ts2 t p).
auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.
Hint Resolve apply_subst_gen_make_constant_gen_subst.
(***********************************************************************)

Lemma find_generic_instance_ts_is_gen_instance_ts :
 forall (ts : type_scheme) (t : type),
 is_gen_instance (find_generic_instance ts t) ts.
intros ts t.
apply gen_instance_intro.
exists (make_constant_gen_subst (max_gen_vars ts) t).
auto.
Qed.
Hint Resolve find_generic_instance_ts_is_gen_instance_ts.

(***********************************************************************)

Lemma Nat_is_not_gen_instance_of_arrow :
 forall ts1 ts2 : type_scheme, ~ is_gen_instance Nat (Arrow_ts ts1 ts2).
intros; unfold not in |- *; intro.
inversion_clear H.
elim H0; clear H0.
intros sg H0.
elim (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 Nat sg H0).
intro x; elim x; intros t1 t2 y.
elim y; intros; elim H1; intros; discriminate H3.
Qed.
Hint Resolve Nat_is_not_gen_instance_of_arrow.

Lemma Var_is_not_gen_instance_of_arrow :
 forall (ts1 ts2 : type_scheme) (st : stamp),
 ~ is_gen_instance (Var st) (Arrow_ts ts1 ts2).
intros; unfold not in |- *; intro.
inversion_clear H.
elim H0; clear H0.
intros sg H0.
elim (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 (Var st) sg H0).
intro x; elim x; intros t1 t2 y.
elim y; intros; elim H1; intros; discriminate H3.
Qed.
Hint Resolve Var_is_not_gen_instance_of_arrow.

(***********************************************************************)
Lemma arrow_ts_more_general_than_arrow :
 forall ts ts1 ts2 : type_scheme,
 (forall t : type,
  is_gen_instance t ts -> is_gen_instance t (Arrow_ts ts1 ts2)) ->
 {ts3_ts4 : type_scheme * type_scheme |
 ts = Arrow_ts (fst ts3_ts4) (snd ts3_ts4)}.
intros ts ts1 ts2; case ts.
(*Nat*)
intro Hyp.
cut (is_gen_instance (find_generic_instance Nat_ts Nat) Nat_ts); auto.
intro Hyp_cut1.
cut (is_gen_instance (find_generic_instance Nat_ts Nat) (Arrow_ts ts1 ts2)).
simpl in |- *; intro Hyp_cut2.
absurd (is_gen_instance Nat (Arrow_ts ts1 ts2)); auto.

apply Hyp; auto.

(*Var*)
intros st Hyp.
cut (is_gen_instance (find_generic_instance (Var_ts st) Nat) (Var_ts st));
 auto.
intro Hyp_cut1.
cut
 (is_gen_instance (find_generic_instance (Var_ts st) Nat) (Arrow_ts ts1 ts2)).
simpl in |- *; intro Hyp_cut2.
absurd (is_gen_instance (Var st) (Arrow_ts ts1 ts2)); auto.

apply Hyp; auto.

(*Gen*)
intros st Hyp.
cut (is_gen_instance (find_generic_instance (Gen_var st) Nat) (Gen_var st));
 auto.
intro Hyp_cut1.
cut
 (is_gen_instance (find_generic_instance (Gen_var st) Nat) (Arrow_ts ts1 ts2)).
simpl in |- *; intro Hyp_cut2.
absurd (is_gen_instance Nat (Arrow_ts ts1 ts2)); auto.

apply Hyp; auto.

(*Arrow*)
intros ts3 ts4 Hyp.
exists (ts3, ts4); auto.
Qed.

(***************************************************************************)

Lemma apply_subst_gen_succeeds :
 forall (ts : type_scheme) (sg : list type),
 max_gen_vars ts <= length sg ->
 {t : type | apply_subst_gen sg ts = Some_subst_gen t}.
Proof.
simple induction ts.
exists Nat; auto.

intro st; exists (Var st); auto.

intro st; elim st; intros n sg le_hyp.
simpl in le_hyp; simpl in |- *.
elim (nth_succeeds sg n le_hyp).
intros t def_t.
rewrite def_t; exists t; auto.

intros ts1 ind_hyp1 ts2 ind_hyp2 sg hyp_le_arrow.
simpl in hyp_le_arrow.
elim (ind_hyp1 sg).
intros t1 rwt1.
elim (ind_hyp2 sg).
intros t2 rwt2.
simpl in |- *; rewrite rwt1; rewrite rwt2.
exists (Arrow t1 t2); auto.

apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.

apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.
(***************************************************************************)



Lemma apply_gen_subst_sg_app :
 forall (ts : type_scheme) (sg l : list type),
 max_gen_vars ts <= length sg ->
 apply_subst_gen (sg ++ l) ts = apply_subst_gen sg ts.
simple induction ts; auto.
(*Gen_var*)
intro s; elim s; intros n sg l le_hyp; simpl in |- *.
rewrite (nth_app sg l n); auto.

(*Arrow*)
simpl in |- *; intros ts1 ind1 ts2 ind2 sg l le_hyp.
rewrite (ind1 sg l).
rewrite (ind2 sg l); auto.

apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.
(***************************************************************************)


Lemma more_general_arrow_inversion_left :
 forall ts1 ts2 sigma1 sigma2 : type_scheme,
 more_general (Arrow_ts ts1 ts2) (Arrow_ts sigma1 sigma2) ->
 more_general ts1 sigma1.
Proof.
intros ts1 ts2 sigma1 sigma2 Hyp.
inversion_clear Hyp.
apply more_general_intro.
intros t t_gen_instance_of_sigma1.
inversion_clear t_gen_instance_of_sigma1.
elim H0; clear H0; intros sg sg_sigma1.
elim
 (apply_subst_gen_succeeds sigma2
    (sg ++ make_constant_gen_subst (max_gen_vars sigma2) Nat)).
intros T sg_app_sigma2.
cut (is_gen_instance (Arrow t T) (Arrow_ts ts1 ts2)).
intro Hyp_cut2; inversion_clear Hyp_cut2.
elim H0; clear H0.
intros sg' sg'_Arrow.
apply gen_instance_intro.
exists sg'.
elim
 (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 (Arrow t T) sg' sg'_Arrow).
intro x; elim x; intros t1 t2 y.
elim y; clear y; intros; elim H1; clear H1; intros.
inversion_clear H2; auto.
(*(is_gen_instance (Arrow t T) (Arrow_ts ts1 ts2))*)
apply H.
(*(is_gen_instance (Arrow t T) (Arrow_ts sigma1 sigma2))*)
apply gen_instance_intro.
exists (sg ++ make_constant_gen_subst (max_gen_vars sigma2) Nat).
(*   (apply_subst_gen
     (app type sg (make_constant_gen_subst (max_gen_vars sigma2) Nat))
     (Arrow_ts sigma1 sigma2))=(Some_subst_gen (Arrow t T))*)
simpl in |- *.
rewrite
 (apply_gen_subst_sg_app sigma1 sg
    (make_constant_gen_subst (max_gen_vars sigma2) Nat))
 ; eauto.
rewrite sg_sigma1; rewrite sg_app_sigma2; auto.
(*   (le (max_gen_vars sigma2)
     (length type
       (app type sg (make_constant_gen_subst (max_gen_vars sigma2) Nat))))*)
rewrite length_app; rewrite length_make_constant_gen_subst; auto with *.
Qed.
(***********************************************************************)
Lemma more_general_arrow_inversion_right :
 forall ts1 ts2 sigma1 sigma2 : type_scheme,
 more_general (Arrow_ts ts1 ts2) (Arrow_ts sigma1 sigma2) ->
 more_general ts2 sigma2.
Proof.
intros ts1 ts2 sigma1 sigma2 Hyp.
inversion_clear Hyp.
apply more_general_intro.
intros t t_gen_instance_of_sigma2.
inversion_clear t_gen_instance_of_sigma2.
elim H0; clear H0; intros sg sg_sigma2.
elim
 (apply_subst_gen_succeeds sigma1
    (sg ++ make_constant_gen_subst (max_gen_vars sigma1) Nat)).
intros T sg_app_sigma1.
cut (is_gen_instance (Arrow T t) (Arrow_ts ts1 ts2)).
intro Hyp_cut2; inversion_clear Hyp_cut2.
elim H0; clear H0.
intros sg' sg'_Arrow.
apply gen_instance_intro.
exists sg'.
elim
 (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 (Arrow T t) sg' sg'_Arrow).
intro x; elim x; intros t1 t2 y.
elim y; clear y; intros; elim H1; clear H1; intros.
inversion_clear H2; auto.
(*(is_gen_instance (Arrow T t) (Arrow_ts ts1 ts2))*)
apply H.
(*(is_gen_instance (Arrow T t) (Arrow_ts sigma1 sigma2))*)
apply gen_instance_intro.
exists (sg ++ make_constant_gen_subst (max_gen_vars sigma1) Nat).
(*   (apply_subst_gen
     (app type sg (make_constant_gen_subst (max_gen_vars sigma1) Nat))
     (Arrow_ts sigma1 sigma2))=(Some_subst_gen (Arrow T t))*)
simpl in |- *.
rewrite
 (apply_gen_subst_sg_app sigma2 sg
    (make_constant_gen_subst (max_gen_vars sigma1) Nat))
 ; eauto.
rewrite sg_sigma2; rewrite sg_app_sigma1; auto.
(*   (le (max_gen_vars sigma1)
     (length type
       (app type sg (make_constant_gen_subst (max_gen_vars sigma1) Nat))))*)
rewrite length_app; rewrite length_make_constant_gen_subst; auto with *.
Qed.
(***********************************************************************)

Lemma var_ts_more_general_than_var_ts2 :
 forall (ts : type_scheme) (st : stamp),
 more_general (Var_ts st) ts -> ts = Var_ts st.
Proof.
intros ts st Hyp.
inversion Hyp.
cut (is_gen_instance (find_generic_instance ts Nat) ts); auto.
intro Hyp_cut1.
cut (is_gen_instance (find_generic_instance ts Nat) (Var_ts st)).
intro Hyp_cut2; inversion_clear Hyp_cut2; elim H2; intro x.
case ts; simpl in |- *.
(**)intro x_gen_subst2; discriminate x_gen_subst2.
(**)intros st1 x_gen_subst2.
inversion x_gen_subst2; auto.
(**)intros st1 x_gen_subst2; discriminate x_gen_subst2.
(**)intros sigma1 sigma2 x_gen_subst2; discriminate x_gen_subst2.

apply H; auto. 
Qed.

(**************************************************************************)
Inductive more_general_env : environment -> environment -> Prop :=
  | more_general_env_nil : more_general_env nil nil
  | more_general_env_cons :
      forall (env1 env2 : environment) (i : identifier)
        (ts1 ts2 : type_scheme),
      more_general_env env1 env2 ->
      more_general ts1 ts2 ->
      more_general_env ((i, ts1) :: env1) ((i, ts2) :: env2).
Hint Resolve more_general_env_nil.
Hint Resolve more_general_env_cons.

Lemma more_general_env_refl :
 forall env : environment, more_general_env env env.
simple induction env; auto.
intros; elim a; auto.
Qed.
Hint Resolve more_general_env_refl.
 

Lemma more_general_env_add_ts :
 forall (env1 env2 : environment) (i : identifier) (ts1 ts2 : type_scheme),
 more_general_env env1 env2 ->
 more_general ts1 ts2 ->
 more_general_env (add_environment env1 i ts1) (add_environment env2 i ts2).
intros; unfold add_environment in |- *; auto.
Qed.
(************************************************************************)

Lemma FV_more_general :
 forall ts1 ts2 : type_scheme,
 more_general ts1 ts2 ->
 is_subset_list_stamp (FV_type_scheme ts1) (FV_type_scheme ts2).
Proof.
simple induction ts1; auto.

(*Var_ts st*)
intros; elim (var_ts_more_general_than_var_ts2 ts2 s); auto.

(*Arrow_ts*)
intros sigma1 ind1 sigma2 ind2 sigma more_gen_arrow.
inversion more_gen_arrow.
elim (arrow_ts_more_general_than_arrow sigma sigma1 sigma2); auto.
intro x; elim x; clear x; intros sigma3 sigma4 sigma_rwt.
rewrite sigma_rwt.
simpl in |- *; apply union_subset_union.
apply ind1; auto.
(*(more_general sigma1 sigma3)*)
apply (more_general_arrow_inversion_left sigma1 sigma2 sigma3 sigma4).
simpl in sigma_rwt; rewrite <- sigma_rwt; auto.

apply ind2; auto.
(*(more_general sigma2 sigma4)*)
apply (more_general_arrow_inversion_right sigma1 sigma2 sigma3 sigma4).
simpl in sigma_rwt; rewrite <- sigma_rwt; auto.
Qed.
Hint Resolve FV_more_general.

(************************************************************************)
Lemma FV_more_general_env :
 forall env1 env2 : environment,
 more_general_env env1 env2 ->
 is_subset_list_stamp (FV_env env1) (FV_env env2).

do 2 intro.
simple induction 1.
auto.

intros; simpl in |- *; apply union_subset_union; auto.
Qed.
(************************************************************************)

Lemma subset_inv1 :
 forall (l1 l2 : list stamp) (st : stamp),
 is_subset_list_stamp l1 l2 ->
 in_list_stamp st l1 = true -> in_list_stamp st l2 = true.
intros.
inversion_clear H; auto.
Qed.


Lemma more_general_gen_type_aux :
 forall (env1 env2 : environment) (tau t : type) (phi : substitution)
   (gv_env2 gv_env1 L P : list stamp) (sg : list type),
 more_general_env env1 env2 ->
 are_disjoints (FV_env env2) gv_env2 ->
 are_disjoints (FV_env env1) gv_env1 ->
 apply_subst_gen sg (fst (gen_aux tau env2 gv_env2)) = Some_subst_gen t ->
 is_prefixe_free2 (FV_env env2) (snd (gen_aux tau env2 gv_env2)) L ->
 product_list L sg = Some_product phi ->
 is_prefixe_free2 (FV_env env1) (snd (gen_aux tau env1 gv_env1)) P ->
 apply_subst_gen (map_extend_subst_type (type_from_stamp_list P) phi)
   (fst (gen_aux tau env1 gv_env1)) = Some_subst_gen t.
simple induction tau.
do 7 intro; simpl in |- *; intro more_gen_hyp; intros.
injection H1; intros; rewrite H5; auto.

do 8 intro; intros more_gen_hyp disjoint1 disjoint2.
simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env1))); intro y; rewrite y;
 simpl in |- *.
(* y : (in_list_stamp s (FV_env env1))=true*)
rewrite
 (subset_inv1 (FV_env env1) (FV_env env2) s
    (FV_more_general_env env1 env2 more_gen_hyp) y)
 ; auto.
(* y : (in_list_stamp s (FV_env env1))=false*)
elim (index_answer_dec (index gv_env1 s)).
(**{n:nat | (index gv_env1 s)=(Index_in n)}*)
intro s_in_l; elim s_in_l; intros n0; clear s_in_l; intro s_in_l;
 rewrite s_in_l; simpl in |- *.
do 4 intro.
inversion_clear H2.
elim H3; clear H3; intros P2 Hyp.
elim Hyp; clear Hyp; intros Def_P disjoint3; rewrite Def_P.
rewrite (type_from_stamp_list_app gv_env1 P2).
rewrite
 (map_extend_app phi (type_from_stamp_list gv_env1) (type_from_stamp_list P2))
 .
rewrite
 (nth_app (map_extend_subst_type (type_from_stamp_list gv_env1) phi)
    (map_extend_subst_type (type_from_stamp_list P2) phi) n0)
 .
rewrite (nth_map phi (type_from_stamp_list gv_env1) n0 (Var s)).
rewrite (gen_subst_to_subst_aux_4 env2 (Var s) t gv_env2 L sg phi); auto.

apply index_nth; auto.

rewrite length_map.
rewrite length_type_from_stamp_list.
apply (index_lt gv_env1 s n0 s_in_l).

(** y0 : (index gv_env1 s)=Stamp_not_in*)
intro y0; rewrite y0.
do 4 intro.
inversion_clear H2.
elim H3; clear H3; intros P2 Hyp.
elim Hyp; clear Hyp; intros Def_P disjoint3; rewrite Def_P.
simpl in |- *.
rewrite (type_from_stamp_list_app (gv_env1 ++ s :: nil) P2).
rewrite
 (map_extend_app phi (type_from_stamp_list (gv_env1 ++ s :: nil))
    (type_from_stamp_list P2)).
rewrite
 (nth_app
    (map_extend_subst_type (type_from_stamp_list (gv_env1 ++ s :: nil)) phi)
    (map_extend_subst_type (type_from_stamp_list P2) phi) 
    (length gv_env1)).
rewrite
 (nth_map phi (type_from_stamp_list (gv_env1 ++ s :: nil)) 
    (length gv_env1) (Var s)).
rewrite (gen_subst_to_subst_aux_4 env2 (Var s) t gv_env2 L sg phi); auto.

rewrite type_from_stamp_list_app; simpl in |- *.
rewrite <- length_type_from_stamp_list; auto.

rewrite length_map2; rewrite length_app_cons; auto.


(*arrow*)
do 11 intro; intros more_gen_hyp disjoint1 disjoint2.
rewrite fst_gen_aux_arrow_rewrite; intro.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (fst (gen_aux t env2 gv_env2))
    (fst (gen_aux t0 env2 (snd (gen_aux t env2 gv_env2)))) t1 sg H1).
intro x; elim x; clear x; do 2 intro; clear H1.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro rwt_t1; rewrite rwt_t1.
rewrite snd_gen_aux_arrow_rewrite; do 2 intro.
rewrite snd_gen_aux_arrow_rewrite.
rewrite fst_gen_aux_arrow_rewrite; intro.
simpl in |- *.
rewrite (H a phi gv_env2 gv_env1 L P sg); eauto.
rewrite
 (H0 b phi (snd (gen_aux t env2 gv_env2)) (snd (gen_aux t env1 gv_env1)) L P
    sg); auto.
Qed.

(********************************************************************)
Lemma more_general_gen_type :
 forall (env1 env2 : environment) (t : type),
 more_general_env env1 env2 ->
 more_general (gen_type t env1) (gen_type t env2).
Proof.
intros; apply more_general_intro; intros.
inversion_clear H0; elim H1; clear H1; intro sg.
unfold gen_type in |- *; intros.
elim (product_list_exists t env2 sg); eauto.
intros phi def_phi.
apply gen_instance_intro.
exists
 (map_extend_subst_type (type_from_stamp_list (snd (gen_aux t env1 nil))) phi).
rewrite
 (more_general_gen_type_aux env1 env2 t t0 phi nil nil
    (snd (gen_aux t env2 nil)) (snd (gen_aux t env1 nil)) sg)
 ; auto.
Qed.

(*********************************************************************)

Lemma type_of_var1 :
 forall (i j : identifier) (env : environment) (t : type) (ts : type_scheme),
 i <> j ->
 type_of env (Variabl i) t -> type_of ((j, ts) :: env) (Variabl i) t.
intros.
inversion_clear H0.
apply type_of_var with (ts := ts0); auto.
simpl in |- *; rewrite eq_identifier_diff; auto.
Qed.

(*********************************************************************)

Lemma type_of_var2 :
 forall (i j : identifier) (env : environment) (t : type) (ts : type_scheme),
 i <> j ->
 type_of ((j, ts) :: env) (Variabl i) t -> type_of env (Variabl i) t.
intros.
inversion_clear H0.
apply type_of_var with (ts := ts0); auto.
generalize H1; clear H1; simpl in |- *.
rewrite eq_identifier_diff; auto.
Qed.

(*********************************************************************)
Lemma typing_in_a_more_general_env :
 forall (e : expr) (env2 env1 : environment) (t : type),
 more_general_env env1 env2 -> type_of env2 e t -> type_of env1 e t.
simple induction e.
(*Nat*)
intros; inversion_clear H0; auto.

(*Var i*)
simple induction env2.
(*env2=[]*)
simpl in |- *; intros.
inversion_clear H0; discriminate H1.

(*env2=(y,y0)::..*)
intro a; elim a; simpl in |- *; do 7 intro.
inversion_clear H0.
elim (identifier_dec a0 i); intros eq1.
(*a0=i*)rewrite eq1; intro; inversion_clear H0.
apply type_of_var with (ts := ts1).
simpl in |- *; rewrite eq_identifier_reflexivity; auto.

simpl in H3; generalize H3; clear H3.
rewrite eq_identifier_reflexivity; simpl in |- *; intros.
injection H3; intros.
inversion_clear H2; apply H5; auto.
rewrite H0; auto.

(*a0<>i*)intro; apply type_of_var1; auto.
apply H; auto.
apply (type_of_var2 i a0 l t b); auto.

(*lambda*)
intros.
inversion_clear H1.
apply type_of_lambda.
apply H with (env2 := add_environment env2 i (type_to_type_scheme t0)); auto.
apply more_general_env_add_ts; auto.
(*rec*)
intros.
inversion_clear H1.
apply type_of_rec_fun.
apply
 H
  with
    (env2 := add_environment
               (add_environment env2 i0 (type_to_type_scheme t0)) i
               (type_to_type_scheme (Arrow t0 t'))); 
 auto.
apply more_general_env_add_ts; auto.
apply more_general_env_add_ts; auto.
(*apply*)
intros.
inversion_clear H2.
apply type_of_app with (t := t0).
apply H with (env2 := env2); auto.
apply H0 with (env2 := env2); auto.
(*Let*)
intros.
inversion_clear H2.
apply type_of_let_in with (t := t0).
apply H with (env2 := env2); auto.
apply H0 with (env2 := add_environment env2 i (gen_type t0 env2)); auto.
apply more_general_env_add_ts; auto.
apply more_general_gen_type; auto.
Qed.

(***************************************************************************)
Lemma more_general_gen_type_aux2 :
 forall (env1 env2 : environment) (tau t : type) (phi : substitution)
   (gv_env2 gv_env1 L P : list stamp) (sg : list type),
 is_subset_list_stamp (FV_env env1) (FV_env env2) ->
 are_disjoints (FV_env env2) gv_env2 ->
 are_disjoints (FV_env env1) gv_env1 ->
 apply_subst_gen sg (fst (gen_aux tau env2 gv_env2)) = Some_subst_gen t ->
 is_prefixe_free2 (FV_env env2) (snd (gen_aux tau env2 gv_env2)) L ->
 product_list L sg = Some_product phi ->
 is_prefixe_free2 (FV_env env1) (snd (gen_aux tau env1 gv_env1)) P ->
 apply_subst_gen (map_extend_subst_type (type_from_stamp_list P) phi)
   (fst (gen_aux tau env1 gv_env1)) = Some_subst_gen t.
simple induction tau.
do 7 intro; simpl in |- *; intro subset_hyp; intros.
injection H1; intros; rewrite H5; auto.

do 8 intro; intros subset_hyp disjoint1 disjoint2.
simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env1))); intro y; rewrite y;
 simpl in |- *.
(* y : (in_list_stamp s (FV_env env1))=true*)
rewrite (subset_inv1 (FV_env env1) (FV_env env2) s subset_hyp y); auto.
(* y : (in_list_stamp s (FV_env env1))=false*)
elim (index_answer_dec (index gv_env1 s)).
(**{n:nat | (index gv_env1 s)=(Index_in n)}*)
intro s_in_l; elim s_in_l; intros n0; clear s_in_l; intro s_in_l;
 rewrite s_in_l; simpl in |- *.
do 4 intro.
inversion_clear H2.
elim H3; clear H3; intros P2 Hyp.
elim Hyp; clear Hyp; intros Def_P disjoint3; rewrite Def_P.
rewrite (type_from_stamp_list_app gv_env1 P2).
rewrite
 (map_extend_app phi (type_from_stamp_list gv_env1) (type_from_stamp_list P2))
 .
rewrite
 (nth_app (map_extend_subst_type (type_from_stamp_list gv_env1) phi)
    (map_extend_subst_type (type_from_stamp_list P2) phi) n0)
 .
rewrite (nth_map phi (type_from_stamp_list gv_env1) n0 (Var s)).
rewrite (gen_subst_to_subst_aux_4 env2 (Var s) t gv_env2 L sg phi); auto.

apply index_nth; auto.

rewrite length_map.
rewrite length_type_from_stamp_list.
apply (index_lt gv_env1 s n0 s_in_l).

(** y0 : (index gv_env1 s)=Stamp_not_in*)
intro y0; rewrite y0.
do 4 intro.
inversion_clear H2.
elim H3; clear H3; intros P2 Hyp.
elim Hyp; clear Hyp; intros Def_P disjoint3; rewrite Def_P.
simpl in |- *.
rewrite (type_from_stamp_list_app (gv_env1 ++ s :: nil) P2).
rewrite
 (map_extend_app phi (type_from_stamp_list (gv_env1 ++ s :: nil))
    (type_from_stamp_list P2)).
rewrite
 (nth_app
    (map_extend_subst_type (type_from_stamp_list (gv_env1 ++ s :: nil)) phi)
    (map_extend_subst_type (type_from_stamp_list P2) phi) 
    (length gv_env1)).
rewrite
 (nth_map phi (type_from_stamp_list (gv_env1 ++ s :: nil)) 
    (length gv_env1) (Var s)).
rewrite (gen_subst_to_subst_aux_4 env2 (Var s) t gv_env2 L sg phi); auto.

rewrite type_from_stamp_list_app; simpl in |- *.
rewrite <- length_type_from_stamp_list; auto.

rewrite length_map2; rewrite length_app_cons; auto.


(*arrow*)
do 11 intro; intros subset_hyp disjoint1 disjoint2.
rewrite fst_gen_aux_arrow_rewrite; intro.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (fst (gen_aux t env2 gv_env2))
    (fst (gen_aux t0 env2 (snd (gen_aux t env2 gv_env2)))) t1 sg H1).
intro x; elim x; clear x; do 2 intro; clear H1.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro rwt_t1; rewrite rwt_t1.
rewrite snd_gen_aux_arrow_rewrite; do 2 intro.
rewrite snd_gen_aux_arrow_rewrite.
rewrite fst_gen_aux_arrow_rewrite; intro.
simpl in |- *.
rewrite (H a phi gv_env2 gv_env1 L P sg); eauto.
rewrite
 (H0 b phi (snd (gen_aux t env2 gv_env2)) (snd (gen_aux t env1 gv_env1)) L P
    sg); auto.
Qed.

(********************************************************************)
Lemma more_gen_subset_gen :
 forall (env1 env2 : environment) (t : type),
 is_subset_list_stamp (FV_env env1) (FV_env env2) ->
 more_general (gen_type t env1) (gen_type t env2).
Proof.
intros; apply more_general_intro; intros.
inversion_clear H0; elim H1; clear H1; intro sg.
unfold gen_type in |- *; intros.
elim (product_list_exists t env2 sg); eauto.
intros phi def_phi.
apply gen_instance_intro.
exists
 (map_extend_subst_type (type_from_stamp_list (snd (gen_aux t env1 nil))) phi).
rewrite
 (more_general_gen_type_aux2 env1 env2 t t0 phi nil nil
    (snd (gen_aux t env2 nil)) (snd (gen_aux t env1 nil)) sg)
 ; auto.
Qed.

(********************************************************************)

Lemma more_general_gen_add :
 forall (env : environment) (x : identifier) (ts : type_scheme) (t : type),
 more_general (gen_type t env) (gen_type t (add_environment env x ts)).
Proof.
intros; apply more_gen_subset_gen.
simpl in |- *; auto.
Qed.
