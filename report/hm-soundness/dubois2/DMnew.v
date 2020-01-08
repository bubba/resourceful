(* author : Catherine Dubois *)

Require Import langs.
Require Import List.
Require Import Le.
Require Import Peano_dec.
Require Import tools.
Require Import tools_bool.
Require Import Lt.
Require Import type_system.
Require Import generic_DB.
Require Import more_general.
Require Import subset.
Require Import FV.
Require Import type_scheme.
Require Import subset_FV_env.
Require Import env_poly.
Require Import s_env_when_s_disjoint_with_env3.
Require Import disjoints.
Require Import completeness.
Require Import stable.
Require Import order_stamp.
Require Import max.
Require Import tools_more_general.
Require Import index_new.
Require Import V.
Require Import more_gen_preserves_subst.
Require Import new_tv.
Require Import DB_gen_stable.
Require Import completeness_var_tools.
Require Import subst.
Require Import not_in_FV_env.
Require Import tools_correctness.

Lemma subset_FV_ts_FV_env :
 forall (i : identifier) (env : environment) (ts : type_scheme),
 assoc_ident_in_env i env = Ident_in_env ts ->
 is_subset_list_stamp (FV_type_scheme ts) (FV_env env).
simple induction env.
simpl in |- *; intros ts pb; discriminate pb.

simpl in |- *; do 4 intro; elim a; intros j ts1; simpl in |- *.
elim (eq_identifier i j); simpl in |- *; intros.
inversion_clear H0; auto.

apply subset_of_union2; auto.
Qed.
Hint Resolve subset_FV_ts_FV_env.

Lemma subset_add_env_t2ts :
 forall (env : environment) (t : type) (x : identifier),
 is_subset_list_stamp (FV_type t)
   (FV_env (add_environment env x (type_to_type_scheme t))).

simple induction env.

simpl in |- *; intros.
rewrite FV_type_scheme_type_to_type_scheme; auto.

intros a l ind t x; elim a; intros y t0; simpl in |- *.
rewrite FV_type_scheme_type_to_type_scheme; auto.
Qed.
Hint Resolve subset_add_env_t2ts.

(**************************************************************************)
(*    bind a list of free variables in a type scheme                       *)
(**************************************************************************)

Definition index_var := index_new V eq_V.

Definition index_V_app := index_new_app2 V eq_V V_dec V_reflexivity V_diff.

Definition index_V_app_cons :=
  index_new_app_cons2 V eq_V V_dec V_reflexivity V_diff.

Definition index_V_app_cons_inv :=
  index_new_app_cons_inv2 V eq_V V_dec V_reflexivity V_diff.

Definition index_V_lt := index_new_lt2 V eq_V V_dec V_reflexivity V_diff.

Fixpoint bind_aux (l : list stamp) (ts : type_scheme) 
 (lv : list V) {struct ts} : type_scheme * list V :=
  match ts with
  | Nat_ts => (Nat_ts, lv)
  | Gen_var v =>
      match index_var lv (B v) with
      | Stamp_not_in => (Gen_var (Stamp (length lv)), lv ++ B v :: nil)
      | Index_in k => (Gen_var (Stamp k), lv)
      end
  | Var_ts v =>
      if_ (type_scheme * list V) (in_list_stamp v l)
        match index_var lv (F v) with
        | Stamp_not_in => (Gen_var (Stamp (length lv)), lv ++ F v :: nil)
        | Index_in k => (Gen_var (Stamp k), lv)
        end (Var_ts v, lv)
  | Arrow_ts ts1 ts2 =>
      match bind_aux l ts1 lv with
      | (ts1', lv_new) =>
          match bind_aux l ts2 lv_new with
          | (ts2', lv_new_new) => (Arrow_ts ts1' ts2', lv_new_new)
          end
      end
  end.


Definition bind_list (l : list stamp) (ts : type_scheme) :=
  fst (bind_aux l ts nil).

Lemma bind_aux_arrow_rwt :
 forall (ts1 ts2 : type_scheme) (l : list stamp) (l1 : list V),
 fst (bind_aux l (Arrow_ts ts1 ts2) l1) =
 Arrow_ts (fst (bind_aux l ts1 l1))
   (fst (bind_aux l ts2 (snd (bind_aux l ts1 l1)))).
intros; simpl in |- *.
elim (bind_aux l ts1 l1); intros a y0; simpl in |- *.
elim (bind_aux l ts2 y0); auto.
Qed.

Lemma Snd_bind_aux_arrow_rwt :
 forall (ts1 ts2 : type_scheme) (l : list stamp) (l1 : list V),
 snd (bind_aux l (Arrow_ts ts1 ts2) l1) =
 snd (bind_aux l ts2 (snd (bind_aux l ts1 l1))).
intros; simpl in |- *.
elim (bind_aux l ts1 l1); intros a y0; simpl in |- *.
elim (bind_aux l ts2 y0); auto.
Qed.

Lemma Snd_bind_aux_with_app :
 forall (l : list stamp) (ts : type_scheme) (l1 : list V),
 {l0 : list V | snd (bind_aux l ts l1) = l1 ++ l0}.
simple induction ts.
simpl in |- *; exists (nil (A:=V)); apply app_nil_end.

simpl in |- *.
intros.
elim (bool_dec (in_list_stamp s l)); intros test; rewrite test; simpl in |- *.
elim (index_var l1 (F s)).
simpl in |- *.
exists (F s :: nil); auto.

intro.
simpl in |- *.
exists (nil (A:=V)); apply app_nil_end.

exists (nil (A:=V)); apply app_nil_end.

simpl in |- *; intros.
elim (index_var l1 (B s)); simpl in |- *.
exists (B s :: nil); auto.

exists (nil (A:=V)); apply app_nil_end.

intros; rewrite Snd_bind_aux_arrow_rwt.
elim (H l1); intros l0 def_l0; rewrite def_l0.
elim (H0 (l1 ++ l0)); intros l2 def_l2; rewrite def_l2.
rewrite app_ass.
exists (l0 ++ l2); auto.
Qed.

(**************************************************************************)
(*    typing rules according to Damas_Milner                              *)
(**************************************************************************)

Inductive type_of_DM : environment -> expr -> type_scheme -> Prop :=
  | type_of_DM_int_const :
      forall (env : environment) (n : nat),
      type_of_DM env (Const_nat n) Nat_ts
  | type_of_DM_taut :
      forall (env : environment) (x : identifier) (ts : type_scheme),
      assoc_ident_in_env x env = Ident_in_env ts ->
      type_of_DM env (Variabl x) ts
  | type_of_DM_inst :
      forall (env : environment) (e : expr) (ts ts' : type_scheme),
      type_of_DM env e ts -> more_general ts ts' -> type_of_DM env e ts'
  | type_of_DM_gen :
      forall (env : environment) (e : expr) (ts : type_scheme)
        (l : list stamp),
      type_of_DM env e ts ->
      are_disjoints l (FV_env env) -> type_of_DM env e (bind_list l ts)
  | type_of_DM_lambda :
      forall (env : environment) (x : identifier) (e : expr) (t t' : type),
      type_of_DM (add_environment env x (type_to_type_scheme t)) e
        (type_to_type_scheme t') ->
      type_of_DM env (Lambda x e) (type_to_type_scheme (Arrow t t'))
  | type_of_DM_rec_fun :
      forall (env : environment) (f x : identifier) (e : expr) (t t' : type),
      type_of_DM
        (add_environment (add_environment env x (type_to_type_scheme t)) f
           (type_to_type_scheme (Arrow t t'))) e (type_to_type_scheme t') ->
      type_of_DM env (Rec f x e) (type_to_type_scheme (Arrow t t'))
  | type_of_DM_app :
      forall (env : environment) (e e' : expr) (t t' : type),
      type_of_DM env e (type_to_type_scheme (Arrow t t')) ->
      type_of_DM env e' (type_to_type_scheme t) ->
      type_of_DM env (Apply e e') (type_to_type_scheme t')
  | type_of_DM_let_in :
      forall (env : environment) (e e' : expr) (x : identifier)
        (ts : type_scheme) (t : type),
      type_of_DM env e ts ->
      type_of_DM (add_environment env x ts) e' (type_to_type_scheme t) ->
      type_of_DM env (Let_in x e e') (type_to_type_scheme t).

Hint Resolve type_of_DM_int_const.

(* est aussi dans srt *)
Lemma gen_instance_type_to_type_scheme_inv :
 forall t t0 : type, is_gen_instance t0 (type_to_type_scheme t) -> t0 = t.
intros; inversion_clear H.
elim H0.
intro sg; rewrite apply_subst_gen_type_to_type_scheme.
intro y; inversion_clear y; auto.
Qed.

Lemma gen_instance_type_to_type_scheme :
 forall t : type, is_gen_instance t (type_to_type_scheme t).
intro; apply gen_instance_intro.
exists (nil (A:=type)); simpl in |- *.
apply apply_subst_gen_type_to_type_scheme.
Qed.

Lemma type_scheme_and_list_stamp_inv :
 forall ts_l : type_scheme * list stamp,
 {ts_l1 : type_scheme * list stamp | ts_l1 = ts_l}.
intro.
exists ts_l; auto.
Qed.


Lemma in_list_app_cons :
 forall (l : list stamp) (s : stamp), in_list_stamp s (l ++ s :: nil) = true.
simple induction l.

simpl in |- *; intro; rewrite eq_stamp_reflexivity; auto.

simpl in |- *; intros.
elim (stamp_dec s a); intro dec.
rewrite dec; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; auto.
Qed.

Lemma index_in_list :
 forall (l : list stamp) (s : stamp) (n : nat),
 index l s = Index_in n -> in_list_stamp s l = true.
simple induction l.
simpl in |- *; intros s n pb; discriminate pb.

intros a l0 ind_hyp s n; simpl in |- *.
elim (stamp_dec s a); intro dec.
rewrite dec; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index l0 s)); intro dec2.
elim dec2; intros k def_k; rewrite def_k.
intro; apply (ind_hyp s k def_k).

rewrite dec2; intro pb; discriminate pb.
Qed.


Lemma in_list_app_fst :
 forall (l1 l2 : list stamp) (s : stamp),
 in_list_stamp s l1 = true -> in_list_stamp s (l1 ++ l2) = true.
simple induction l1.
simpl in |- *; intros l2 s pb; discriminate pb.

intros a l0 ind_hyp l2 s; simpl in |- *.
elim (stamp_dec s a); intro dec.
rewrite dec; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; auto.
Qed.


Fixpoint turn (f : stamp -> V) (l : list stamp) {struct l} : 
 list V := match l with
           | nil => nil (A:=V)
           | x :: r => f x :: turn f r
           end.

 
Lemma index_var_turn_F2 :
 forall (l : list stamp) (s : stamp), index_var (turn F l) (F s) = index l s.
simple induction l; auto.
unfold index_var in |- *; intros; simpl in |- *.
elim (stamp_dec s a); intro eq_s_a.
rewrite eq_s_a; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.
rewrite (H s); auto.
Qed.

Lemma index_var_turn_B2 :
 forall (l : list stamp) (s : stamp), index_var (turn B l) (B s) = index l s.
simple induction l; auto.
unfold index_var in |- *; intros; simpl in |- *.
elim (stamp_dec s a); intro eq_s_a.
rewrite eq_s_a; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.
rewrite (H s); auto.
Qed.

Lemma length_turn :
 forall (f : stamp -> V) (l : list stamp), length (turn f l) = length l.
simple induction l; auto.
simpl in |- *; intros; auto.
Qed.

Lemma app_turn :
 forall (f : stamp -> V) (l1 l2 : list stamp),
 turn f l1 ++ turn f l2 = turn f (l1 ++ l2).
simple induction l1; auto.
simpl in |- *; intros; rewrite H; auto.
Qed.


Lemma bind_list_gen_type_aux_rwt :
 forall (t : type) (env : environment) (L l : list stamp),
 are_disjoints (FV_env env) l ->
 is_prefixe_free2 (FV_env env) (snd (gen_aux t env l)) L ->
 bind_aux L (type_to_type_scheme t) (turn F l) =
 (fst (gen_aux t env l), turn F (snd (gen_aux t env l))).
simple induction t.
auto.

simpl in |- *; do 5 intro.
elim (bool_dec (in_list_stamp s (FV_env env))); intro in_list_eq;
 rewrite in_list_eq; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp.
elim H0; intros x y; elim y; intros H1 H2; rewrite H1.
rewrite (disjoint_inversion2 (l ++ x) (FV_env env) s); auto.
apply are_disjoints_symetry; auto.
apply disjoints_app; auto.


elim (index_answer_dec (index l s)); intros hyp_index.
elim hyp_index; intros n def_n; rewrite def_n; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp.
elim H0; intros x y; elim y; intros H1 H2; rewrite H1.
rewrite (index_in_list (l ++ x) s n); auto.
rewrite (index_var_turn_F2 l s); simpl in |- *.
rewrite def_n; auto.

apply index_app; auto.

rewrite (index_var_turn_F2 l s); rewrite hyp_index; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp.
elim H0; intros x y; elim y; intros H1 H2; rewrite H1.
rewrite in_list_app_fst; auto.
rewrite length_turn; rewrite <- app_turn; auto.
apply in_list_app_cons.

simpl in |- *; do 8 intro.
elim (type_scheme_and_list_stamp_inv (gen_aux t0 env l)); intro x; elim x;
 clear x; intros ts1 L1 def_x; rewrite <- def_x.
elim (type_scheme_and_list_stamp_inv (gen_aux t1 env L1)); intro y; elim y;
 clear y; intros ts2 L2 def_y; rewrite <- def_y; simpl in |- *.
intro prefixe_hyp.
rewrite (H env L l H1).
rewrite (H0 env L (snd (gen_aux t0 env l))); auto.
rewrite <- def_x; simpl in |- *; rewrite <- def_y; auto.

rewrite <- def_x; simpl in |- *; rewrite <- def_y; auto.

apply is_prefixe2_gen_aux with (t := t1).
rewrite <- def_x; simpl in |- *; rewrite <- def_y; auto.
Qed.


Lemma bind_list_gen_type_rwt :
 forall (t : type) (env : environment),
 bind_list (snd (gen_aux t env nil)) (type_to_type_scheme t) = gen_type t env.
intros; unfold bind_list in |- *; unfold gen_type in |- *.
change
  (fst
     (bind_aux (snd (gen_aux t env nil)) (type_to_type_scheme t) (turn F nil)) =
   fst (gen_aux t env nil)) in |- *.
rewrite (bind_list_gen_type_aux_rwt t env (snd (gen_aux t env nil)) nil);
 auto.
Qed.

Lemma sound2 :
 forall (e : expr) (env : environment) (t : type),
 type_of env e t -> type_of_DM env e (type_to_type_scheme t).
Proof.
simple induction e.
(* const *)
intros n env t Hyp_type.
inversion_clear Hyp_type; auto.

(* variable *)
intros i env t Hyp_type.
inversion_clear Hyp_type.
apply type_of_DM_inst with (ts := ts).
apply type_of_DM_taut; auto.

apply more_general_intro; intros.
rewrite (gen_instance_type_to_type_scheme_inv t t0 H1); auto.

(* lambda *)
intros i e0 Hyp_ind env t Hyp_type.
inversion_clear Hyp_type.
apply type_of_DM_lambda.
auto.

(* Rec *)
intros i i0 e0 Hyp_ind env t Hyp_type.
inversion_clear Hyp_type.
apply type_of_DM_rec_fun.
auto.

(* Apply *)
intros e0 Hyp_ind0 e1 Hyp_ind1 env t Hyp_type.
inversion_clear Hyp_type.
apply type_of_DM_app with (t := t0); auto.

(* Let *)
intros i e0 Hyp_ind0 e1 Hyp_ind1 env t Hyp_type.
inversion_clear Hyp_type.
apply type_of_DM_let_in with (ts := gen_type t0 env); auto.
rewrite <- bind_list_gen_type_rwt.
apply type_of_DM_gen; auto.

apply are_disjoints_symetry; auto.
Qed.

(**********************************************************************)
(**********************************************************************)
Inductive G : environment -> expr -> type_scheme -> Prop :=
    intro_G :
      forall (env : environment) (e : expr) (ts : type_scheme),
      {t : type | type_of env e t /\ more_general (gen_type t env) ts} ->
      G env e ts.

Lemma more_general_trans :
 forall ts1 ts2 ts3 : type_scheme,
 more_general ts1 ts2 -> more_general ts2 ts3 -> more_general ts1 ts3.
intros ts1 ts2 ts3 Hyp_ts1_2 Hyp_ts2_3.   
inversion_clear Hyp_ts1_2.
inversion_clear Hyp_ts2_3.
apply more_general_intro; auto.
Qed.



(*aussi pour srt*)
Lemma find_new_tv_type_scheme2 :
 forall ts : type_scheme, {st : stamp | new_tv_type_scheme ts st}.
intro ts.
exists (succ_stamp (max_list_stamp (FV_type_scheme ts))).
apply
 new_tv_ts_trans_le
  with (st1 := succ_stamp (max_list_stamp (FV_type_scheme ts))); 
 auto.
(*Apply new_tv_max.*)
Qed.

Lemma exists_st_new_tv_env :
 forall env : environment, {st : stamp | new_tv_env env st}.
simple induction env.
exists (Stamp 0); auto.

intros a; elim a; intros x ts env0 ind.
elim ind; intros st0 new_tv_env0_st0.
elim (find_new_tv_type_scheme2 ts).
intros st new_tv_ts_st.
exists (max_stamp st st0).
apply new_tv_env_cons.
apply (new_tv_env_trans_le env0 st0 (max_stamp st st0)); auto.
apply (new_tv_ts_trans_le ts st (max_stamp st st0)); auto.
Qed.


Lemma type_of_type_to_type_scheme :
 forall (e : expr) (env : environment) (t t1 : type),
 type_of env e t1 ->
 more_general (gen_type t1 env) (type_to_type_scheme t) -> type_of env e t.

intros e env t t1 type_of_hyp gen_hyp; inversion_clear gen_hyp.
generalize (H t (gen_instance_type_to_type_scheme t)).
intro t_gen_inst_of_gen_t1; inversion_clear t_gen_inst_of_gen_t1.
elim H0; intros sg def_t.
unfold gen_type in def_t.
elim (product_list_exists t1 env sg); eauto.
intros phi def_phi.
rewrite <-
 (gen_subst_to_subst_aux_4 env t1 t nil (snd (gen_aux t1 env nil)) sg phi)
 ; auto.
rewrite <- (s_env_when_s_disjoint_with_env3 phi env).
apply typage_is_stable_by_substitution; auto.

rewrite (domain_product (snd (gen_aux t1 env nil)) sg phi def_phi).
apply are_disjoints_symetry; auto.
Qed.



Inductive is_prefixe : list V -> list V -> Prop :=
    prefixe_intro :
      forall l L : list V, {l1 : list V | L = l ++ l1} -> is_prefixe l L.


Lemma is_prefixe_reflexivity : forall L : list V, is_prefixe L L.
intros; simpl in |- *; apply prefixe_intro.
exists (nil (A:=V)).
apply app_nil_end.
Qed.
Hint Resolve is_prefixe_reflexivity.

Lemma is_prefixe_bind_aux :
 forall (ts1 ts2 : type_scheme) (l1 L : list V) (l : list stamp),
 is_prefixe (snd (bind_aux l ts2 (snd (bind_aux l ts1 l1)))) L ->
 is_prefixe (snd (bind_aux l ts1 l1)) L.
intros ts1 ts2 l1 L l.
elim (Snd_bind_aux_with_app l ts2 (snd (bind_aux l ts1 l1))).
intros l0 def_snd_bind; rewrite def_snd_bind.
intro pref_hyp; inversion_clear pref_hyp.
elim H; intros l2 def_l2; rewrite def_l2.
apply prefixe_intro.
exists (l0 ++ l2).
apply app_ass.
Qed.
Hint Resolve is_prefixe_bind_aux.



(**************************************************************************)
(*                   ts is more general than (bind nil ts)                *)
(**************************************************************************)

Fixpoint sort_gen_subst (sg : list type) (l : list V) 
 (p : nat) {struct p} : Exc (list type) :=
  match p with
  | O => value nil
  | S k =>
      match sort_gen_subst sg l k with
      | None => error (A:=list type)
      | Some sg' =>
          match index_var l (B (Stamp k)) with
          | Stamp_not_in => value (sg' ++ Nat :: nil)
          | Index_in p =>
              match nth p sg with
              | Type_not_in => error (A:=list type)
              | Nth_in t => value (sg' ++ t :: nil)
              end
          end
      end
  end.

(***********************************************************************)
Lemma length_sort_gen_subst :
 forall (p : nat) (l1 : list V) (sg sg' : list type),
 sort_gen_subst sg l1 p = value sg' -> length sg' = p.
simple induction p.
simpl in |- *; intros; inversion_clear H; auto.

do 5 intro; simpl in |- *.
elim (exc_dec (list type) (sort_gen_subst sg l1 n)).
intro y.
elim y; intros sg1.
intro y0.
rewrite y0.
elim (index_var l1 (B (Stamp n))).
intro.
inversion_clear H0; simpl in |- *.
rewrite length_app.
simpl in |- *.
rewrite (H l1 sg sg1 y0); auto.

intro.
elim (nth n0 sg).
intro pb; discriminate pb.

intros; inversion_clear H0.
rewrite length_app; simpl in |- *.
rewrite (H l1 sg sg1 y0); auto.

intro y; rewrite y; intro pb; discriminate pb.
Qed.

(***************************************************************************)

Lemma nth_sort_gen_subst :
 forall (p : nat) (l1 : list V) (sg sg' : list type),
 sort_gen_subst sg l1 p = value sg' ->
 forall (k n : nat) (t : type),
 n < p ->
 index_var l1 (B (Stamp n)) = Index_in k ->
 nth k sg = Nth_in t -> nth n sg' = Nth_in t.
simple induction p.

intros; inversion H0.

intros p0 ind_hyp l1 sg sg'; simpl in |- *.
(**)elim (exc_dec (list type) (sort_gen_subst sg l1 p0)); intro dec1.
elim dec1; intros sg1 def_sg1; rewrite def_sg1.
(***)elim (index_answer_dec (index_var l1 (B (Stamp p0)))); intro dec2.
elim dec2; intros j def_j; rewrite def_j.
(****)elim (nth_answer_inv (nth j sg)); intro dec3.
elim dec3; intros t' def_t'; rewrite def_t'; intro def_sg';
 inversion_clear def_sg'.
intros k n t lt_hyp.
elim (le_lt_or_eq n p0); auto with *.
intro n_lt_p0.
rewrite nth_app.
intros; apply (ind_hyp l1 sg sg1 def_sg1 k n t); auto.

rewrite (length_sort_gen_subst p0 l1 sg sg1 def_sg1); auto.

intro n_is_p0; rewrite n_is_p0.
rewrite def_j.
intro index_j_k; injection index_j_k; intro j_is_k; rewrite <- j_is_k.
rewrite def_t'; intro nth_t'_t; inversion_clear nth_t'_t.
rewrite <- (length_sort_gen_subst p0 l1 sg sg1 def_sg1).
apply nth_app_cons.

(****)rewrite dec3; intro pb; discriminate pb.

(***)rewrite dec2.
intro def_sg'; inversion_clear def_sg'.
intros k n t lt_hyp.
elim (le_lt_or_eq n p0); auto with *.
intro n_lt_p0.
rewrite nth_app.
intros; apply (ind_hyp l1 sg sg1 def_sg1 k n t); auto.

rewrite (length_sort_gen_subst p0 l1 sg sg1 def_sg1); auto.

intro n_is_p0; rewrite n_is_p0.
rewrite dec2.
intro pb; discriminate pb.

(**)rewrite dec1; intro pb; discriminate pb.
Qed.

Lemma ts_more_gen_then_bind_aux_nil :
 forall (ts : type_scheme) (l1 L : list V) (tau : type) 
   (sg sg' : list type) (p : nat),
 apply_subst_gen sg (fst (bind_aux nil ts l1)) = Some_subst_gen tau ->
 is_prefixe (snd (bind_aux nil ts l1)) L ->
 max_gen_vars ts <= p ->
 sort_gen_subst sg L p = value sg' ->
 apply_subst_gen sg' ts = Some_subst_gen tau.
Proof.
simple induction ts; auto.

(*Gen_var s*)
do 7 intro; elim s; intro n; simpl in |- *.
(**)elim (index_answer_dec (index_var l1 (B (Stamp n)))); intro hyp_dec.
elim hyp_dec; intros k def_k; rewrite def_k; simpl in |- *.
(***)elim (nth_answer_inv (nth k sg)); intro hyp_dec2.
elim hyp_dec2; intros t def_t; rewrite def_t; simpl in |- *; intro t_tau;
 injection t_tau; intro t_eq_tau; rewrite <- t_eq_tau.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L.
rewrite def_L; intros le_hyp def_sg'.
rewrite (nth_sort_gen_subst p (l1 ++ l0) sg sg' def_sg' k n t); auto.
(******Unfold index_var;Apply index_new_app; Auto.*)
apply index_V_app; auto.

(***)rewrite hyp_dec2; intro pb; discriminate pb.

(**)rewrite hyp_dec; simpl in |- *.
(***)elim (nth_answer_inv (nth (length l1) sg)); intro hyp_dec2.
elim hyp_dec2; intros t def_t; rewrite def_t; simpl in |- *; intro t_tau;
 injection t_tau; intro t_eq_tau; rewrite <- t_eq_tau.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L.
rewrite def_L; intros le_hyp def_sg'.
generalize
 (nth_sort_gen_subst p ((l1 ++ B (Stamp n) :: nil) ++ l0) sg sg' def_sg').
intro H; rewrite (H (length l1) n t); auto.
(*Unfold index_var; Apply index_new_app.*)
apply index_V_app; auto.
(*Unfold index_var; Apply index_new_app_cons;Auto.*)
apply index_V_app_cons; auto.

(***)rewrite hyp_dec2; intro pb; discriminate pb.

(*Arrow_ts ts1 ts2*)
intros ts1 hyp_ind1 ts2 hyp_ind2 l1 L tau sg sg' p.
rewrite bind_aux_arrow_rwt.
intro apply_subst_gen_hyp.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (fst (bind_aux nil ts1 l1))
    (fst (bind_aux nil ts2 (snd (bind_aux nil ts1 l1)))) tau sg
    apply_subst_gen_hyp).
intro x; elim x; clear x; do 2 intro.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro tau_rwt; rewrite tau_rwt.
rewrite Snd_bind_aux_arrow_rwt.
intros prefixe_hyp le_hyp def_sg'; simpl in le_hyp.
simpl in |- *.
rewrite (hyp_ind1 l1 L a sg sg' p); eauto.
rewrite (hyp_ind2 (snd (bind_aux nil ts1 l1)) L b sg sg' p); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.

Definition valid_list_V_index (L : list V) (sg : list type) :=
  forall n n0 : nat,
  index_var L (B (Stamp n)) = Index_in n0 ->
  {t : type | nth n0 sg = Nth_in t}.

Lemma domain_of_sort_gen_subst :
 forall (L : list V) (sg : list type) (p : nat),
 valid_list_V_index L sg ->
 {sg' : list type | sort_gen_subst sg L p = value sg'}.
simple induction p.
intro; simpl in |- *; exists (nil (A:=type)); auto.

intros; simpl in |- *; elim (H H0).
intros sg1 def_sg1; rewrite def_sg1.
elim (index_answer_dec (index_var L (B (Stamp n)))); intro dec1.
elim dec1; intros n0 def_n0; rewrite def_n0.
unfold valid_list_V_index in H0.
elim (H0 n n0 def_n0).
intros t def_t; rewrite def_t.
exists (sg1 ++ t :: nil); auto.

rewrite dec1.
exists (sg1 ++ Nat :: nil); auto.
Qed.


Lemma valid_list_V_index_Snd_bind_aux_nil :
 forall (ts : type_scheme) (sg : list type) (L : list V),
 valid_list_V_index L sg ->
 max_gen_vars (fst (bind_aux nil ts L)) <= length sg ->
 valid_list_V_index (snd (bind_aux nil ts L)) sg.
simple induction ts; auto.

intros s sg L valid_hyp; simpl in |- *; elim s; intro p.
elim (index_answer_dec (index_var L (B (Stamp p)))); intro dec1.
elim dec1; intros n0 def_n0; rewrite def_n0; auto.

rewrite dec1; simpl in |- *; intro le_hyp.
unfold valid_list_V_index in |- *; intros n n0.
elim (eq_nat_dec n p); intro n_is_p.
rewrite n_is_p.
(*Unfold index_var.
(Rewrite -> index_new_app_cons; Auto).*)
rewrite index_V_app_cons; auto.
intro.
unfold valid_list_V_index in valid_hyp.
inversion_clear H.
apply nth_succeeds; auto.

(*Unfold index_var; *)
intros index_hyp.
unfold valid_list_V_index in valid_hyp.
apply valid_hyp with (n := n).
unfold index_var in |- *.
 apply index_V_app_cons_inv with (s1 := B (Stamp p)); 
 auto.
unfold not in |- *; intros.
injection H; intros.
absurd (n = p); auto.

intros ts1 ind1 ts2 ind2 sg L valid_hyp.
rewrite Snd_bind_aux_arrow_rwt.
rewrite bind_aux_arrow_rwt.
intro le_hyp.
apply ind2.
apply ind1; auto.
apply
 le_trans
  with
    (m := max (max_gen_vars (fst (bind_aux nil ts1 L)))
            (max_gen_vars (fst (bind_aux nil ts2 (snd (bind_aux nil ts1 L))))));
 auto.
apply
 le_trans
  with
    (m := max (max_gen_vars (fst (bind_aux nil ts1 L)))
            (max_gen_vars (fst (bind_aux nil ts2 (snd (bind_aux nil ts1 L))))));
 auto.

Qed.

Lemma sort_subst_gen_exists :
 forall (sg : list type) (ts : type_scheme),
 max_gen_vars (bind_list nil ts) <= length sg ->
 {sg' : list type |
 sort_gen_subst sg (snd (bind_aux nil ts nil)) (max_gen_vars ts) = value sg'}.

unfold bind_list in |- *; intros.
apply domain_of_sort_gen_subst.
apply valid_list_V_index_Snd_bind_aux_nil; auto.
(*(valid_list_V_index (nil V) sg)*)
unfold valid_list_V_index in |- *; unfold index_var in |- *; simpl in |- *;
 intros; discriminate H0.
Qed.

Lemma ts_more_gen_then_bind_nil :
 forall ts : type_scheme, more_general ts (bind_list nil ts).
intro ts; apply more_general_intro; intros.
inversion_clear H.
elim H0; clear H0; intros sg def_t.
elim (sort_subst_gen_exists sg ts); eauto.
intros sg' def_sg'.
apply gen_instance_intro.
exists sg'.
apply
 (ts_more_gen_then_bind_aux_nil ts nil (snd (bind_aux nil ts nil)) t sg sg'
    (max_gen_vars ts)); auto.
Qed.


(**************************************************************************)
(*                     (bind l ts) is more general than ts                *)
(**************************************************************************)
Fixpoint map_sg_var (sg : list type) (L : list V) {struct L} :
 Exc (list type) :=
  match L with
  | nil => value nil
  | v :: L0 =>
      match map_sg_var sg L0 with
      | None => error (A:=list type)
      | Some sg1 =>
          match v with
          | B (Stamp n) =>
              match nth n sg with
              | Type_not_in => error (A:=list type)
              | Nth_in t => value (t :: sg1)
              end
          | F s => value (Var s :: sg1)
          end
      end
  end.


Definition valid_list_V_bis (L : list V) (sg : list type) :=
  forall n n0 : nat,
  index_var L (B (Stamp n)) = Index_in n0 -> {t : type | nth n sg = Nth_in t}.

Lemma valid_list_V_bis_inv2 :
 forall (sg : list type) (l0 : list V) (v : V),
 valid_list_V_bis (v :: l0) sg -> valid_list_V_bis l0 sg. 
unfold valid_list_V_bis in |- *; simpl in |- *; do 3 intro;
 unfold index_var in |- *.
case v; intro s.
elim s; intros k ind n.
elim (eq_nat_dec n k); intro hyp.
rewrite hyp; intros.
apply (ind k 0).
simpl in |- *; rewrite eq_nat_reflexivity; auto.

intros; apply (ind n (S n0)).
simpl in |- *.
rewrite eq_nat_diff; auto.
simpl in |- *; rewrite H; auto.

intros ind n n0 index_hyp.
apply (ind n (S n0)).
simpl in |- *; rewrite index_hyp; auto.
Qed.


Lemma domain_of_map_sg_var :
 forall (sg : list type) (L : list V),
 valid_list_V_bis L sg -> {sg' : list type | map_sg_var sg L = value sg'}.
simple induction L.
intro; simpl in |- *; exists (nil (A:=type)); auto.

intros a l0 ind_hyp; simpl in |- *.
case a; intro a0.
elim a0; intros n0.
intro valid_hyp.
unfold valid_list_V_bis in valid_hyp.
elim (valid_hyp n0 0).
intros t def_t; rewrite def_t.
elim (ind_hyp (valid_list_V_bis_inv2 sg l0 (B (Stamp n0)) valid_hyp)).
intros sg1 def_sg1; rewrite def_sg1.
exists (t :: sg1); auto.

unfold index_var in |- *; simpl in |- *; rewrite eq_nat_reflexivity; auto. 

intro valid_hyp.
unfold valid_list_V_bis in valid_hyp.
elim (ind_hyp (valid_list_V_bis_inv2 sg l0 (F a0) valid_hyp)).
intros sg1 def_sg1; rewrite def_sg1.
exists (Var a0 :: sg1); auto.
Qed.

Lemma map_sg_var_nth :
 forall (sg : list type) (L : list V) (sg' : list type) (n : nat) (s : stamp),
 map_sg_var sg L = value sg' ->
 index_var L (F s) = Index_in n -> nth n sg' = Nth_in (Var s).
Proof.
unfold index_var in |- *; simple induction L.

simpl in |- *; intros; discriminate H0.

intros a L0 ind_hyp sg' n s; simpl in |- *.
elim (exc_dec (list type) (map_sg_var sg L0)); intro dec1.
elim dec1; intros sg1 def_sg1; rewrite def_sg1.
case a; intro s0; simpl in |- *; elim s0; intro n0.
elim (nth n0 sg).
intro pb; discriminate pb.

intros t def_sg'.
inversion_clear def_sg'.
elim (index_answer_dec (index_new V eq_V L0 (F s))); intro dec2.
elim dec2; intros j def_j; rewrite def_j.
intro; inversion_clear H.
simpl in |- *; auto.

rewrite dec2; intro pb; discriminate pb.

intro def_sg'; inversion_clear def_sg'.
elim (stamp_dec s (Stamp n0)); intro eq_s_s0.
rewrite eq_s_s0; rewrite eq_stamp_reflexivity; simpl in |- *.
intro; inversion_clear H; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.

elim (index_answer_dec (index_new V eq_V L0 (F s))); intro dec2.
elim dec2; intros j def_j; rewrite def_j.
intro; inversion_clear H; auto.

rewrite dec2; intro pb; discriminate pb.

rewrite dec1; intro pb; discriminate pb.
Qed.

Lemma map_sg_var_nth_B :
 forall (sg : list type) (L : list V) (sg' : list type) 
   (n k : nat) (t : type),
 map_sg_var sg L = value sg' ->
 nth n sg = Nth_in t ->
 index_var L (B (Stamp n)) = Index_in k -> nth k sg' = Nth_in t.
Proof.
unfold index_var in |- *; simple induction L.

simpl in |- *; intros; discriminate H1.

intros a L0 ind_hyp sg' n s t; simpl in |- *.
elim (exc_dec (list type) (map_sg_var sg L0)); intro dec1.
elim dec1; intros sg1 def_sg1; rewrite def_sg1.
case a; intro s0; simpl in |- *; elim s0; intro n0.
elim (nth_answer_inv (nth n0 sg)); intro dec2.
elim dec2; intros t' def_t'; rewrite def_t'; intro def_sg'.
inversion_clear def_sg'.
elim (eq_nat_dec n n0); intro n_eq_n0.
(*n=n0*)rewrite n_eq_n0; rewrite eq_nat_reflexivity; simpl in |- *.
rewrite def_t'; intros def_t n_is_O.
inversion_clear def_t; inversion_clear n_is_O; auto.
(*~n=n0*)
rewrite eq_nat_diff; auto.
simpl in |- *; intro def_t.
elim (index_answer_dec (index_new V eq_V L0 (B (Stamp n)))); intro dec3.
elim dec3; intros k def_k; rewrite def_k.
intro def_s; inversion_clear def_s.
apply (ind_hyp sg1 n k t); auto.

rewrite dec3; intro pb; discriminate pb.

rewrite dec2; intro pb; discriminate pb.

intro def_sg'; inversion_clear def_sg'; intro def_t.
elim (index_answer_dec (index_new V eq_V L0 (B (Stamp n)))); intro dec3.
elim dec3; intros k def_k; rewrite def_k.
intro def_s; inversion_clear def_s.
simpl in |- *; apply (ind_hyp sg1 n k t); auto.

rewrite dec3; intro pb; discriminate pb.

rewrite dec1; intro pb; discriminate pb.
Qed.


Lemma map_sg_var_app_cons_B_inv :
 forall (l : list V) (n : nat) (sg sg' : list type),
 map_sg_var sg (B (Stamp n) :: l) = value sg' ->
 {sg'_t : list type * type |
 map_sg_var sg l = value (fst sg'_t) /\
 nth n sg = Nth_in (snd sg'_t) /\ sg' = snd sg'_t :: fst sg'_t}.
do 4 intro; simpl in |- *.
elim (exc_dec (list type) (map_sg_var sg l)); intros dec1.
elim dec1; intros sg1 def_sg1; rewrite def_sg1.
elim (nth_answer_inv (nth n sg)); intro dec2.
elim dec2; intros t def_t; rewrite def_t.
intro; inversion_clear H.
exists (sg1, t); auto.

rewrite dec2; intro pb; discriminate pb.

rewrite dec1; intro pb; discriminate pb.
Qed.

Lemma map_sg_var_app_cons_F_inv :
 forall (l : list V) (s : stamp) (sg sg' : list type),
 map_sg_var sg (F s :: l) = value sg' ->
 {sg1 : list type | map_sg_var sg l = value sg1 /\ sg' = Var s :: sg1}.
do 4 intro; simpl in |- *.
elim (exc_dec (list type) (map_sg_var sg l)); intros dec1.
elim dec1; intros sg1 def_sg1; rewrite def_sg1.
intro def_sg'; inversion_clear def_sg'.
exists sg1; auto.

rewrite dec1; intro pb; discriminate pb.
Qed.

Lemma map_sg_var_app_inversion :
 forall (l1 l2 : list V) (sg sg' : list type),
 map_sg_var sg (l1 ++ l2) = value sg' ->
 {sg1_sg2 : list type * list type |
 map_sg_var sg l1 = value (fst sg1_sg2) /\
 map_sg_var sg l2 = value (snd sg1_sg2) /\ sg' = fst sg1_sg2 ++ snd sg1_sg2}.
Proof.
simple induction l1.
simpl in |- *; intros; exists (@nil type, sg'); auto.

intros a l ind_hyp l2 sg sg'; rewrite <- app_comm_cons.
case a; intro s.
elim s; intros n hyp_map_cons.
elim (map_sg_var_app_cons_B_inv (l ++ l2) n sg sg' hyp_map_cons).
intro x; elim x; simpl in |- *; intros sg1 t hyp; elim hyp; intros; elim H0;
 intros.
elim (ind_hyp l2 sg sg1 H).
intro y; elim y; intros L1 L2; simpl in |- *; intro y0; elim y0; intros;
 elim H4; intros.
rewrite H3; rewrite H1; rewrite H5.
exists (t :: L1, L2); simpl in |- *; rewrite <- H6; auto.

intro hyp_map_cons.
elim (map_sg_var_app_cons_F_inv (l ++ l2) s sg sg' hyp_map_cons).
intros x hyp; elim hyp; intros.
elim (ind_hyp l2 sg x H).
intro y; elim y; intros L1 L2; simpl in |- *; intro y0; elim y0; intros;
 elim H2; intros.
rewrite H3; rewrite H1.
exists (Var s :: L1, L2); simpl in |- *.
rewrite <- H4; auto.
Qed.


Lemma map_sg_var_bind_aux :
 forall (ts : type_scheme) (l : list stamp) (l1 L : list V) 
   (tau : type) (sg sg' : list type),
 apply_subst_gen sg ts = Some_subst_gen tau ->
 is_prefixe (snd (bind_aux l ts l1)) L ->
 map_sg_var sg L = value sg' ->
 apply_subst_gen sg' (fst (bind_aux l ts l1)) = Some_subst_gen tau.
Proof.
simple induction ts; auto.

(*Var_ts s*)
simpl in |- *; intros s l l1 L tau sg sg' tau_is_var_s.
inversion_clear tau_is_var_s.
elim (bool_dec (in_list_stamp s l)); intro test; rewrite test; simpl in |- *.
(**)elim (index_answer_dec (index_var l1 (F s))); intro dec1.
elim dec1; intros n def_n; rewrite def_n.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L; rewrite def_L.
intro def_sg'; simpl in |- *; rewrite (map_sg_var_nth sg (l1 ++ l0) sg' n s);
 auto.
(*Unfold index_var;Apply index_new_app; Auto.*)
apply index_V_app; auto.

(**)rewrite dec1; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L; rewrite def_L.
intro def_sg'.
elim (map_sg_var_app_inversion (l1 ++ F s :: nil) l0 sg sg' def_sg').
intro x; elim x; intros sg1 sg2 hyp; elim hyp; simpl in |- *;
 intros def_sg1 hyp1.
elim hyp1; intros def_sg2 def_sg'_new.
rewrite def_sg'_new.
rewrite
 (map_sg_var_nth sg ((l1 ++ F s :: nil) ++ l0) (sg1 ++ sg2) (length l1) s)
 ; auto.
rewrite <- def_sg'_new; auto.

(*(Unfold index_var; Apply index_new_app; Auto).*)
apply index_V_app; auto.
(*(Apply index_new_app_cons; Auto).*)
apply index_V_app_cons; auto.

auto.

(*Gen s*)
simpl in |- *; intros s l l1 L tau sg sg'; elim s; intro n.
elim (nth_answer_inv (nth n sg)); intro dec1.
elim dec1; intros t def_t; rewrite def_t; intro t_is_tau; injection t_is_tau;
 clear t_is_tau; intro t_is_tau; rewrite <- t_is_tau.
(**)elim (index_answer_dec (index_var l1 (B (Stamp n)))); intro dec2.
elim dec2; intros k def_k; rewrite def_k.
simpl in |- *; intro prefixe_hyp; inversion_clear prefixe_hyp; elim H;
 clear H; intros l0 def_L; rewrite def_L.
intro def_sg'.
rewrite (map_sg_var_nth_B sg (l1 ++ l0) sg' n k t); auto.
(*Unfold index_var;Apply index_new_app; Auto.*)
apply index_V_app; auto.

(**)rewrite dec2; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L; rewrite def_L.
intro def_sg'.
elim (map_sg_var_app_inversion (l1 ++ B (Stamp n) :: nil) l0 sg sg' def_sg').
intro x; elim x; intros sg1 sg2 hyp; elim hyp; simpl in |- *;
 intros def_sg1 hyp1.
elim hyp1; intros def_sg2 def_sg'_new.
rewrite def_sg'_new.
rewrite
 (map_sg_var_nth_B sg ((l1 ++ B (Stamp n) :: nil) ++ l0) 
    (sg1 ++ sg2) n (length l1) t); auto.
rewrite <- def_sg'_new; auto.

(*(Unfold index_var; Apply index_new_app; Auto).*)
apply index_V_app; auto.
(*(Apply index_new_app_cons; Auto).*)
apply index_V_app_cons; auto.

rewrite dec1; intro pb; discriminate pb.

(*Arrow_ts*)
intros ts1 ind1 ts2 ind2 l l1 L tau sg sg'.
rewrite bind_aux_arrow_rwt.
intro apply_subst_gen_hyp.
elim
 (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 tau sg apply_subst_gen_hyp).
intro x; elim x; clear x; do 2 intro.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro tau_rwt; rewrite tau_rwt.
rewrite Snd_bind_aux_arrow_rwt.
intros prefixe_hyp def_sg'; simpl in |- *.
rewrite (ind1 l l1 L a sg sg'); eauto.
rewrite (ind2 l (snd (bind_aux l ts1 l1)) L b sg sg'); auto.
Qed.



Lemma valid_list_V_bis_Snd_bind_aux_nil :
 forall (ts : type_scheme) (sg : list type) (L : list V) (l : list stamp),
 valid_list_V_bis L sg ->
 max_gen_vars ts <= length sg -> valid_list_V_bis (snd (bind_aux l ts L)) sg.
simple induction ts; auto.

(*Var_ts s*)
unfold valid_list_V_bis in |- *.
unfold index_var in |- *; intros s sg L l valid_hyp; simpl in |- *; elim s;
 intros p le_hyp.
elim (bool_dec (in_list_stamp (Stamp p) l)); intro test; rewrite test;
 simpl in |- *.
elim (index_answer_dec (index_var L (F (Stamp p)))); intro dec1.
elim dec1; intros n0 def_n0; rewrite def_n0; auto.

rewrite dec1; simpl in |- *; intros n n0 index_hyp.
apply (valid_hyp n n0); auto.
apply index_V_app_cons_inv with (s1 := F (Stamp p)); auto.
unfold not in |- *; intro pb; discriminate pb.

auto.

(*Gen_ts s*)
unfold valid_list_V_bis in |- *.
unfold index_var in |- *; intros s sg L l valid_hyp; simpl in |- *; elim s;
 intros p le_hyp.
elim (index_answer_dec (index_var L (B (Stamp p)))); intro dec1.
elim dec1; intros n0 def_n0; rewrite def_n0; auto.

rewrite dec1; simpl in |- *; intros n n0.
elim (eq_nat_dec n p); intro n_is_p.
rewrite n_is_p; intro; apply nth_succeeds; auto.

intro; apply (valid_hyp n n0); auto.
apply index_V_app_cons_inv with (s1 := B (Stamp p)); auto.
unfold not in n_is_p.
unfold not in |- *; intro; apply n_is_p.
injection H0; auto.

(*Arrow_ts ts1 ts2*)
intros ts1 ind1 ts2 ind2 sg L l valid_hyp.
rewrite Snd_bind_aux_arrow_rwt.
simpl in |- *; intro le_hyp.
apply ind2.
apply ind1; auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.



Lemma map_sg_var_exists :
 forall (sg : list type) (ts : type_scheme) (l : list stamp),
 max_gen_vars ts <= length sg ->
 {sg' : list type | map_sg_var sg (snd (bind_aux l ts nil)) = value sg'}.
unfold bind_list in |- *; intros.
apply domain_of_map_sg_var.
apply valid_list_V_bis_Snd_bind_aux_nil; auto.
(*(valid_list_V_bis (nil V) sg)*)
unfold valid_list_V_bis in |- *; unfold index_var in |- *; simpl in |- *;
 intros; discriminate H0.
Qed.

Lemma bind_l_ts_more_gen_than_ts :
 forall (ts : type_scheme) (l : list stamp), more_general (bind_list l ts) ts.
intros ts l; apply more_general_intro; intros.
inversion_clear H.
elim H0; clear H0; intros sg def_t.
elim (map_sg_var_exists sg ts l); eauto.
intros sg' def_sg'.
apply gen_instance_intro.
exists sg'.
apply (map_sg_var_bind_aux ts l nil (snd (bind_aux l ts nil)) t sg sg'); auto.
Qed.

(***************************************************************************)
(*                   (gen t env) is more general than t                    *)
(***************************************************************************)
Lemma t_is_l_gen_aux :
 forall (env : environment) (t : type) (l L : list stamp),
 is_prefixe_free2 (FV_env env) (snd (gen_aux t env l)) L ->
 apply_subst_gen (type_from_stamp_list L) (fst (gen_aux t env l)) =
 Some_subst_gen t.
simple induction t; auto.

(*Var s*)
intros s l L; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro test; rewrite test;
 simpl in |- *; auto.
elim (index_answer_dec (index l s)); intro dec1.
elim dec1; intros n def_n; rewrite def_n; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp.
elim H; intros l0 Hyp; elim Hyp; clear Hyp; intros def_L disjoint_hyp;
 rewrite def_L.
rewrite (type_from_stamp_list_app l l0).
rewrite (nth_app (type_from_stamp_list l) (type_from_stamp_list l0) n).
rewrite (index_nth l s n def_n); auto.

rewrite length_type_from_stamp_list.
apply (index_lt l s n def_n).

rewrite dec1; simpl in |- *.
intro prefixe_hyp; inversion_clear prefixe_hyp.
elim H; intros l0 Hyp; elim Hyp; clear Hyp; intros def_L disjoint_hyp;
 rewrite def_L.
rewrite (type_from_stamp_list_app (l ++ s :: nil) l0).
rewrite (type_from_stamp_list_app l (s :: nil)); simpl in |- *.
rewrite
 (nth_app (type_from_stamp_list l ++ Var s :: nil) 
    (type_from_stamp_list l0) (length l)).
rewrite <- (length_type_from_stamp_list l).
rewrite (nth_app_cons (type_from_stamp_list l) (Var s)); auto.

rewrite length_app_cons; rewrite length_type_from_stamp_list; auto.

(*Arrow t1 t2*)
intros t1 ind1 t2 ind2 l L.
rewrite fst_gen_aux_arrow_rewrite; rewrite snd_gen_aux_arrow_rewrite.
intro prefixe_hyp; simpl in |- *.
rewrite (ind1 l L); eauto.
rewrite (ind2 (snd (gen_aux t1 env l)) L); auto.
Qed.


Lemma gen_t_env_more_general_than_t :
 forall (env : environment) (t : type),
 more_general (gen_type t env) (type_to_type_scheme t).
Proof.
intros; apply more_general_intro; intros.
generalize (gen_instance_type_to_type_scheme_inv t t0 H).
intro t_t0; rewrite t_t0.
apply gen_instance_intro.
unfold gen_type in |- *.
exists (type_from_stamp_list (snd (gen_aux t env nil))).
apply t_is_l_gen_aux; auto.
Qed.






Lemma map_plus2_rwt :
 forall (l : list stamp) (n m : nat),
 index l (Stamp n) = index (map_plus2 l m) (Stamp (m + n)).
simple induction l; auto.

intro a; elim a; intros; simpl in |- *.
elim (eq_nat_dec n0 n); intro n0_is_n.
rewrite n0_is_n.
do 2 (rewrite eq_nat_reflexivity; simpl in |- *).
auto.

rewrite eq_nat_diff; auto.
simpl in |- *.
rewrite eq_nat_diff.
simpl in |- *; rewrite (H n0 m); auto.

apply eq_nat_plus; auto.
Qed.

Lemma app_map_plus2 :
 forall (l1 l2 : list stamp) (m : nat),
 map_plus2 (l1 ++ l2) m = map_plus2 l1 m ++ map_plus2 l2 m.
simple induction l1; auto.

simpl in |- *; intros; elim a; intro p.
simpl in |- *; rewrite H; auto.
Qed.

Lemma length_map_plus :
 forall (l : list stamp) (n m : nat), length l = length (map_plus2 l m).
simple induction l; auto.
intros; simpl in |- *.
elim a; intro k; simpl in |- *; auto.
Qed.

Lemma gen_fresh_aux :
 forall (env : environment) (ts : type_scheme) (m p : nat) 
   (t : type) (l : list stamp),
 new_tv_env env (Stamp m) ->
 is_subset_list_stamp (FV_type_scheme ts) (FV_env env) ->
 max_gen_vars ts <= p ->
 apply_subst_gen (fst (compute_generic_subst (Stamp m) p)) ts =
 Some_subst_gen t ->
 {ts'_x : type_scheme * list stamp |
 bind_aux nil ts (turn B l) = (fst ts'_x, turn B (snd ts'_x)) /\
 gen_aux t env (map_plus2 l m) = (fst ts'_x, map_plus2 (snd ts'_x) m)}.
simple induction ts.
simpl in |- *; intros st p t l new_tv_hyp subset_hyp hyp_le def_t.
inversion_clear def_t.
exists (Nat_ts, l); auto.

simpl in |- *; intros s st p t l new_tv_hyp subset_hyp hyp_le def_t.
inversion_clear def_t; simpl in |- *.
exists (Var_ts s, l).
inversion_clear subset_hyp; rewrite H; auto.

intro s; elim s; intros n m p t l new_tv_hyp subset_hyp hyp_le.
unfold apply_subst_gen at 1 in |- *.
rewrite (nth_compute p n m); auto.
intro def_t; inversion_clear def_t; simpl in |- *.
generalize (new_tv_env_plus env m n new_tv_hyp).
intro Hyp_cut; rewrite Hyp_cut; simpl in |- *.
rewrite (index_var_turn_B2 l (Stamp n)); rewrite (length_turn B l).
rewrite <- (map_plus2_rwt l n m).
elim (index l (Stamp n)); simpl in |- *.
exists (Gen_var (Stamp (length l)), l ++ Stamp n :: nil); simpl in |- *.
rewrite <- app_turn; rewrite app_map_plus2; simpl in |- *;
 rewrite <- (length_map_plus l n m); auto.

intro n0; exists (Gen_var (Stamp n0), l); auto.

intros ts1 ind1 ts2 ind2 m p t l new_tv_hyp subset_hyp hyp_le def_t.
elim
 (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 t
    (fst (compute_generic_subst (Stamp m) p)) def_t).
intro x; elim x; clear x; do 2 intro.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro t_rwt; rewrite t_rwt.
simpl in hyp_le; simpl in subset_hyp.
elim (ind1 m p a l); auto.
intro x; elim x; clear x; intros sigma1 l1 hyp1; elim hyp1; clear hyp1.
intros bind1 gen1; simpl in |- *.
rewrite bind1; rewrite gen1; simpl in |- *.
elim (ind2 m p b l1); auto.
intro x; elim x; clear x; intros sigma2 l2 hyp2; elim hyp2; clear hyp2;
 intros bind2 gen2.
rewrite bind2; rewrite gen2; simpl in |- *.
exists (Arrow_ts sigma1 sigma2, l2); auto.

apply subset_of_union_inversion2 with (l1 := FV_type_scheme ts1); auto.

apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.

apply subset_of_union_inversion1 with (l2 := FV_type_scheme ts2); auto.

apply le_trans with (m := max (max_gen_vars ts1) (max_gen_vars ts2)); auto.
Qed.





(***************************************************************************)
(*               (are_disjoints l (FV_env env)) ->                         *)
(*               (more_general (gen_type t env) ts) ->                     *)
(*                    (more_general (gen_type t env) (bind_list l ts)).    *)
(***************************************************************************)


Fixpoint sg_bind_l_split (sg : list type) (L : list V) 
 (l : list stamp) {struct L} : Exc (list type * substitution) :=
  match L with
  | nil => value (nil, empty_subst)
  | v :: y =>
      match sg with
      | nil => error (A:=list type * substitution)
      | t :: x =>
          match sg_bind_l_split x y l with
          | None => error (A:=list type * substitution)
          | Some (sg', phi) =>
              match v with
              | F s =>
                  if_ (Exc (list type * substitution)) 
                    (in_list_stamp s l) (value (sg', (s, t) :: phi)) error
              | B s => value (t :: sg', phi)
              end
          end
      end
  end.


Fixpoint filter_B (l : list V) : list V :=
  match l with
  | nil => nil (A:=V)
  | x :: y => match x with
              | B s => x :: filter_B y
              | _ => filter_B y
              end
  end.

(**************************************************************)

Lemma index_var_cons_k_inv :
 forall (s0 s : stamp) (k : nat) (l : list V),
 index_var (B s0 :: l) (F s) = Index_in k ->
 {p : nat | k = S p /\ index_var l (F s) = Index_in p}.
Proof.
unfold index_var in |- *; intros s0 s k l; case k; simpl in |- *.
elim (index_new V eq_V l (F s)).
intro pb; discriminate pb.

do 2 intro; inversion_clear H.

elim (index_new V eq_V l (F s)).
intros n pb; discriminate pb.

intros n n0 n0_n; inversion_clear n0_n.
exists n0; auto.
Qed.


Lemma index_var_cons_k_inv2 :
 forall (s0 s : stamp) (k : nat) (l : list V),
 index_var (F s0 :: l) (B s) = Index_in k ->
 {p : nat | k = S p /\ index_var l (B s) = Index_in p}.
Proof.
unfold index_var in |- *; intros s0 s k l; case k; simpl in |- *.
elim (index_new V eq_V l (B s)).
intro pb; discriminate pb.

do 2 intro; inversion_clear H.

elim (index_new V eq_V l (B s)).
intros n pb; discriminate pb.

intros n n0 n0_n; inversion_clear n0_n.
exists n0; auto.
Qed.


(*************************************************************************)

Lemma sg_bind_l_split2 :
 forall (l1 l0 : list V) (sg sg' : list type) (s : stamp) 
   (t : type) (phi : substitution) (k : nat) (binds : list stamp),
 index_var l1 (F s) = Index_in k ->
 nth k sg = Nth_in t ->
 sg_bind_l_split sg (l1 ++ l0) binds = value (sg', phi) ->
 apply_substitution phi s = t.
Proof.
simple induction l1.
(*l1=nil*)
do 8 intro; unfold index_var in |- *; simpl in |- *.
intro pb; discriminate pb.

(*l1=a::l*)
intros a l ind_hyp l0 sg sg' s t phi k binds; simpl in |- *.
case sg.
(*sg=nil*)simpl in |- *; intros index_hyp pb; discriminate pb.
(*sg=t0::l0*)
intros t0 l2; simpl in |- *.
elim
 (exc_dec (list type * substitution) (sg_bind_l_split l2 (l ++ l0) binds));
 intro hyp.
(***)elim hyp; intro x; clear hyp; elim x; intros sg1 phi1 def_sg1_phi1;
      rewrite def_sg1_phi1.
case a; intro s0. 
(*a=B s0*)
intro index_hyp.
elim (index_var_cons_k_inv s0 s k l index_hyp).
intros p Hyp; elim Hyp; clear Hyp; intros def_k index_hyp_l; rewrite def_k.
intros nth_hyp def_rec; injection def_rec; intros phi1_eq_phi sg'_eq_cons_sg1.
rewrite <- phi1_eq_phi.
rewrite (ind_hyp l0 l2 sg1 s t phi1 p binds); auto.

(*a=F s0*)
elim (bool_dec (in_list_stamp s0 binds)); intro test; rewrite test;
 simpl in |- *.
  (*(in_list_stamp s binds)=true*)
elim (stamp_dec s0 s); unfold index_var in |- *; simpl in |- *; intro s_eq_s0.
 (**s=s0*)rewrite s_eq_s0; rewrite eq_stamp_reflexivity; simpl in |- *.
intro O_k; inversion_clear O_k.
intro t0_t; inversion_clear t0_t.
intro def_sg'_phi; inversion_clear def_sg'_phi.
apply apply_subst_cons.
 (**s<>s0*)rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new V eq_V l (F s))); intro index_dec.
(****)elim index_dec; intros p def_p; rewrite def_p; intro def_k.
inversion_clear def_k.
intros nth_hyp def_sg'_phi.
injection def_sg'_phi.
intros def_phi def_sg'; rewrite <- def_phi.
rewrite apply_subst_cons2; auto.
apply (ind_hyp l0 l2 sg1 s t phi1 p binds); auto.
(****)rewrite index_dec; intro pb; discriminate pb.

  (*(in_list_stamp s binds)=false*)
intros index_hyp nth_hyp pb; discriminate pb.

(***)rewrite hyp; intros index_hyp nth_hyp pb; discriminate pb.
Qed.


Lemma filter_B_app :
 forall l1 l2 : list V, filter_B (l1 ++ l2) = filter_B l1 ++ filter_B l2.
simple induction l1; auto.
intros; simpl in |- *; case a; intro s; auto.
simpl in |- *; rewrite H; auto.
Qed.

(*************************************************************************)

Lemma domain_split_l_included_in_l :
 forall (l : list stamp) (L : list V) (sg sg' : list type)
   (phi : substitution),
 sg_bind_l_split sg L l = value (sg', phi) ->
 is_subset_list_stamp (domain_of_substitution phi) l.
Proof.
simple induction L.
simpl in |- *; intros; inversion_clear H; auto.

intros a lo ind_hyp sg sg' phi; simpl in |- *.
case sg; simpl in |- *.
intro pb; discriminate pb.

intros l1 sg0.
(**)elim (exc_dec (list type * substitution) (sg_bind_l_split sg0 lo l));
     intro hyp.
elim hyp; intro x; clear hyp; elim x; intros sg1 phi1 def_sg1_phi1;
 rewrite def_sg1_phi1.
case a; intro s0.
intro def_sg'_phi; injection def_sg'_phi.
intros phi_is_phi1 def_sg'; rewrite <- phi_is_phi1.
apply (ind_hyp sg0 sg1 phi1); auto.

elim (bool_dec (in_list_stamp s0 l)); intro test; rewrite test; simpl in |- *;
 intros def_sg'_phi.
(***)injection def_sg'_phi; intros def_sg' def_phi1; rewrite <- def_sg';
      simpl in |- *.
apply subset_cons_inv; auto.
apply (ind_hyp sg0 sg1 phi1); auto.

(***)discriminate def_sg'_phi.

(**)rewrite hyp; intro pb; discriminate pb.
Qed.
Hint Resolve domain_split_l_included_in_l.

Lemma subset_inv2 :
 forall (l1 l2 : list stamp) (st : stamp),
 is_subset_list_stamp l1 l2 ->
 in_list_stamp st l2 = false -> in_list_stamp st l1 = false.
intros; inversion_clear H.
elim (bool_dec (in_list_stamp st l1)); auto.
intro y; generalize (H1 st y); rewrite H0; intro pb; discriminate pb.
Qed.


Lemma sg_bind_l_split_sg' :
 forall (l : list stamp) (s : stamp) (l1 : list V) 
   (sg sg' : list type) (phi : substitution) (k p : nat) 
   (t : type),
 sg_bind_l_split sg l1 l = value (sg', phi) ->
 index_var l1 (B s) = Index_in k ->
 nth k sg = Nth_in t ->
 index_var (filter_B l1) (B s) = Index_in p -> nth p sg' = Nth_in t.
simple induction l1.
simpl in |- *; intros sg sg' phi k p t def_sg'_phi;
 inversion_clear def_sg'_phi.
unfold index_var in |- *; simpl in |- *; intro pb; discriminate pb.

intros a l0 ind_hyp sg sg' phi k p t; simpl in |- *.
case sg.
intro pb; discriminate pb.

intros t0 sg0.
(**)elim (exc_dec (list type * substitution) (sg_bind_l_split sg0 l0 l));
     intro hyp.
elim hyp; intro x; clear hyp; elim x; intros sg1 phi1 def_sg1_phi1;
 rewrite def_sg1_phi1.
case a; intro s0.
intro def_sg'_phi; injection def_sg'_phi.
intros phi_is_phi1 def_sg'; rewrite <- def_sg'.
elim (stamp_dec s0 s); unfold index_var in |- *; simpl in |- *; intro s_eq_s0.
 (**s=s0*)rewrite s_eq_s0; rewrite eq_stamp_reflexivity; simpl in |- *.
intro O_k; injection O_k; intro k_is_O; rewrite <- k_is_O.
intro t0_t; injection t0_t; intro t_is_t0; rewrite <- t_is_t0.
intro O_p; inversion_clear O_p; auto.
 (**s<>s0*)rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new V eq_V l0 (B s))); intro index_dec.
(****)elim index_dec; intros j1 def_j1; rewrite def_j1; intro def_k.
inversion_clear def_k.
intro nth_hyp.
(*Rewrite <- def_sg'.*)
(*****)elim (index_answer_dec (index_new V eq_V (filter_B l0) (B s)));
        intro index_dec2.
elim index_dec2; intros p1 def_p1; rewrite def_p1; simpl in |- *; intro def_p.
inversion_clear def_p.
apply (ind_hyp sg0 sg1 phi1 j1 p1); auto.

(*****)rewrite index_dec2; intro pb; discriminate pb.

(****)rewrite index_dec; intro pb; discriminate pb.

elim (bool_dec (in_list_stamp s0 l)); intro test; rewrite test; simpl in |- *.
intro def_sg'_phi; injection def_sg'_phi; intros def_phi def_sg' index_hyp;
 rewrite <- def_sg'.
elim (index_var_cons_k_inv2 s0 s k l0 index_hyp).
intros j Hyp; elim Hyp; clear Hyp; intros def_k index_hyp_l; rewrite def_k.
intros nth_hyp def_rec.
apply (ind_hyp sg0 sg1 phi1 j p t); auto.

intro pb; discriminate pb.

rewrite hyp; intro pb; discriminate pb.
Qed.

(********************************************************************)
Lemma index_var_inv :
 forall (l1 : list V) (k : nat) (s : stamp),
 index_var (filter_B l1) (B s) = Index_in k ->
 {p : nat | index_var l1 (B s) = Index_in p}.
unfold index_var in |- *; simple induction l1.
simpl in |- *; intros; discriminate H.

intros a l ind_hyp k s.
case a; intros s0.
simpl in |- *; elim (stamp_dec s s0); intro eq_s_s0.
rewrite eq_s_s0; rewrite eq_stamp_reflexivity; simpl in |- *; intros.
inversion_clear k; exists 0; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new V eq_V (filter_B l) (B s))); intro dec.
elim dec; intros p def_p; rewrite def_p; intro def_k; inversion_clear def_k.
elim (ind_hyp p s def_p).
intros m def_m; rewrite def_m.
exists (S m); auto.

rewrite dec; intro pb; discriminate pb.

simpl in |- *; intro index_hyp.
elim (ind_hyp k s index_hyp).
intros p def_p; simpl in |- *; rewrite def_p.
exists (S p); auto.

Qed.

Lemma index_var_B_inv2 :
 forall (l1 : list V) (s : stamp),
 index_var (filter_B l1) (B s) = Stamp_not_in ->
 index_var l1 (B s) = Stamp_not_in.
unfold index_var in |- *; simple induction l1; auto.

intros a l ind_hyp s; simpl in |- *.
case a; intro s0; simpl in |- *.
elim (stamp_dec s s0); intro eq_s_s0.
rewrite eq_s_s0; rewrite eq_stamp_reflexivity; simpl in |- *; intros;
 discriminate H.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new V eq_V (filter_B l) (B s))); intros dec.
elim dec; intros p def_p; rewrite def_p; intro pb; discriminate pb.

rewrite (ind_hyp s dec); rewrite dec; auto.

intro dec; rewrite (ind_hyp s dec); auto.
Qed.

Lemma index_var_filter_B_inv :
 forall (l1 : list V) (k : nat) (s : stamp),
 index_var l1 (B s) = Index_in k ->
 {p : nat | index_var (filter_B l1) (B s) = Index_in p}.
unfold index_var in |- *; simple induction l1.
simpl in |- *; intros; discriminate H.

intros a l ind_hyp k s.
case a; intros s0.
simpl in |- *.
elim (stamp_dec s s0); intros eq_s_s0.
rewrite eq_s_s0; rewrite eq_stamp_reflexivity; simpl in |- *; intros.
inversion_clear k; exists 0; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new V eq_V l (B s))); intro dec.
elim dec; intros p def_p; rewrite def_p; intro def_k; inversion_clear def_k.
elim (ind_hyp p s def_p).
intros m def_m; rewrite def_m.
exists (S m); auto.

rewrite dec; intro pb; discriminate pb.

intro index_hyp.
elim (index_var_cons_k_inv2 s0 s k l index_hyp).
intros m hyp; elim hyp; clear hyp; intros def_k index_hyp2.
elim (ind_hyp m s index_hyp2).
intros j hyp.
exists j; auto.
Qed.

Lemma index_var_filter_B_inv2 :
 forall (l1 : list V) (s : stamp),
 index_var l1 (B s) = Stamp_not_in ->
 index_var (filter_B l1) (B s) = Stamp_not_in.
unfold index_var in |- *; simple induction l1; auto.

intros a l ind_hyp s; simpl in |- *.
case a; intro s0; simpl in |- *.
elim (stamp_dec s s0); intro eq_s_s0.
rewrite eq_s_s0; rewrite eq_stamp_reflexivity; simpl in |- *; intros;
 discriminate H.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new V eq_V l (B s))); intros dec.
elim dec; intros p def_p; rewrite def_p; intro def_k; inversion_clear def_k.

rewrite (ind_hyp s dec); rewrite dec; auto.

elim (index_answer_dec (index_new V eq_V l (B s))); intro dec.
elim dec; intros p def_p; rewrite def_p; intro pb; discriminate pb.

rewrite dec; auto.
Qed.

(***********************************************************************)
Lemma bind_dec :
 forall v : type_scheme * list V, {ts_L : type_scheme * list V | ts_L = v}.
intro v; elim v; intros t l; exists (t, l); auto.
Qed.


Lemma bind_aux_filter_B :
 forall (ts1 : type_scheme) (l1 : list V) (l : list stamp),
 snd (bind_aux nil ts1 (filter_B l1)) = filter_B (snd (bind_aux l ts1 l1)).
simple induction ts1; auto.

simpl in |- *; intros.
elim (bool_dec (in_list_stamp s l)); intro test; rewrite test; simpl in |- *;
 auto.
elim (index_var l1 (F s)); simpl in |- *; auto.
rewrite filter_B_app; simpl in |- *; apply app_nil_end.

simpl in |- *; intros.
elim (index_answer_dec (index_var (filter_B l1) (B s))); intro dec.
elim dec; intros p def_p; rewrite def_p; simpl in |- *.
elim (index_var_inv l1 p s def_p).
intros k def_k; rewrite def_k; auto.

rewrite dec.
rewrite (index_var_B_inv2 l1 s dec).
simpl in |- *; rewrite filter_B_app; auto.

intros; do 2 rewrite Snd_bind_aux_arrow_rwt.
rewrite (H l1 l).
rewrite (H0 (snd (bind_aux l t l1)) l); auto.
Qed.

(****************************************************************************)

Lemma bind_l_split2 :
 forall (ts : type_scheme) (l : list stamp) (l1 L : list V) 
   (tau : type) (sg sg' : list type) (phi : substitution),
 apply_subst_gen sg (fst (bind_aux l ts l1)) = Some_subst_gen tau ->
 is_prefixe (snd (bind_aux l ts l1)) L ->
 sg_bind_l_split sg L l = value (sg', phi) ->
 apply_subst_gen sg'
   (extend_subst_type_scheme phi (fst (bind_aux nil ts (filter_B l1)))) =
 Some_subst_gen tau.
Proof.
simple induction ts; auto.

(*Var s*)
do 8 intro; simpl in |- *.
elim (bool_dec (in_list_stamp s l)); intro s_in_l; rewrite s_in_l;
 simpl in |- *.
(*(in_list_stamp s l)=true*)
(**)elim (index_answer_dec (index_var l1 (F s))); intro hyp_dec.
elim hyp_dec; intros k def_k; rewrite def_k; simpl in |- *.
(***)elim (nth_answer_inv (nth k sg)); intro hyp_dec2.
elim hyp_dec2; intros t def_t; rewrite def_t; simpl in |- *; intro t_tau;
 injection t_tau; intro t_eq_tau; rewrite <- t_eq_tau.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L.
rewrite def_L; intro; rewrite apply_subst_gen_type_to_type_scheme.
rewrite (sg_bind_l_split2 l1 l0 sg sg' s t phi k l); auto.
(***)rewrite hyp_dec2; simpl in |- *; intro pb; discriminate pb.

(**)rewrite hyp_dec; simpl in |- *.
(***)elim (nth_answer_inv (nth (length l1) sg)); simpl in |- *.
intro hyp; elim hyp; intros t def_t; rewrite def_t; simpl in |- *.
intro t_is_tau; injection t_is_tau; intro t_tau; rewrite <- t_tau.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L.
rewrite def_L; intro; rewrite apply_subst_gen_type_to_type_scheme.
rewrite (sg_bind_l_split2 (l1 ++ F s :: nil) l0 sg sg' s t phi (length l1) l);
 auto.
(*Unfold index_var;Apply index_new_app_cons;Auto.*)
apply index_V_app_cons; auto.

(***)intro hyp; rewrite hyp; simpl in |- *; intro pb; discriminate pb.

(*(in_list_stamp s l)=false*)
intros Var_s_tau; inversion_clear Var_s_tau.
rewrite apply_subst_gen_type_to_type_scheme.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L.
intro; rewrite is_not_in_domain_subst; auto.
apply (subset_inv2 (domain_of_substitution phi) l s); eauto.

(*Gen_var s*)
do 8 intro; simpl in |- *.
(**)elim (index_answer_dec (index_var l1 (B s))); intro hyp_dec.
elim hyp_dec; intros k def_k; rewrite def_k; simpl in |- *.
(***)elim (nth_answer_inv (nth k sg)); intro hyp_dec2.
elim hyp_dec2; intros t def_t; rewrite def_t; simpl in |- *; intro t_tau;
 injection t_tau; intro t_eq_tau; rewrite <- t_eq_tau.
intro prefixe_hyp; inversion_clear prefixe_hyp; elim H; clear H;
 intros l0 def_L.
rewrite def_L; intro.
elim (index_var_filter_B_inv l1 k s def_k).
intros p def_p; rewrite def_p; simpl in |- *.
rewrite (sg_bind_l_split_sg' l s (l1 ++ l0) sg sg' phi k p t); auto.
(*Unfold index_var; Apply index_new_app; Auto.*)
apply index_V_app; auto.

(*Unfold index_var; Rewrite filter_B_app;Apply index_new_app; Auto.*)
rewrite filter_B_app; apply index_V_app; auto.

(***)rewrite hyp_dec2; simpl in |- *; intro pb; discriminate pb.

(**) generalize (index_var_filter_B_inv2 l1 s hyp_dec).
intro hyp_index_filter; rewrite hyp_index_filter.
rewrite hyp_dec; simpl in |- *.
(***)elim (nth_answer_inv (nth (length l1) sg)); intro hyp_dec2.
elim hyp_dec2; intros t def_t; rewrite def_t.
intro t_tau; injection t_tau; intro t_is_tau; rewrite <- t_is_tau.
intro hyp_prefixe; inversion_clear hyp_prefixe.
elim H; intros l2 def_L; rewrite def_L; intro def_sg'_phi.
rewrite
 (sg_bind_l_split_sg' l s ((l1 ++ B s :: nil) ++ l2) sg sg' phi 
    (length l1) (length (filter_B l1)) t); auto.
(*Unfold index_var; Apply index_new_app.*)
apply index_V_app.
(*Apply index_new_app_cons;Auto.*)
apply index_V_app_cons; auto.

(*Unfold index_var; *)
rewrite filter_B_app; rewrite filter_B_app.
(*Apply index_new_app;Simpl.*)
apply index_V_app; simpl in |- *.
(*Apply index_new_app_cons; Auto.*)
apply index_V_app_cons; auto.

(***)rewrite hyp_dec2; intro pb; discriminate pb.

(*Arrow_ts ts1 ts2*)
intros ts1 hyp_ind1 ts2 hyp_ind2 l l1 L tau sg sg' phi.
do 2 rewrite bind_aux_arrow_rwt.
intro apply_subst_gen_hyp.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (fst (bind_aux l ts1 l1))
    (fst (bind_aux l ts2 (snd (bind_aux l ts1 l1)))) tau sg
    apply_subst_gen_hyp).
intro x; elim x; clear x; do 2 intro.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro tau_rwt; rewrite tau_rwt.
rewrite Snd_bind_aux_arrow_rwt.
intros prefixe_hyp def_sg'_phi; simpl in |- *.
rewrite (hyp_ind1 l l1 L a sg sg' phi); eauto.
rewrite (bind_aux_filter_B ts1 l1 l).
rewrite (hyp_ind2 l (snd (bind_aux l ts1 l1)) L b sg sg' phi); auto.
Qed.

(****************************************************************************)
Definition valid_list_V (L : list V) (l : list stamp) :=
  forall s : stamp, In (F s) L -> in_list_stamp s l = true.


Lemma valid_bind_aux :
 forall (l : list stamp) (ts : type_scheme) (L : list V),
 valid_list_V L l -> valid_list_V (snd (bind_aux l ts L)) l.

unfold valid_list_V in |- *; simple induction ts; auto.
do 4 intro; simpl in |- *.
elim (bool_dec (in_list_stamp s l)); intros test; rewrite test; simpl in |- *.
elim (index_var L (F s)); simpl in |- *; intros.
(* Elim (in_app_or V L (cons (F s) (nil V)) (F s0) H0);Intro;Auto.*)
elim (in_app_or _ _ _ H0); intro; auto.
unfold In in H1; elim H1.
intro Fs_is_Fs0; injection Fs_is_Fs0; intros s_is_s0; rewrite <- s_is_s0;
 auto.
intro; elim H2.

auto.

auto.

do 4 intro; simpl in |- *.
elim (index_var L (B s)); simpl in |- *.
intro.
(*Elim (in_app_or V L (cons (B s) (nil V)) (F s0) H0);Intro;Auto.*)
elim (in_app_or _ _ _ H0); intro; auto.
unfold In in H1; elim H1.
intros Fs_is_Fs0; discriminate Fs_is_Fs0.

intro; elim H2.

auto.

do 7 intro.
rewrite Snd_bind_aux_arrow_rwt; intro.
apply (H0 (snd (bind_aux l t L))); auto.
intros; apply (H L H1 s0); auto.
Qed.

(****************************************************************************)
Lemma valid_cons :
 forall (l : list stamp) (L0 : list V) (a : V),
 valid_list_V (a :: L0) l -> valid_list_V L0 l.
unfold valid_list_V in |- *; simpl in |- *; intros; auto.
Qed.

(************************************************************************)
Lemma domain_of_sg_bind_l_split :
 forall (l : list stamp) (L : list V) (sg : list type),
 length L <= length sg ->
 valid_list_V L l ->
 {sg'_phi : list type * substitution |
 sg_bind_l_split sg L l = value sg'_phi}.
simple induction L.

intros; exists (@nil type, empty_subst); auto.

intros a L0 ind_hyp sg.
case sg; simpl in |- *.
simpl in |- *; intro le_hyp.
absurd (S (length L0) <= 0); auto with *.

intros t0 sg0 le_hyp valid_hyp.
elim
 (ind_hyp sg0 (le_S_n (length L0) (length sg0) le_hyp)
    (valid_cons l L0 a valid_hyp)).
intro x; elim x; clear x; intros sg' phi' def_sg'_phi'; rewrite def_sg'_phi'.
generalize valid_hyp.
case a; intros s valid_hyp0.
exists (t0 :: sg', phi'); auto.

unfold valid_list_V in valid_hyp0; rewrite (valid_hyp0 s); simpl in |- *;
 auto.
exists (sg', (s, t0) :: phi'); auto.
Qed.
(************************************************************************)


Lemma length_Snd_bind_aux :
 forall (l : list stamp) (ts : type_scheme) (L : list V),
 length (snd (bind_aux l ts L)) =
 max (length L) (max_gen_vars (fst (bind_aux l ts L))).
(* cf length_Snd_gen_aux *)
simple induction ts; auto.

(*Var_ts*)
simpl in |- *; intros.
elim (bool_dec (in_list_stamp s l)); intro y; rewrite y; simpl in |- *.
elim (index_answer_dec (index_var L (F s))); intro hyp_dec.
elim hyp_dec; intros n def_n; rewrite def_n; simpl in |- *.
rewrite max_rew1; auto.
change (n < length L) in |- *.
unfold index_var in def_n.
apply (index_V_lt L (F s) n def_n).

rewrite hyp_dec; simpl in |- *; rewrite max_n_S_n; rewrite length_app; auto.

auto.

(*Gen_var*)
simpl in |- *; intros.
elim (index_answer_dec (index_var L (B s))); intro hyp_dec.
elim hyp_dec; intros n def_n; rewrite def_n; simpl in |- *.
rewrite max_rew1; auto.
change (n < length L) in |- *.
unfold index_var in def_n.
apply (index_V_lt L (B s) n def_n).

rewrite hyp_dec; simpl in |- *; rewrite max_n_S_n; rewrite length_app; auto.

(*Arrow_ts*)
intros ts1 ind1 ts2 ind2 L.
rewrite bind_aux_arrow_rwt; rewrite Snd_bind_aux_arrow_rwt.
simpl in |- *.
rewrite max_ass.
rewrite <- ind1; rewrite <- ind2; auto.
Qed.

(************************************************************************)
Lemma sg_bind_l_split_exists :
 forall (sg : list type) (ts : type_scheme) (l : list stamp),
 max_gen_vars (bind_list l ts) <= length sg ->
 {sg'_phi : list type * substitution |
 sg_bind_l_split sg (snd (bind_aux l ts nil)) l = value sg'_phi}.
unfold bind_list in |- *; intros.
apply domain_of_sg_bind_l_split.
rewrite length_Snd_bind_aux; auto.

replace  (@length V (@nil V)) with 0; auto.
rewrite max_commutes; rewrite <- max_O; auto.

apply valid_bind_aux; auto.
unfold valid_list_V in |- *; simpl in |- *.
intros; elim H0.
Qed.
(* cf product_list_exists *)

(************************************************************************)

(************************************************************************)
Lemma FV_gen_t_env_included_in_env :
 forall (env : environment) (t : type) (l : list stamp),
 is_subset_list_stamp (FV_type_scheme (fst (gen_aux t env l))) (FV_env env).
simple induction t; auto.

(*Var s*)
intros s l; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro test; rewrite test;
 simpl in |- *.
apply subset_cons_inv; auto.
elim (index l s); auto.

(*Arrow t1 t2*)
intros t1 ind1 t2 ind2 l.
rewrite fst_gen_aux_arrow_rewrite; simpl in |- *.
apply union_subset; auto.
Qed.


Lemma gen_more_general_than_bind :
 forall (ts : type_scheme) (l : list stamp) (t : type) (env : environment),
 are_disjoints l (FV_env env) ->
 more_general (gen_type t env) ts ->
 more_general (gen_type t env) (bind_list l ts).
Proof.
intros ts l t env disjoint_hyp more_gen_hyp; unfold bind_list in |- *;
 apply more_general_intro.
intros tau tau_is_instance.
inversion_clear tau_is_instance.
elim H; clear H; intros sg def_tau.
elim (sg_bind_l_split_exists sg ts l); eauto.
intro x; elim x; clear x; intros sg' phi def_sg_bind_l_split.
generalize
 (bind_l_split2 ts l nil (snd (bind_aux l ts nil)) tau sg sg' phi def_tau
    (is_prefixe_reflexivity (snd (bind_aux l ts nil))) def_sg_bind_l_split).
simpl in |- *;
 change
   (apply_subst_gen sg' (extend_subst_type_scheme phi (bind_list nil ts)) =
    Some_subst_gen tau -> is_gen_instance tau (gen_type t env)) 
  in |- *.
intro new_def_tau.
cut (is_gen_instance tau (extend_subst_type_scheme phi (bind_list nil ts))).
intro tau_instance_of_phi_gen_t.
generalize
 (more_general_preserves_subst (gen_type t env) (bind_list nil ts) phi
    (more_general_trans (gen_type t env) ts (bind_list nil ts) more_gen_hyp
       (ts_more_gen_then_bind_nil ts))).
intro more_gen_cut.
inversion_clear more_gen_cut.
generalize (H tau tau_instance_of_phi_gen_t).
(*   (is_gen_instance tau (extend_subst_type_scheme phi (gen_type t env)))
    ->(is_gen_instance tau (gen_type t env))
*)
rewrite s_ts_when_s_disjoint_with_ts; auto.
apply disjoint_subset_bis with (l2 := FV_env env).
apply disjoint_subset_bis with (l2 := l); eauto.
unfold gen_type in |- *; apply FV_gen_t_env_included_in_env.

apply gen_instance_intro; exists sg'; auto.

Qed.




Lemma complete :
 forall (env : environment) (e : expr) (ts : type_scheme),
 type_of_DM env e ts -> G env e ts.
simple induction 1.

intros; apply intro_G.
exists Nat; unfold gen_type in |- *; auto.

(**)
intros.
elim (exists_st_new_tv_env env0).
intro st; elim st; intros m new_tv_hyp.
elim (apply_compute_generic_subst (Stamp m) ts0 (max_gen_vars ts0)); auto.
intros t def_t.
apply intro_G; exists t; split.
apply
 (type_of_var env0 x t ts0 H0
    (compute_generic_subst_create_generic_instance ts0 (Stamp m) t def_t)).
unfold gen_type in |- *.
elim (gen_fresh_aux env0 ts0 m (max_gen_vars ts0) t nil); eauto.
intro x0; elim x0; clear x0; simpl in |- *; intros y y0 y1; elim y1; clear y1;
 intros.
rewrite H2.
simpl in |- *.
change (more_general (fst (y, turn B y0)) ts0) in |- *.
rewrite <- H1.
change (more_general (bind_list nil ts0) ts0) in |- *.
apply bind_l_ts_more_gen_than_ts.

(**)
intros; inversion_clear H1; elim H3; intros t Hyp; elim Hyp; clear Hyp;
 intros.
apply intro_G; exists t.
split; auto.
apply more_general_trans with (ts2 := ts0); auto.

(**)
intros; inversion_clear H1; elim H3; intros t Hyp; elim Hyp; clear Hyp;
 intros.
apply intro_G; exists t.
split; auto.
apply gen_more_general_than_bind; auto.

(**)
simpl in |- *; intros; inversion_clear H1; elim H2; intros t1 Hyp; elim Hyp;
 clear Hyp; intros.
apply intro_G; exists (Arrow t t1).
split.
apply type_of_lambda; auto.
apply
 more_general_trans
  with
    (ts2 := gen_type (Arrow t t1)
              (add_environment env0 x (type_to_type_scheme t))).
apply more_general_gen_add.

unfold gen_type in |- *.
rewrite fst_gen_aux_arrow_rewrite.
rewrite is_not_generalizable_aux; auto.
simpl in |- *.
apply more_general_intro; intro.
change
  (is_gen_instance t0 (type_to_type_scheme (Arrow t t')) ->
   is_gen_instance t0
     (Arrow_ts (type_to_type_scheme t)
        (fst
           (gen_aux t1 (add_environment env0 x (type_to_type_scheme t)) nil))))
 in |- *.
intro t0_gen_instance_of.
generalize
 (gen_instance_type_to_type_scheme_inv (Arrow t t') t0 t0_gen_instance_of).
intro def_t0; rewrite def_t0.
inversion_clear H3.
generalize (H4 t' (gen_instance_type_to_type_scheme t')).
intro t'_gen_instance_of; inversion_clear t'_gen_instance_of.
elim H3; intros sg t'_is_sg_gen_t1_add.
unfold gen_type in t'_is_sg_gen_t1_add.
apply gen_instance_intro.
exists sg; simpl in |- *.
rewrite (apply_subst_gen_type_to_type_scheme sg t).
rewrite t'_is_sg_gen_t1_add; auto.

(**)
simpl in |- *; intros; inversion_clear H1; elim H2; intros t1 Hyp; elim Hyp;
 clear Hyp; intros.
apply intro_G; exists (Arrow t t').
split.
apply type_of_rec_fun.
apply type_of_type_to_type_scheme with (t1 := t1); auto.

change
  (more_general (gen_type (Arrow t t') env0)
     (type_to_type_scheme (Arrow t t'))) in |- *.
apply gen_t_env_more_general_than_t.

(**)
simpl in |- *; intros; inversion_clear H1; elim H4; clear H4; intros t1 Hyp1;
 elim Hyp1; clear Hyp1; intros.
inversion_clear H3; elim H5; clear H5; intros t2 Hyp2; elim Hyp2; clear Hyp2;
 intros.
apply intro_G; exists t'.
split.
apply type_of_app with (t := t).
apply type_of_type_to_type_scheme with (t1 := t1); auto.

apply type_of_type_to_type_scheme with (t1 := t2); auto.
apply gen_t_env_more_general_than_t.


(*let*)
simpl in |- *; intros; inversion_clear H1; elim H4; clear H4; intros t1 Hyp1;
 elim Hyp1; clear Hyp1; intros.
inversion_clear H3; elim H5; clear H5; intros t2 Hyp2; elim Hyp2; clear Hyp2;
 intros.
apply intro_G; exists t2.
split.
apply (type_of_let_in env0 e0 e' x t1 t2); auto.
(*Apply type_of_let_in with t:=t1;Auto.*)
apply typing_in_a_more_general_env with (env2 := add_environment env0 x ts0);
 auto.
apply more_general_env_add_ts; auto.
apply
 more_general_trans with (ts2 := gen_type t2 (add_environment env0 x ts0));
 auto.
apply more_general_gen_add.
Qed.


