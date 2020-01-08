(* Author : Catherine Dubois *)

Require Import List.
Require Import tools_bool.
Require Import Le.
Require Import Lt.
Require Import langs.
Require Import tools.
Require Import env_poly.
Require Import subst.
Require Import FV.
Require Import not_in_FV_env.
Require Import max.
Require Import disjoints.
Require Import generic_DB.
Require Import DB_stable_gen_instance.
Require Import DB_gen_stable.

(************************************************************************)
Inductive product_check : Set :=
  | Error_product : product_check
  | Some_product : list (stamp * type) -> product_check.

Lemma product_check_inv :
 forall v : product_check,
 {l : list (stamp * type) | v = Some_product l} + {v = Error_product}.
simple induction v; auto.

intros; left.
exists l; auto.
Qed.

(************************************************************************)

Fixpoint product_list (l1 : list stamp) (l2 : list type) {struct l1} :
 product_check :=
  match l1 return product_check with
  | nil =>
      (* *)  Some_product nil
      
      (* *) 
  | st :: l'1 =>
      match l2 return product_check with
      | nil => Error_product
      | t :: l'2 =>
          match product_list l'1 l'2 return product_check with
          | Error_product => Error_product
          | Some_product s => Some_product ((st, t) :: s)
          end
      end
  end.

(************************************************************************)

Lemma product_for_le_length :
 forall (l1 : list stamp) (l2 : list type),
 length l1 <= length l2 ->
 {s : substitution | product_list l1 l2 = Some_product s}.
simple induction l1.
(*l1=nil*)
simpl in |- *; intros; exists (nil (A:=stamp * type)); auto.

(*l1=a::l*)
intros a l ind_hyp l2.
case l2; simpl in |- *; intros.
(*l2=nil*)
absurd (S (length l) <= 0); auto with *.
(*l2=t::l0*)
generalize (ind_hyp l0 (le_S_n (length l) (length l0) H)).
intro product_list_l_l0_exists; elim product_list_l_l0_exists.
intros x x_eq; rewrite x_eq.
exists ((a, t) :: x); auto.
Qed.

(************************************************************************)

Fixpoint type_from_stamp_list (l : list stamp) : list type :=
  match l return (list type) with
  | nil => nil
  | x :: l' => Var x :: type_from_stamp_list l'
  end.

Lemma length_type_from_stamp_list :
 forall l : list stamp, length (type_from_stamp_list l) = length l.
simple induction l; auto.
intros; simpl in |- *; rewrite H; auto.
Qed.

(*********************************************************************)


Lemma nth_S_last : forall l : list type, nth (length l) l = Type_not_in.

simple induction l; auto.
Qed.
(*********************************************************************)
Lemma map_extend_subst_type_app :
 forall (s : substitution) (l : list type) (t : type),
 map_extend_subst_type (l ++ t :: nil) s =
 map_extend_subst_type l s ++ extend_subst_type s t :: nil.
Proof.
simple induction l; auto.
intros; simpl in |- *.
rewrite H; auto.
Qed.

(*********************************************************************)

Lemma index_answer_dec :
 forall v : index_answer, {n : nat | v = Index_in n} + {v = Stamp_not_in}.
simple induction v; auto.
intros; left.
exists n; auto.
Qed.
(*************************************************************************)

Lemma index_nth :
 forall (l : list stamp) (v : stamp) (k : nat),
 index l v = Index_in k -> nth k (type_from_stamp_list l) = Nth_in (Var v).
Proof.
simple induction l; simpl in |- *.
intros v k pb; discriminate pb.

intros a l0 ind_hyp v k.
elim (stamp_dec v a); intro eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *.
intro H; inversion_clear H; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; elim (index_answer_dec (index l0 v)).
intro Hyp; elim Hyp; intros x eq2.
rewrite eq2; intro H; inversion_clear H; auto.

intro eq2; rewrite eq2.
intro pb; discriminate pb.
Qed.

(*************************************************************************)
Lemma nth_last :
 forall (l : list type) (t : type), nth (length l) (l ++ t :: nil) = Nth_in t.
Proof.
simple induction l; auto.
Qed.
Hint Resolve nth_last.


Lemma nth_last_gen :
 forall (l l1 : list type) (t : type),
 nth (length l) (l ++ t :: l1) = Nth_in t.
Proof.
simple induction l; auto.
Qed.
Hint Resolve nth_last_gen.

Lemma type_from_stamp_list_app :
 forall l1 l2 : list stamp,
 type_from_stamp_list (l1 ++ l2) =
 type_from_stamp_list l1 ++ type_from_stamp_list l2.
Proof.
simple induction l1; auto.
intros; simpl in |- *.
rewrite H; auto.
Qed.


(********************************************************************)

Lemma length_map :
 forall (s : substitution) (l : list type),
 length (map_extend_subst_type l s) = length l.
Proof.
simple induction l; auto.
intros; simpl in |- *.
rewrite H; auto.
Qed.
(********************************************************************)

Inductive is_prefixe_free2 :
list stamp -> list stamp -> list stamp -> Prop :=
    prefixe_free2_intro :
      forall C l L : list stamp,
      {l1 : list stamp | L = l ++ l1 /\ are_disjoints C l1} ->
      is_prefixe_free2 C l L.

(*****************************************************************)
Lemma is_prefixe_reflexivity :
 forall C L : list stamp, is_prefixe_free2 C L L.
intros C L.
apply prefixe_free2_intro.
exists (nil (A:=stamp)).
split; auto.
apply app_nil_end.
Qed.
Hint Resolve is_prefixe_reflexivity.
(*****************************************************************)


Lemma domain_product :
 forall (l : list stamp) (sg : list type) (phi : substitution),
 product_list l sg = Some_product phi -> domain_of_substitution phi = l.
simple induction l.
intros sg phi H; injection H; intro eq1; rewrite <- eq1; auto.

intros a l0 ind_hyp sg phi.
case sg; simpl in |- *.
(*sg=nil*)
intro pb; discriminate pb.

(*sg = t::sg0*)
intros t sg0.
elim (product_check_inv (product_list l0 sg0)).
intro Hyp; elim Hyp; clear Hyp; intros x eq1.
rewrite eq1; intro eq2; inversion_clear eq2; simpl in |- *.
rewrite (ind_hyp sg0 x eq1); auto.

intro eq2; rewrite eq2.
intro pb; discriminate pb.
Qed.

(*****************************************************************)

Lemma image_by_product2 :
 forall (l : list stamp) (sg : list type) (st : stamp) 
   (n0 : nat) (phi : substitution) (t : type),
 index l st = Index_in n0 ->
 product_list l sg = Some_product phi ->
 nth n0 sg = Nth_in t -> apply_substitution phi st = t.
Proof.
simple induction l.
simpl in |- *; intros sg st n0 phi t pb; discriminate pb.

intros a l0 ind_hyp sg st n0 phi t; simpl in |- *.
(**)elim (stamp_dec st a); intro eq1.
(**)rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *.
intro eq2; inversion_clear eq2.
case sg.
intro pb; discriminate pb.

intros t0 sg0.
(***)elim (product_check_inv (product_list l0 sg0)).
(***)intro Hyp; elim Hyp; clear Hyp; intros x eq2.
rewrite eq2.
intros; inversion_clear H; inversion_clear H0.
simpl in |- *; apply apply_subst_cons; auto.

(***)intro prod_error; rewrite prod_error.
intro pb; discriminate pb.

(**)rewrite (eq_stamp_diff st a eq1); simpl in |- *.
(***)elim (index_answer_dec (index l0 st)).
(***)intro Hyp; elim Hyp; clear Hyp.
intros n1 def_n1; rewrite def_n1.
intro Hyp; inversion_clear Hyp.
(*-*)case sg.
(*-*)intro pb; discriminate pb.

(*-*)intros t0 l1.
(****)elim (product_check_inv (product_list l0 l1)).
(****)intro Hyp; elim Hyp; clear Hyp.
intros l2 def_l2; rewrite def_l2; intro nth_hyp.
inversion_clear nth_hyp; simpl in |- *; intro.
rewrite apply_subst_cons2; auto.
apply (ind_hyp l1 st n1 l2 t def_n1 def_l2 H).

(****)intro prod_error; rewrite prod_error.
intro pb; discriminate pb.

(***) intro index_error; rewrite index_error.
intro pb; discriminate pb.
Qed.

 (*****************************************************************)

Lemma index_app :
 forall (l l2 : list stamp) (n : nat) (s : stamp),
 index l s = Index_in n -> index (l ++ l2) s = Index_in n.
simple induction l.
simpl in |- *; intros; discriminate H.

do 6 intro; simpl in |- *.
elim (stamp_dec s a); intro eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.

elim (index_answer_dec (index l0 s)); intro y; elim y.
intros x y0; rewrite y0; intro.
rewrite (H l2 x s); auto.

rewrite y; intro Pb; discriminate Pb.
Qed.


Lemma index_app_cons_gen :
 forall (l l1 : list stamp) (s : stamp),
 index l s = Stamp_not_in -> index (l ++ s :: l1) s = Index_in (length l).
simple induction l.
simpl in |- *; intros; rewrite eq_stamp_reflexivity; auto.

do 5 intro; simpl in |- *.
elim (stamp_dec s a); intros eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *.
intros Pb; discriminate Pb.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index l0 s)); intros y; elim y.
intros x y0; rewrite y0; intro.
discriminate H0.

rewrite y; intro.
rewrite (H l1 s); auto.
Qed.



(*remplacer index_app_cons par (index_app_cons_gen l (nil stamp))*)
Lemma index_app_cons :
 forall (l : list stamp) (s : stamp),
 index l s = Stamp_not_in -> index (l ++ s :: nil) s = Index_in (length l).
intro l; exact (index_app_cons_gen l nil).
(*Induction l.
Simpl; Intros;Rewrite  eq_stamp_reflexivity; Auto.


Do 4 Intro;Simpl.
Elim (stamp_dec s a);Intro eq1.
Rewrite  eq1; Rewrite  eq_stamp_reflexivity; Simpl.
Intro Pb;Discriminate Pb.

Rewrite  eq_stamp_diff; Auto.
Simpl.
Elim (index_answer_dec (index l0 s)); Intro y;Elim y.
Do 2 Intro;Rewrite -> y0;Intro.
Discriminate H0.

Rewrite  y; Intro.
Rewrite (H s);Auto.*)
Qed.

Lemma index_lt :
 forall (l : list stamp) (st : stamp) (k : nat),
 index l st = Index_in k -> k < length l.
Proof.
simple induction l.
simpl in |- *; intros st k H; discriminate H.

intros a l0 ind_hyp st k; simpl in |- *.
elim (stamp_dec st a); intro eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *.
intro eq2; inversion_clear eq2; auto with *.

rewrite eq_stamp_diff; auto.
simpl in |- *.
elim (index_answer_dec (index l0 st)).
intro Hyp; elim Hyp; clear Hyp; intros p eq3.
rewrite eq3.
intro eq4; inversion_clear eq4.
apply (lt_n_S p (length l0) (ind_hyp st p eq3)).

intro eq3; rewrite eq3; intro pb; discriminate pb.
Qed.

Lemma nth_app_cons :
 forall (l : list type) (t : type), nth (length l) (l ++ t :: nil) = Nth_in t.
simple induction l; auto.
Qed.
Hint Resolve nth_app_cons.

(******************************************************************)
Lemma map_extend_app :
 forall (s : substitution) (l1 l2 : list type),
 map_extend_subst_type (l1 ++ l2) s =
 map_extend_subst_type l1 s ++ map_extend_subst_type l2 s.

Proof.
simple induction l1; auto.
intros; simpl in |- *.
rewrite H; auto.
Qed.

(******************************************************************)
Lemma nth_app :
 forall (l l1 : list type) (n : nat),
 n < length l -> nth n (l ++ l1) = nth n l.
simple induction l.
simpl in |- *; intros; inversion_clear H.

simpl in |- *; intros a l0 ind_hyp l1 n.
case n; auto with *.
Qed.

Lemma length_map2 :
 forall (s : substitution) (l : list stamp),
 length (map_extend_subst_type (type_from_stamp_list l) s) = length l.
Proof.
simple induction l; auto.
intros; simpl in |- *.
rewrite H; auto.
Qed.

(******************************************************************)

Lemma type_from_stamp_list_cons :
 forall (s : stamp) (l : list stamp),
 type_from_stamp_list (s :: l) = Var s :: type_from_stamp_list l.
auto.
Qed.
(******************************************************************)

Lemma map_extend_cons :
 forall (t : type) (s : substitution) (l : list type),
 map_extend_subst_type (t :: l) s =
 extend_subst_type s t :: map_extend_subst_type l s.
auto.
Qed.
(******************************************************************)
Lemma Snd_gen_aux_with_app3 :
 forall (env : environment) (t : type) (l : list stamp),
 {l' : list stamp |
 snd (gen_aux t env l) = l ++ l' /\ are_disjoints (FV_env env) l'}.
Proof.
simple induction t.
(*Nat*)
simpl in |- *; intros.
exists (nil (A:=stamp)); split; auto.
apply app_nil_end.

(*Var*)
simpl in |- *; intros.
elim (bool_dec (in_list_stamp s (FV_env env))); intro eq1; rewrite eq1;
 simpl in |- *.
(**)exists (nil (A:=stamp)); split; auto.
apply app_nil_end.
(**)elim (index l s); simpl in |- *.
exists (s :: nil); split; auto.
apply are_disjoints_symetry; auto.

intro; exists (nil (A:=stamp)); split; auto.
apply app_nil_end.

(*Arrow*)
intros; rewrite snd_gen_aux_arrow_rewrite.
elim (H l).
intro l'; intro Hyp; elim Hyp; clear Hyp; intros gen_aux_t0_rwt disjoints1.
rewrite gen_aux_t0_rwt.
elim (H0 (l ++ l')).
intro l''; intro Hyp; elim Hyp; clear Hyp; intros gen_aux_t1_rwt disjoints2.
rewrite gen_aux_t1_rwt.
exists (l' ++ l''); split.
apply app_ass.
apply disjoints_app; auto.
Qed.

(******************************************************************)
Lemma is_prefixe2_gen_aux :
 forall (l L : list stamp) (t : type) (env : environment),
 is_prefixe_free2 (FV_env env) (snd (gen_aux t env l)) L ->
 is_prefixe_free2 (FV_env env) l L.
do 4 intro.
elim (Snd_gen_aux_with_app3 env t l).
intros x y.
elim y; clear y; do 2 intro.
intro Hyp; inversion_clear Hyp; elim H1; clear H1; intros x0 y.
elim y; clear y; do 2 intro.
rewrite H1.
apply prefixe_free2_intro.
exists (x ++ x0).
split.
rewrite H; rewrite <- ass_app; auto.
apply disjoints_app; auto.
Qed.
Hint Resolve is_prefixe2_gen_aux.
(*utilise par s_gen_aux_4*)
(******************************************************************)

Lemma disjoint_Snd_gen_aux :
 forall (env : environment) (l : list stamp) (t : type),
 are_disjoints (FV_env env) l ->
 are_disjoints (FV_env env) (snd (gen_aux t env l)).
intros.
elim (Snd_gen_aux_with_app3 env t l).
intros l' Hyp; elim Hyp; clear Hyp; intros; rewrite H0.
apply disjoints_app; auto.
Qed.
Hint Resolve disjoint_Snd_gen_aux.


(**********************************************************************)
Lemma gen_subst_to_subst_aux_4 :
 forall (env : environment) (tau t : type) (l L : list stamp)
   (sg : list type) (phi : substitution),
 are_disjoints (FV_env env) l ->
 apply_subst_gen sg (fst (gen_aux tau env l)) = Some_subst_gen t ->
 is_prefixe_free2 (FV_env env) (snd (gen_aux tau env l)) L ->
 product_list L sg = Some_product phi -> extend_subst_type phi tau = t.
simple induction tau.
simpl in |- *; intros; injection H0; auto.

do 7 intro; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro y; rewrite y;
 simpl in |- *.
intro Some_Some; injection Some_Some; intros.
rewrite <- H0.
apply is_not_in_domain_subst.
rewrite (domain_product L sg phi); auto.
inversion_clear H1; elim H3; clear H3.
intros x Hyp; elim Hyp; clear Hyp; intros.
rewrite H1; apply not_in_list_stamp_app.
unfold are_disjoints in H; auto.

unfold are_disjoints in H; auto.

elim (index_answer_dec (index l s)).
intro s_in_l; elim s_in_l; intro n0; clear s_in_l; intro s_in_l;
 rewrite s_in_l; simpl in |- *.
elim (nth_answer_inv (nth n0 sg)).
intro Hyp; elim Hyp; clear Hyp; intros t0 nth_val; rewrite nth_val;
 simpl in |- *.
intro Hyp; injection Hyp; intros; rewrite <- H0.
apply (image_by_product2 L sg s n0 phi t0); auto.
inversion_clear H1; elim H3; clear H3.
intros l2 Hyp2; elim Hyp2; clear Hyp2; intros.
rewrite H1.
apply index_app; auto.

intro Hyp; rewrite Hyp; simpl in |- *.
intro Pb; discriminate Pb.

intro s_in_l; rewrite s_in_l; simpl in |- *.
elim (nth_answer_inv (nth (length l) sg)).
intros Hyp; elim Hyp; clear Hyp; intros t0 nth_val; rewrite nth_val;
 simpl in |- *.
intros Hyp; injection Hyp.
intros; rewrite <- H0.
apply (image_by_product2 L sg s (length l) phi t0).
inversion_clear H1.
elim H3; clear H3.
intros l2 Hyp2; elim Hyp2; clear Hyp2; intros.
rewrite H1.
apply index_app; auto.
apply index_app_cons; auto.

auto.

auto.

intros Hyp; rewrite Hyp; simpl in |- *; intro Pb; discriminate Pb.

(*Arrow*)
do 10 intro.
rewrite <- apply_subst_arrow_rewrite; rewrite fst_gen_aux_arrow_rewrite;
 intro.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (fst (gen_aux t env l))
    (fst (gen_aux t0 env (snd (gen_aux t env l)))) t1 sg); 
 auto.
intro x; elim x; clear x; do 2 intro.
do 2 (intro Hyp; elim Hyp; clear Hyp; intro).
intro rwt_t1; rewrite rwt_t1.
rewrite snd_gen_aux_arrow_rewrite; do 2 intro.
rewrite (H0 b (snd (gen_aux t env l)) L sg phi); auto.
rewrite (H a l L sg phi); eauto.
Qed.

(**************************************************************************)

Lemma plus_one : forall n : nat, n + 1 = S n.
simple induction n; auto.
simpl in |- *; auto.
Qed.
Hint Resolve plus_one.


(*************************************************************************)

Lemma length_Snd_gen_aux :
 forall (env : environment) (t : type) (l : list stamp),
 length (snd (gen_aux t env l)) =
 max (length l) (max_gen_vars (fst (gen_aux t env l))).
simple induction t; auto.

simpl in |- *; intros.
elim (bool_dec (in_list_stamp s (FV_env env))); intro y; rewrite y;
 simpl in |- *.
auto.

elim (index_answer_dec (index l s)).
intro Hyp; elim Hyp; clear Hyp; intros x y0.
rewrite y0; simpl in |- *.
rewrite max_rew1; auto.
change (x < length l) in |- *.
apply (index_lt l s x y0).

intro y0; rewrite y0; simpl in |- *.
rewrite length_app; simpl in |- *.
rewrite max_n_S_n; auto.

intros t1 ind1 t2 ind2 l.
rewrite fst_gen_aux_arrow_rewrite; rewrite snd_gen_aux_arrow_rewrite.
simpl in |- *.
rewrite max_ass.
rewrite <- ind1; rewrite <- ind2; auto.
Qed.

(***************************************************************************)

Lemma product_list_exists :
 forall (t : type) (env : environment) (sg : list type),
 max_gen_vars (gen_type t env) <= length sg ->
 {s : substitution |
 product_list (snd (gen_aux t env nil)) sg = Some_product s}.
Proof.
unfold gen_type in |- *; intros.
apply product_for_le_length.
rewrite length_Snd_gen_aux; auto.
replace  (@length stamp (@nil stamp)) with 0; auto.
rewrite max_commutes; rewrite <- max_O; auto.
Qed.
