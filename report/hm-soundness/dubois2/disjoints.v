(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import langs.
Require Import tools.
Require Import tools_bool.
Require Import List.
Require Import subset.
Require Import FV.

Definition are_disjoints (l l' : list stamp) :=
  forall x : stamp, in_list_stamp x l = true -> in_list_stamp x l' = false.

Lemma disjoint_nil_l : forall l : list stamp, are_disjoints nil l.

Proof.
intro; unfold are_disjoints in |- *.
simpl in |- *; intros; discriminate H.
Qed.
Hint Resolve disjoint_nil_l.

Lemma disjoint_cons_nil :
 forall (l : list stamp) (s : stamp),
 in_list_stamp s l = false -> are_disjoints (s :: nil) l.

Proof.
intros; unfold are_disjoints in |- *.
simpl in |- *; intros.
elim (if_false_true (eq_stamp x s) true H0); intros.
rewrite (eq_stamp_equality x s H1).
assumption.
Qed.
Hint Resolve disjoint_cons_nil.

Lemma disjoint_inversion2 :
 forall (l l' : list stamp) (x : stamp),
 are_disjoints l l' -> in_list_stamp x l' = true -> in_list_stamp x l = false.

Proof.
unfold are_disjoints in |- *; intros.
apply not_true_is_false.
generalize (H x); intros.
elim H0.
generalize H1; elim (in_list_stamp x l); simpl in |- *; intros.
rewrite H2. hnf in |- *; intros; discriminate H3.
auto.
rewrite H0; hnf in |- *; intros; discriminate H3.
Qed.

Lemma are_disjoints_symetry :
 forall l l' : list stamp, are_disjoints l l' -> are_disjoints l' l.

Proof.
unfold are_disjoints in |- *; intros.
apply (disjoint_inversion2 l l' x H H0).
Qed.

Lemma disjoint_list_and_union :
 forall l l1 l2 : list stamp,
 are_disjoints l1 l ->
 are_disjoints l2 l -> are_disjoints (union_list_stamp l1 l2) l.

Proof.
unfold are_disjoints in |- *; intros.
elim (in_union_list_stamp l1 l2 x H1).
exact (H x).
exact (H0 x).
Qed.

Lemma disjoint_list_and_union_inversion1 :
 forall l l1 l2 : list stamp,
 are_disjoints l (union_list_stamp l1 l2) -> are_disjoints l l1.

Proof.
unfold are_disjoints in |- *; intros.
elim (not_in_list_union l1 l2 x (H x H0)); intros; assumption.
Qed.

Lemma disjoint_list_and_union_inversion2 :
 forall l l1 l2 : list stamp,
 are_disjoints l (union_list_stamp l1 l2) -> are_disjoints l l2.

Proof.
unfold are_disjoints in |- *; intros.
elim (not_in_list_union l1 l2 x (H x H0)); intros; assumption.
Qed.

Lemma disjoint_subset_bis :
 forall l1 l2 l : list stamp,
 are_disjoints l2 l1 -> is_subset_list_stamp l l2 -> are_disjoints l1 l.

Proof.
intros; unfold are_disjoints in |- *; intros.
inversion H0.
apply (contrapp (in_list_stamp x l) (in_list_stamp x l2)).
exact (H2 x).
apply (disjoint_inversion2 l2 l1 x H H1).
Qed.

(******************************************************************)
Lemma disjoint_l_nil : forall l : list stamp, are_disjoints l nil.
simple induction l; auto.
intros.
unfold are_disjoints in |- *; auto.
Qed.
Hint Resolve disjoint_l_nil.

(*********************************************************************)

Lemma disjoints_app :
 forall l l1 l2 : list stamp,
 are_disjoints l l1 -> are_disjoints l l2 -> are_disjoints l (l1 ++ l2).
simple induction l1; auto.

unfold are_disjoints in |- *; intros.
apply not_in_list_stamp_app; auto.
Qed.

(******************************************************************)
Lemma are_disjoint_cons_inv :
 forall (v v' : stamp) (l1 l2 : list stamp),
 are_disjoints (v :: l1) (v' :: l2) -> are_disjoints l1 l2.
Proof.
unfold are_disjoints in |- *; intros v v' l1 l2 Hyp x in_list_x.
generalize (in_list_in_list_cons x v l1 in_list_x).
intro in_list_x_cons.
generalize (Hyp x in_list_x_cons).
exact (in_list_cons_in_list x v' l2).
Qed.