(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import langs.
Require Import tools.
Require Import FV.

Inductive is_subset_list_stamp : list stamp -> list stamp -> Prop :=
    is_subset_intro :
      forall l1 l2 : list stamp,
      (forall st : stamp,
       in_list_stamp st l1 = true -> in_list_stamp st l2 = true) ->
      is_subset_list_stamp l1 l2.

Lemma subset_reflexivity : forall l : list stamp, is_subset_list_stamp l l.

Proof.
intro.
apply is_subset_intro; auto.
Qed.
Hint Immediate subset_reflexivity.

Lemma nil_is_subset : forall l : list stamp, is_subset_list_stamp nil l.

Proof.
intro; apply is_subset_intro.
intros; simpl in H; discriminate H.
Qed.
Hint Immediate nil_is_subset.

Lemma subset_cons_subset :
 forall (s : stamp) (l l' : list stamp),
 is_subset_list_stamp ( (*stamp*) s :: l') l -> in_list_stamp s l = true.

Proof.
intros; inversion H.
apply H0.
simpl in |- *; rewrite eq_stamp_reflexivity; auto.
Qed.

Lemma subset_app_inv :
 forall (l l' : list stamp) (s : stamp),
 is_subset_list_stamp l l' ->
 in_list_stamp s l' = true ->
 is_subset_list_stamp ( (*stamp*) l ++  (*stamp*) s :: nil) l'.

Proof.
intros; apply is_subset_intro; simpl in |- *; intros st st_in_app.
elim (in_app_list_stamp l ( (*stamp*) s :: nil) st st_in_app).
inversion H; exact (H1 st).

simpl in |- *; elim (stamp_dec st s); intro eq1.
rewrite eq1; rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *; intro pb; discriminate pb.
Qed.

Lemma subset_cons_inv :
 forall (l l' : list stamp) (s : stamp),
 is_subset_list_stamp l l' ->
 in_list_stamp s l' = true -> is_subset_list_stamp ( (*stamp*) s :: l) l'.

Proof.
intros; apply is_subset_intro; simpl in |- *.
intros st.
elim (stamp_dec st s).
(* st=s *)
intros eq_st_s; rewrite eq_st_s; rewrite eq_stamp_reflexivity; auto.
(* st<>s *)
intros neq_st_s; rewrite (eq_stamp_diff st s neq_st_s); simpl in |- *.
inversion H; intros P; apply (H1 st P).
Qed.

Lemma subset_of_union_inversion1 :
 forall l l1 l2 : list stamp,
 is_subset_list_stamp (union_list_stamp l1 l2) l -> is_subset_list_stamp l1 l.

Proof.
intros; apply is_subset_intro; intros.
inversion H.
apply (H1 st (in_first_componant_union_list_stamp l1 l2 st H0)).
Qed.

Lemma subset_of_union_inversion2 :
 forall l l1 l2 : list stamp,
 is_subset_list_stamp (union_list_stamp l1 l2) l -> is_subset_list_stamp l2 l.

Proof.
intros; apply is_subset_intro; intros.
inversion H.
apply (H1 st (in_second_componant_union_list_stamp l1 l2 st H0)).
Qed.

Lemma subset_of_union1 :
 forall l l1 l2 : list stamp,
 is_subset_list_stamp l l1 -> is_subset_list_stamp l (union_list_stamp l1 l2).

Proof.
intros; apply is_subset_intro; intros.
apply (in_first_componant_union_list_stamp l1 l2 st).
inversion H. 
apply (H1 st H0).
Qed.

Lemma subset_of_union2 :
 forall l l1 l2 : list stamp,
 is_subset_list_stamp l l2 -> is_subset_list_stamp l (union_list_stamp l1 l2).

Proof.
intros; apply is_subset_intro; intros.
apply (in_second_componant_union_list_stamp l1 l2 st).
inversion H. 
apply (H1 st H0).
Qed.

Lemma l1_subset_of_union_l1_l2 :
 forall l1 l2 : list stamp, is_subset_list_stamp l1 (union_list_stamp l1 l2).

Proof.
intros; apply is_subset_intro; intros.
apply (in_first_componant_union_list_stamp l1 l2 st H).
Qed.
Hint Resolve l1_subset_of_union_l1_l2.

Lemma l2_subset_of_union_l1_l2 :
 forall l1 l2 : list stamp, is_subset_list_stamp l2 (union_list_stamp l1 l2).

Proof.
intros; apply is_subset_intro; intros.
apply (in_second_componant_union_list_stamp l1 l2 st H).
Qed.
Hint Resolve l2_subset_of_union_l1_l2.

Lemma union_subset :
 forall l l1 l2 : list stamp,
 is_subset_list_stamp l1 l ->
 is_subset_list_stamp l2 l -> is_subset_list_stamp (union_list_stamp l1 l2) l.

Proof.
intros; apply is_subset_intro; intros.
inversion H; inversion H0; intros.
elim (in_union_list_stamp l1 l2 st H1).
exact (H2 st).
exact (H5 st).
Qed.

Lemma subset_trans :
 forall l1 l2 l3 : list stamp,
 is_subset_list_stamp l1 l2 ->
 is_subset_list_stamp l2 l3 -> is_subset_list_stamp l1 l3.
intros l1 l2 l3 l1_in_l2 l2_in_l3.
inversion_clear l1_in_l2; inversion_clear l2_in_l3.
apply is_subset_intro.
auto.
Qed.


Lemma subset_union_ass3 :
 forall l1 l2 l3 : list stamp,
 is_subset_list_stamp (union_list_stamp (union_list_stamp l1 l2) l3)
   (union_list_stamp (union_list_stamp l1 l3) l2).
intros; apply is_subset_intro.
intros st st_in_union_union.
elim (in_union_list_stamp (union_list_stamp l1 l2) l3 st st_in_union_union);
 intro.
elim (in_union_list_stamp l1 l2 st H); intro.
apply in_first_componant_union_list_stamp.
apply in_first_componant_union_list_stamp; auto.

apply in_second_componant_union_list_stamp; auto.

apply in_first_componant_union_list_stamp.
apply in_second_componant_union_list_stamp; auto.
Qed.
Hint Resolve subset_union_ass3.

Lemma subset_union_ass2 :
 forall l1 l2 l3 : list stamp,
 is_subset_list_stamp (union_list_stamp l1 (union_list_stamp l2 l3))
   (union_list_stamp (union_list_stamp l1 l2) l3).
intros; apply is_subset_intro.
intros st st_in_union_union.
elim (in_union_list_stamp l1 (union_list_stamp l2 l3) st st_in_union_union);
 intro.
apply in_first_componant_union_list_stamp.
apply in_first_componant_union_list_stamp; auto.

elim (in_union_list_stamp l2 l3 st H); intro.
apply in_first_componant_union_list_stamp.
apply in_second_componant_union_list_stamp; auto.

apply in_second_componant_union_list_stamp; auto.
Qed.
Hint Resolve subset_union_ass2.

Lemma union_subset_union :
 forall l l' l1 l2 : list stamp,
 is_subset_list_stamp l1 l ->
 is_subset_list_stamp l2 l' ->
 is_subset_list_stamp (union_list_stamp l1 l2) (union_list_stamp l l').
Proof.
intros l l' l1 l2 l1_subset_l l2_subset_l'.
apply is_subset_intro.
intros x x_in_l1_U_l2.
elim (in_union_list_stamp l1 l2 x x_in_l1_U_l2).
intro x_in_l1.
inversion_clear l1_subset_l.
apply in_first_componant_union_list_stamp; auto.
intro x_in_l2.
inversion_clear l2_subset_l'.
apply in_second_componant_union_list_stamp; auto.
Qed.


Lemma subset_union_com :
 forall l1 l2 : list stamp,
 is_subset_list_stamp (union_list_stamp l1 l2) (union_list_stamp l2 l1).

Proof.
intros.
apply is_subset_intro.
intros.
elim (in_union_list_stamp l1 l2 st H).
intros.
apply in_second_componant_union_list_stamp; auto.

intros.
apply in_first_componant_union_list_stamp; auto.
Qed.
Hint Resolve subset_union_com.

Lemma subset_union_ass4 :
 forall l1 l2 l3 : list stamp,
 is_subset_list_stamp (union_list_stamp (union_list_stamp l1 l2) l3)
   (union_list_stamp l1 (union_list_stamp l2 l3)).
intros; apply is_subset_intro.
intros.
elim (in_union_list_stamp (union_list_stamp l1 l2) l3 st H); intro.
elim (in_union_list_stamp l1 l2 st H0); intro.
apply in_first_componant_union_list_stamp; auto.

apply in_second_componant_union_list_stamp; auto.
apply in_first_componant_union_list_stamp; auto.

apply in_second_componant_union_list_stamp; auto.
apply in_second_componant_union_list_stamp; auto.

Qed.
