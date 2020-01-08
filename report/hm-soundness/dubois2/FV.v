(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import subst.
Require Import List.
Require Import langs.
Require Import tools.
Require Import tools_bool.


Fixpoint in_list_stamp (x : stamp) (ls : list stamp) {struct ls} : bool :=
  match ls with
  | nil => false
  | y :: l => if_ bool (eq_stamp x y) true (in_list_stamp x l)
  end.

Lemma in_list_cons :
 forall s : stamp, in_list_stamp s ( (*stamp*) s :: nil) = true.

Proof.
intro; simpl in |- *; rewrite eq_stamp_reflexivity; auto.
Qed.
Hint Immediate in_list_cons.

Lemma in_list_cons_inv :
 forall (l0 : list stamp) (x a : stamp),
 in_list_stamp x ( (*stamp*) a :: l0) = true ->
 {x = a} + {in_list_stamp x l0 = true}.

Proof.
do 3 intro; simpl in |- *.
elim (stamp_dec x a).
(* x=a *)
intros eq_x_a; rewrite eq_x_a; rewrite eq_stamp_reflexivity; auto.
intros neq_x_a; rewrite (eq_stamp_diff x a neq_x_a); auto.
Qed.


Lemma in_list_in_list_cons :
 forall (x v : stamp) (l : list stamp),
 in_list_stamp x l = true -> in_list_stamp x ( (*stamp*) v :: l) = true.
Proof.
simple induction l.
intros; simpl in H; discriminate H.

do 3 intro; simpl in |- *.
elim (bool_dec (eq_stamp x a)); intro y; rewrite y; simpl in |- *; intro.
apply if_same_results_true; auto.

simpl in H; auto.
Qed.

Lemma in_list_cons_in_list :
 forall (x v' : stamp) (l2 : list stamp),
 in_list_stamp x ( (*stamp*) v' :: l2) = false -> in_list_stamp x l2 = false.
Proof.
simple induction l2; auto.

do 3 intro; simpl in |- *.
elim (bool_dec (eq_stamp x v')); intro y; rewrite y; simpl in |- *.
intro pb; discriminate pb.

auto.
Qed.

Lemma permut_in_list_stamp_if :
 forall (l1 l2 : list stamp) (st : stamp) (b : bool),
 in_list_stamp st (if_ (list stamp) b l1 l2) =
 if_ bool b (in_list_stamp st l1) (in_list_stamp st l2).

Proof.
intros.
elim b; simpl in |- *; auto.
Qed.

Lemma in_list_stamp_equiv_In_true :
 forall (st : stamp) (l : list stamp),
 (in_list_stamp st l = true -> In (*stamp*)  st l) /\
 (In (*stamp*)  st l -> in_list_stamp st l = true).

Proof.
intros; split.
(* first part *)
elim l.
(* l = [] *)
simpl in |- *; intro H; inversion H.
(* l = a::l0 *)
simpl in |- *; intros a l0 H.
elim (stamp_dec st a).
(* st=a *)
intro eq_st_a; elim eq_st_a.
left; auto.
(* st <> a *)
intros not_eq_st_a.
rewrite (eq_stamp_diff st a not_eq_st_a).
simpl in |- *; intros; right; apply (H H0).
(* second part *)
elim l.
(* l = [] *)
simpl in |- *; intro H; inversion H.
(* l = a::l0 *)
simpl in |- *; intros a l0 H disj.
elim disj.
(* a=st *)
intros eq_a_st; rewrite eq_a_st.
rewrite (eq_stamp_reflexivity st).
simpl in |- *; auto.
(* In stamp st l0 *)
intro H0.
apply (if_same_results_true (eq_stamp st a) true (in_list_stamp st l0)).
auto.
apply (H H0).
Qed.

Lemma in_list_stamp_equiv_In_false :
 forall (st : stamp) (l : list stamp),
 (in_list_stamp st l = false -> ~ In (*stamp*)  st l) /\
 (~ In (*stamp*)  st l -> in_list_stamp st l = false).

Proof.
intros; split.
(* first part *)
elim l.
(* l = [] *)
simpl in |- *; intros; hnf in |- *; auto.
(* l = a::l0 *)
simpl in |- *; intros a l0 H.
intros; elim (if_true_false (eq_stamp st a) (in_list_stamp st l0) H0); intros.
hnf in |- *; intros.
elim H3.
intros eq_a_st.
generalize H1; rewrite eq_a_st; rewrite (eq_stamp_reflexivity st); intros;
 discriminate H4.
intros; apply (H H2 H4).
(* second part *)
elim l.
(* l = [] *)
simpl in |- *; auto.
(* l = a::l0 *)
simpl in |- *; intros a l0 H disj.
rewrite (eq_stamp_diff st a).
simpl in |- *.
apply H.
hnf in |- *; intros; apply disj; right; assumption.
hnf in |- *; intros; apply disj; left; auto.
Qed.

Fixpoint union_list_stamp (l1 l2 : list stamp) {struct l1} : 
 list stamp :=
  match l1, l2 with
  | nil (*stamp*), l => l
  |  (*stamp*) x :: l, l' =>
      if_ (list stamp) (in_list_stamp x l') (union_list_stamp l l')
        ( (*stamp*) x :: union_list_stamp l l')
  end.

Lemma in_union_list_stamp :
 forall (l1 l2 : list stamp) (st : stamp),
 in_list_stamp st (union_list_stamp l1 l2) = true ->
 in_list_stamp st l1 = true \/ in_list_stamp st l2 = true.

Proof.
simple induction l1.
(* l1 = [] *)
intros; right; assumption.
(* l1 = a::l *)
intros.
elim (stamp_dec st a).
(* st = a *)
intros eq_st_a; elim eq_st_a; left; simpl in |- *;
 rewrite eq_stamp_reflexivity; simpl in |- *; auto.
(* st <> a *)
intros y; elim (H l2 st).
(* H first case of conclusion *)
intros; left; simpl in |- *; rewrite (eq_stamp_diff st a y); simpl in |- *;
 auto.
(* H second case of conclusion *)
intros; right; assumption.
(* H hypothesis to justify *)
generalize H0; simpl in |- *; elim (in_list_stamp a l2); simpl in |- *.
(* (in_list_stamp a l2) = true *)
auto.
(* (in_list_stamp a l2) = false *)
rewrite (eq_stamp_diff st a y); simpl in |- *; auto.
Qed.

Lemma in_app_list_stamp :
 forall (l1 l2 : list stamp) (st : stamp),
 in_list_stamp st ( (*stamp*) l1 ++ l2) = true ->
 in_list_stamp st l1 = true \/ in_list_stamp st l2 = true.
Proof.
simple induction l1.
(* l1 = [] *)
intros; right; assumption.
(* l1 = a::l *)
intros.
elim (stamp_dec st a).
(* st = a *)
intro eq_st_a; elim eq_st_a; left; simpl in |- *;
 rewrite eq_stamp_reflexivity; simpl in |- *; auto.
(* st <> a *)
intros y; elim (H l2 st).
intros; left; simpl in |- *; rewrite (eq_stamp_diff st a y); simpl in |- *;
 auto.

intros; right; assumption.

generalize H0; simpl in |- *; elim (in_list_stamp a l2); simpl in |- *.
rewrite (eq_stamp_diff st a y); simpl in |- *; auto.

rewrite (eq_stamp_diff st a y); simpl in |- *; auto.
Qed.


Lemma in_second_componant_union_list_stamp :
 forall (l1 l2 : list stamp) (st : stamp),
 in_list_stamp st l2 = true ->
 in_list_stamp st (union_list_stamp l1 l2) = true.
Proof.
simple induction l1.
(* l1 = [] *)
simpl in |- *; intros; assumption.
(* l1 = a::l *)
intros; simpl in |- *;
 rewrite
  (permut_in_list_stamp_if (union_list_stamp l l2)
     ( (*stamp*) a :: union_list_stamp l l2) st (in_list_stamp a l2))
  .
apply
 (if_same_results_true (in_list_stamp a l2)
    (in_list_stamp st (union_list_stamp l l2))
    (in_list_stamp st ( (*stamp*) a :: union_list_stamp l l2))).
(* (in_list_stamp a l2)=true *)
apply (H l2 st H0).
(* (in_list_stamp a l2)=false *)
apply
 (if_same_results_true (eq_stamp st a) true
    (in_list_stamp st (union_list_stamp l l2))).
(* (eq_stamp st a)=true *)
auto.
(* (eq_stamp st a)=false *)
apply (H l2 st H0).
Qed.

Lemma in_first_componant_union_list_stamp :
 forall (l1 l2 : list stamp) (st : stamp),
 in_list_stamp st l1 = true ->
 in_list_stamp st (union_list_stamp l1 l2) = true.

Proof.
simple induction l1.
(* l1 = [] *)
simpl in |- *; intros; discriminate H.
(* l1 = a::l *)
intros; simpl in |- *.
rewrite
 (permut_in_list_stamp_if (union_list_stamp l l2)
    ( (*stamp*) a :: union_list_stamp l l2) st (in_list_stamp a l2))
 .
generalize H0; simpl in |- *.
elim (stamp_dec st a).
(* st = a *)
intros eq_st_a; elim eq_st_a; rewrite (eq_stamp_reflexivity st);
 simpl in |- *.
elim (bool_dec (in_list_stamp st l2)); intros H1 H2.
(* (in_list_stamp a l2)=true *)
rewrite H1; simpl in |- *;
 apply (in_second_componant_union_list_stamp l l2 st H1).
(* (in_list_stamp a l2)=false *)
rewrite H1; simpl in |- *; auto.
(* st <> a *)
intros neq_st_a.
rewrite (eq_stamp_diff st a neq_st_a); simpl in |- *.
intros; apply if_same_results_true; apply (H l2 st H1).
Qed.

Lemma not_in_list_union_inversion :
 forall (l1 l2 : list stamp) (st : stamp),
 in_list_stamp st l1 = false ->
 in_list_stamp st l2 = false ->
 in_list_stamp st (union_list_stamp l1 l2) = false.

Proof.
intros.
apply
 (contrapp2 (in_list_stamp st (union_list_stamp l1 l2)) 
    (in_list_stamp st l1) (in_list_stamp st l2)
    (in_union_list_stamp l1 l2 st) H H0).
Qed.

Lemma not_In_list :
 forall (l : list stamp) (st a : stamp),
 ~ In (*stamp*)  st l -> In (*stamp*)  a l -> eq_stamp st a = false.

Proof.
simple induction l.
(* l = [] *)
simpl in |- *; intros; inversion H0.
(* l = a0::l0 *)
simpl in |- *; intros. 
elim H1; intros. elim H2; apply (eq_stamp_diff st a).
hnf in |- *; intros; apply H0; left; auto.
intros; apply (H st a0).
hnf in |- *; intros; apply H0; right; auto.
assumption.
Qed.

Lemma not_in_list :
 forall (l : list stamp) (st a : stamp),
 in_list_stamp st l = false ->
 in_list_stamp a l = true -> eq_stamp st a = false.

Proof.
intros.
apply (not_In_list l st a).
elim (in_list_stamp_equiv_In_false st l); intros.
hnf in |- *; intros; apply (H1 H); assumption.
elim (in_list_stamp_equiv_In_true a l); intros.
apply (H1 H0).
Qed.

Lemma not_in_union_incremental :
 forall (l1 l2 : list stamp) (st a : stamp),
 in_list_stamp st (union_list_stamp ( (*stamp*) a :: l1) l2) = false ->
 in_list_stamp st (union_list_stamp l1 l2) = false.

Proof.
intros l1 l2 st a.
simpl in |- *.
elim (bool_dec (in_list_stamp a l2)).
(* (in_list_stamp a l2)=true *)
intros H; rewrite H; simpl in |- *; intros; assumption.
(* (in_list_stamp a l2)=flase *)
intros H; rewrite H; simpl in |- *; intros.
elim
 (if_true_false (eq_stamp st a) (in_list_stamp st (union_list_stamp l1 l2))
    H0); intros; assumption.
Qed.


Lemma not_in_list_union :
 forall (l1 l2 : list stamp) (st : stamp),
 in_list_stamp st (union_list_stamp l1 l2) = false ->
 in_list_stamp st l1 = false /\ in_list_stamp st l2 = false.

Proof.
simple induction l1.
(* l1 = [] *)
simpl in |- *; split; auto.
(* l1 = a::l *)
simpl in |- *; intros.
split.
elim (if_true_false_inversion (eq_stamp st a) (in_list_stamp st l)).
auto.
(* eq_stamp st a)=false *)
elim (bool_dec (in_list_stamp a l2)).
(* (in_list_stamp a l2)=true *)
intros H1; generalize H0; rewrite H1; simpl in |- *; intros.
apply (not_in_list l2 st a).
elim (H l2 st); intros; assumption.
assumption.
(* (in_list_stamp a l2)=false *)
intros H1; generalize H0; rewrite H1; simpl in |- *; intros.
elim
 (if_true_false (eq_stamp st a) (in_list_stamp st (union_list_stamp l l2)) H2);
 intros; assumption.
(* (in_list_stamp st l)=false *)
elim (H l2 st). intros; assumption.
apply (not_in_union_incremental l l2 st a H0).
(* (in_list_stamp st l2)=false *)
elim (H l2 st). intros; assumption.
apply (not_in_union_incremental l l2 st a H0).
Qed.

Lemma not_in_list_stamp_app :
 forall (l1 l2 : list stamp) (s : stamp),
 in_list_stamp s l1 = false ->
 in_list_stamp s l2 = false -> in_list_stamp s ( (*stamp*) l1 ++ l2) = false.
simple induction l1; auto.
intros a l ind_hyp l2 s.
elim (stamp_dec s a); intro eq1; simpl in |- *.
rewrite eq1; rewrite eq_stamp_reflexivity; simpl in |- *.
intro pb; discriminate pb.

rewrite (eq_stamp_diff s a eq1); simpl in |- *; auto.
Qed.

(***************************************************************)
Lemma length_app :
 forall (A : Set) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
simple induction l1; auto.
simpl in |- *; intros; auto.
Qed.
 

Lemma length_app_cons :
 forall (A : Set) (l : list A) (x : A), length (l ++ x :: nil) = S (length l).
Proof.
simple induction l; auto.

intros; simpl in |- *; auto.
Qed.

(*********************************************************************)
(*****************************************************************)
Fixpoint FV_type (t : type) : list stamp :=
  match t with
  | Nat => nil (A:=stamp)
  | Var st =>  (*stamp*) st :: nil
  | Arrow t1 t2 => union_list_stamp (FV_type t1) (FV_type t2)
  end.

Fixpoint range_of_substitution (s : substitution) : 
 list stamp :=
  match s with
  | nil => nil (A:=stamp)
  | (st, t) :: l' => union_list_stamp (FV_type t) (range_of_substitution l')
  end.

Fixpoint domain_of_substitution (l : substitution) : 
 list stamp :=
  match l with
  | nil => nil (A:=stamp)
  | a :: l' => fst a :: domain_of_substitution l'
  end.