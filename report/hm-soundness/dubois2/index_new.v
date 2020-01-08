(* author : Catherine Dubois *)

Require Import List.
Require Import tools_bool.
Require Import generic_DB.
Require Import tools_more_general.
Require Import Lt.

Fixpoint index_new (A : Set) (eq_dec : A -> A -> bool) 
 (l : list A) (v : A) {struct l} : index_answer :=
  match l with
  | nil => Stamp_not_in
  | a :: r =>
      if_ index_answer (eq_dec v a) (Index_in 0)
        match index_new A eq_dec r v with
        | Stamp_not_in => Stamp_not_in
        | Index_in n => Index_in (S n)
        end
  end.

Lemma
  index_new_app_cons_inv2 :
    forall (A : Set) (eq_A : A -> A -> bool) 
   (A_dec : forall x1 x2 : A, {x1 = x2} + {x1 <> x2})
   (A_reflexivity : forall x : A, eq_A x x = true)
   (A_diff : forall x y : A, x <> y -> eq_A x y = false) 
   (l : list A) 
      (s1 s2 : A) (n : nat),
    s1 <> s2 ->
    index_new A eq_A (l ++ s1 :: nil) s2 = Index_in n ->
    index_new A eq_A l s2 = Index_in n.
induction l.
intros;simpl in H0.
rewrite (A_diff s2 s1) in H0;auto.

intros;simpl.
elim (A_dec a s2);intro Heq_s2.
subst.
rewrite (A_reflexivity s2);simpl.
simpl in H0;rewrite (A_reflexivity s2) in H0;simpl in H0.
assumption.

rewrite (A_diff s2 a);auto.
simpl.
simpl in H0.
rewrite (A_diff s2 a) in H0;auto.
simpl in H0.
case_eq (index_new A eq_A (l++s1::nil) s2).
intro Hcase;rewrite Hcase in H0;discriminate H0.
intros n0 Hcase; rewrite Hcase in H0.
rewrite IHl with (s1:=s1) (n:=n0);assumption.
Qed.



Lemma index_new_app2 :
 forall (A : Set) (eq_A : A -> A -> bool)
   (A_dec : forall x1 x2 : A, {x1 = x2} + {x1 <> x2})
   (A_reflexivity : forall x : A, eq_A x x = true)
   (A_diff : forall x y : A, x <> y -> eq_A x y = false) 
   (l l2 : list A) (n : nat) (s : A),
 index_new A eq_A l s = Index_in n ->
 index_new A eq_A (l ++ l2) s = Index_in n.
Proof.
intros A eq_A A_dec A_reflexivity A_diff.
simple induction l.
simpl in |- *; intros; discriminate H.

do 6 intro; simpl in |- *.
elim (A_dec s a); intro eq1.
rewrite eq1; rewrite A_reflexivity; simpl in |- *; auto.

rewrite A_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new A eq_A l0 s)); intros y; elim y.
intros x y0; rewrite y0; intro.
rewrite (H l2 x s); auto.

rewrite y; intro Pb; discriminate Pb.
Qed.


Lemma index_new_app_cons2 :
 forall (A : Set) (eq_A : A -> A -> bool)
   (A_dec : forall x1 x2 : A, {x1 = x2} + {x1 <> x2})
   (A_reflexivity : forall x : A, eq_A x x = true)
   (A_diff : forall x y : A, x <> y -> eq_A x y = false) 
   (l : list A) (s : A),
 index_new A eq_A l s = Stamp_not_in ->
 index_new A eq_A (l ++ s :: nil) s = Index_in (length l).
Proof.
intros A eq_A A_dec A_reflexivity A_diff.
simple induction l.
simpl in |- *; intros; rewrite A_reflexivity; auto.


do 4 intro; simpl in |- *.
elim (A_dec s a); intro eq1.
rewrite eq1; rewrite A_reflexivity; simpl in |- *.
intro Pb; discriminate Pb.

rewrite A_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new A eq_A l0 s)); intro y; elim y.
intros x y0; rewrite y0; intro; discriminate H0.

rewrite y; intro.
rewrite (H s); auto.
Qed.


Lemma index_new_lt2 :
 forall (A : Set) (eq_A : A -> A -> bool)
   (A_dec : forall x1 x2 : A, {x1 = x2} + {x1 <> x2})
   (A_reflexivity : forall x : A, eq_A x x = true)
   (A_diff : forall x y : A, x <> y -> eq_A x y = false) 
   (l : list A) (x : A) (k : nat),
 index_new A eq_A l x = Index_in k -> k < length l.
Proof.
intros A eq_A A_dec A_reflexivity A_diff.
simple induction l.
simpl in |- *; intros st k H; discriminate H.

intros a l0 ind_hyp st k; simpl in |- *.
elim (A_dec st a); intro eq1.
rewrite eq1; rewrite A_reflexivity; simpl in |- *.
intro eq2; inversion_clear eq2; auto with *.

rewrite A_diff; auto.
simpl in |- *.
elim (index_answer_dec (index_new A eq_A l0 st)).
intro Hyp; elim Hyp; clear Hyp; intros p eq3.
rewrite eq3.
intro eq4; inversion_clear eq4.
apply (lt_n_S p (length l0) (ind_hyp st p eq3)).

intro eq3; rewrite eq3; intro pb; discriminate pb.
Qed.
