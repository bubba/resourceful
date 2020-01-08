(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import langs.
Require Import subst.
Require Import type_scheme.
Require Import generic_DB.



Fixpoint map_extend_subst_type (l : list type) (s2 : substitution) {struct l} 
   : list type :=
  match l with
  | nil => nil (A:=type)
  | t :: rest => extend_subst_type s2 t :: map_extend_subst_type rest s2
  end.

Lemma max_gen_vars_of_type_to_type_scheme :
 forall t : type, max_gen_vars (type_to_type_scheme t) = 0.
Proof.
simple induction t; auto.
(*Arrow*)
intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed.

Lemma max_gen_vars_subst :
 forall (s : substitution) (ts : type_scheme),
 max_gen_vars (extend_subst_type_scheme s ts) = max_gen_vars ts.
Proof.
simple induction ts; auto.
intro; simpl in |- *.
apply max_gen_vars_of_type_to_type_scheme.
intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed.


Lemma length_map :
 forall (s : substitution) (x : list type),
 length (map_extend_subst_type x s) = length x.

Proof.
simple induction x; auto.
intros; simpl in |- *; rewrite H; auto.
Qed.




Lemma nth_map :
 forall (s : substitution) (x : list type) (n : nat) (t : type),
 nth n x = Nth_in t ->
 nth n (map_extend_subst_type x s) = Nth_in (extend_subst_type s t).

Proof.
simple induction x.
(*nil*)
intros; simpl in H; discriminate H.
(*cons*)
simpl in |- *; do 5 intro.
case n; simpl in |- *.
(*n=O*)
intros nth_a_t; inversion_clear nth_a_t; auto.
(*n=(S n0) *)
intros; apply H; auto.
Qed.

Lemma generic_compose :
 forall (s : substitution) (ts : type_scheme) (t : type) (x : list type),
 apply_subst_gen x ts = Some_subst_gen t ->
 apply_subst_gen (map_extend_subst_type x s) (extend_subst_type_scheme s ts) =
 Some_subst_gen (extend_subst_type s t).
Proof.
simple induction ts.
(*Nat*)
intros; simpl in |- *; inversion_clear H; auto.
(*Var_ts*)
intros; simpl in |- *; inversion_clear H.
rewrite apply_subst_gen_type_to_type_scheme; auto.
(*Gen*)
do 3 intro; simpl in |- *; elim s0; simpl in |- *; intro n0.
elim (nth_answer_inv (nth n0 x)).
(* Nth_in *)
intro Ex1; elim Ex1; intros t0 Pt0.
rewrite Pt0; simpl in |- *.
intro; inversion H.
rewrite (nth_map s x n0 t0 Pt0).
rewrite H1; auto.

(* Type_not_in *)
intro H; rewrite H; simpl in |- *.
intro H1; discriminate H1.
(*Arrow*)
intros ts1 H1 ts2 H2 t x; simpl in |- *.
elim (subst_gen_answer_inv (apply_subst_gen x ts1)).
intro Ex1; elim Ex1; intros t1 Pt_n1; rewrite Pt_n1.
elim (subst_gen_answer_inv (apply_subst_gen x ts2)).
intro Ex2; elim Ex2; intros t2 Pt_n2; rewrite Pt_n2.
intro eq1.
inversion_clear eq1.
rewrite (H1 t1 x Pt_n1).
rewrite (H2 t2 x Pt_n2); auto.

(* (apply_subst_gen ...=Error *)
intros wrong; rewrite wrong.
intros Hwrong; discriminate Hwrong.

(* (apply_subst_gen ...=Error *)
intros wrong; rewrite wrong.
intros Hwrong; discriminate Hwrong.
Qed.


(*************************************************************************)
Lemma is_gen_instance_stable_by_substitution :
 forall (ts : type_scheme) (s : substitution) (t : type),
 is_gen_instance t ts ->
 is_gen_instance (extend_subst_type s t) (extend_subst_type_scheme s ts).

Proof.
intros; inversion_clear H.
elim H0; clear H0; intros.
apply gen_instance_intro.
exists (map_extend_subst_type x s).
apply generic_compose; auto.
Qed.