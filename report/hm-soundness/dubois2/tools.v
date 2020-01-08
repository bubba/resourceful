(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import Peano_dec.
Require Import Plus.
Require Import langs.
Require Import tools_bool.

Lemma eq_nat_plus : forall n1 n2 m : nat, n1 <> n2 -> m + n1 <> m + n2.
unfold not in |- *; intros.
absurd (n1 = n2); auto.
apply plus_reg_l with (p := m); auto.
Qed.

Lemma exc_dec :
 forall (A : Set) (v : Exc A), {x : A | v = value x} + {v = error}.
intros; case v; auto.
intros a; left; exists a; auto.
Qed.


(*Recursive Definition eq_nat: nat -> nat -> bool := *)
Fixpoint eq_nat (n m : nat) {struct n} : bool :=
  match n, m with
  | O, O => true
  | S n, S m => eq_nat n m
  | O, S m => false
  | S n, O => false
  end.

Lemma eq_nat_diff : forall n1 n2 : nat, n1 <> n2 -> eq_nat n1 n2 = false.
simple induction n1.
intro n2; case n2; auto.
intro; absurd (0 = 0); auto.

unfold not in |- *.
do 3 intro; simpl in |- *.
case n2; auto.
Qed.

Definition eq_stamp (v v' : stamp) :=
  match v, v' with
  | Stamp n, Stamp n' => eq_nat n n'
  end.

Definition eq_identifier (v v' : identifier) :=
  match v, v' with
  | Ident n, Ident n' => eq_nat n n'
  end. 

Lemma eq_identifier_reflexivity :
 forall i : identifier, eq_identifier i i = true.

Proof.
simple induction i; simpl in |- *; simple induction n; auto.
Qed.

Lemma eq_stamp_reflexivity : forall st : stamp, eq_stamp st st = true.

Proof.
simple induction st; simpl in |- *; simple induction n; auto.
Qed.
Hint Resolve eq_stamp_reflexivity.

Lemma eq_nat_equality : forall n1 n2 : nat, eq_nat n1 n2 = true -> n1 = n2.

Proof.

simple induction n1; simple induction n2; simpl in |- *.
auto.
intros; discriminate H0.
intros; discriminate H0.
auto.
Qed.

Lemma eq_nat_reflexivity : forall n : nat, eq_nat n n = true.
simple induction n; auto.
Qed.

Lemma eq_nat_plus_p_Sn_and_p : forall n p : nat, eq_nat (p + S n) p = false.
simple induction p; auto.
Qed.


Lemma eq_stamp_equality :
 forall st1 st2 : stamp, eq_stamp st1 st2 = true -> st1 = st2.

Proof.
simple induction st1; intros n1; simple induction st2; intros n2.
simpl in |- *; intros.
elim (eq_nat_equality n1 n2 H).
auto.
Qed. 

Lemma eq_identifier_equality :
 forall i1 i2 : identifier, eq_identifier i1 i2 = true -> i1 = i2.

Proof.
simple induction i1; intros n1; simple induction i2; intros n2.
simpl in |- *; intros.
elim (eq_nat_equality n1 n2 H).
auto.
Qed. 

Lemma eq_stamp_diff :
 forall st1 st2 : stamp, st1 <> st2 -> eq_stamp st1 st2 = false.

Proof.
intros.
elim (not_true_is_false (eq_stamp st1 st2)); auto.
unfold not in |- *; intros; apply H; exact (eq_stamp_equality st1 st2 H0).
Qed.

Lemma eq_identifier_diff :
 forall i1 i2 : identifier, i1 <> i2 -> eq_identifier i1 i2 = false.

Proof.
intros.
elim (not_true_is_false (eq_identifier i1 i2)); auto.
unfold not in |- *; intros; apply H; exact (eq_identifier_equality i1 i2 H0).
Qed.

Lemma stamp_dec : forall st1 st2 : stamp, {st1 = st2} + {st1 <> st2}.

Proof.
simple induction st1; simple induction st2; intros.
elim (eq_nat_dec n n0).
intro eq; left; rewrite eq; auto.
unfold not in |- *; intro neq; right; intro eqs; apply neq; inversion eqs;
 auto.
Qed.

Lemma identifier_dec : forall v1 v2 : identifier, {v1 = v2} + {v1 <> v2}.

Proof.
simple induction v1; simple induction v2; intros.
elim (eq_nat_dec n n0).
intro eq; left; rewrite eq; auto.
unfold not in |- *; intro neq; right; intro eqs; apply neq; inversion eqs;
 auto.
Qed.
