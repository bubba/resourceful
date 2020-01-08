(* author : Catherine Dubois *)
Require Import FV.
Require Import order_stamp.
Require Import langs.
Require Import List.
Require Import tools.
Require Import Setoid.
Require Import Compare.

(* maximum of two nats *)
Fixpoint max (n m : nat) {struct n} : nat :=
  match n, m with
  | O, O => 0
  | O, S m' => S m'
  | S n', O => S n'
  | S n', S m' => S (max n' m')
  end.

Lemma max_n_n : forall n, max n n = n.
Proof.
induction n.
auto.
simpl;auto.
Qed.

Lemma le_max_l : forall n m : nat, n <= max n m.

Proof.
simple induction n; simple induction m; simpl in |- *; auto with *.
Qed.
Hint Resolve le_max_l.

Lemma le_max_r : forall n m : nat, m <= max n m.

Proof.
simple induction n; simple induction m; simpl in |- *; auto with *.
Qed.
Hint Resolve le_max_r.

Lemma max_case : forall n m : nat, {max n m = n} + {max n m = m}.

Proof.
simple induction n; simple induction m.
(* O O *)
auto.
(* O (S m0) *)
simpl in |- *; auto.
(* (S n0) O *)
simpl in |- *; auto.
(* (S n0) (S m0) *)
intros m0 H0; elim (H m0).
left; simpl in |- *; auto.
right; simpl in |- *; auto.
Qed.
Hint Resolve max_case.

Lemma max_O : forall n : nat, n = max n 0.
simple induction n; auto.
Qed.
Hint Resolve max_O.

Lemma max_O_m : forall m : nat, max 0 m = m.
simple induction m; auto.
Qed.
Hint Resolve max_O_m.

Lemma max_rew1 : forall m n : nat, n <= m -> max m n = m.
simple induction m; auto.
intros; inversion_clear H; auto.

do 3 intro; case n0.
auto.

intros; simpl in |- *.
rewrite H; auto with *.
Qed.

Lemma max_commutes : forall n m : nat, max n m = max m n.
simple induction n.
intro; rewrite <- max_O; auto.

intros; case m; auto.

intro; simpl in |- *.
rewrite H; auto.
Qed.


Lemma max_n_S_n : forall n : nat, max n (S n) = S n.
simple induction n; auto.
simpl in |- *; auto.
Qed.


Lemma max_ass : forall n p q : nat, max n (max p q) = max (max n p) q.
simple induction n.
intros; do 2 rewrite max_O_m; auto.

intros; case p.
rewrite max_O_m; rewrite <- max_O; auto.

intro; case q.
do 2 rewrite <- max_O; auto.

simpl in |- *; intro; rewrite H; auto.
Qed.


Lemma le_max_plus2 : forall n m k : nat, m <= k -> max n m <= k + n.
intros n m k H.
elim (le_dec n m); intro.
(*(le n m)*)
rewrite max_commutes; rewrite max_rew1; auto with *.

(*(le m n)*)
rewrite max_rew1; auto with *.
Qed.


Lemma le_max_plus : forall n m k : nat, n <= k -> max n m <= k + m.
do 4 intro.
elim (le_dec n m); intro.
(*(le n m)*)
rewrite max_commutes; rewrite max_rew1; auto with *.

(*(le m n)*)
rewrite max_rew1; auto with *.
Qed.
(***************************************************************************)

Lemma lt_succ_stamp : forall a : stamp, lt_stamp a (succ_stamp a).

Proof.
simple induction a; simpl in |- *; auto.
Qed.
Hint Resolve lt_succ_stamp.

(* maximum of two stamps *)
Definition max_stamp (st1 st2 : stamp) :=
  match st1, st2 with
  | Stamp n1, Stamp n2 => Stamp (max n1 n2)
  end.

Lemma max_stamp_n_n : forall a, 
max_stamp a a = a.
intro a;case a;simpl.
intro;rewrite max_n_n;reflexivity.
Qed.


Lemma max_stamp_commutes: forall a b,
max_stamp a b = max_stamp b a.
intros a b;destruct a;destruct b;simpl.
rewrite max_commutes;reflexivity.
Qed.


Lemma max_stamp_ass : forall a b c, 
 max_stamp a (max_stamp b c) = max_stamp (max_stamp a b) c.
intros a b c;destruct a;destruct b;destruct  c;simpl.
rewrite max_ass;reflexivity.
Qed.


Lemma le_stamp_max_l :
 forall st1 st2 : stamp, le_stamp st1 (max_stamp st1 st2).

Proof.
simple induction st1; simple induction st2; simpl in |- *; auto.
Qed.
Hint Resolve le_stamp_max_l.

Lemma le_stamp_max_r :
 forall st1 st2 : stamp, le_stamp st2 (max_stamp st1 st2).

Proof.
simple induction st1; simple induction st2; simpl in |- *; auto.
Qed.
Hint Resolve le_stamp_max_r.

Fixpoint max_list_stamp (l : list stamp) : stamp :=
  match l with
  | nil => Stamp 0
  | a :: l0 => max_stamp a (max_list_stamp l0)
  end.

Lemma in_list_max_stamp :
forall l x, in_list_stamp x l = true -> 
max_stamp x (max_list_stamp l) = max_list_stamp l.
Proof.
simple induction l.
simpl.
intros x Hpb. 
discriminate Hpb.
intros a l0 IH x0;simpl.
elim (stamp_dec x0 a);intro Heq.
rewrite Heq;rewrite eq_stamp_reflexivity;simpl.
intro h;clear h.
rewrite max_stamp_ass;rewrite max_stamp_n_n.
reflexivity.

rewrite (eq_stamp_diff x0 a Heq);simpl.
intro in_h.
rewrite max_stamp_commutes; rewrite <- max_stamp_ass.
setoid_rewrite max_stamp_commutes at 2.
rewrite (IH x0 in_h);reflexivity.
Qed.


Lemma lt_max_list :
 forall (l : list stamp) (x : stamp),
 in_list_stamp x l = true -> le_stamp x (max_list_stamp l).

Proof.
simple induction l.
(* l=[] *)
simpl in |- *; intros; discriminate H.
(* l=a::l0 *)
do 5 intro; simpl in |- *.
elim (in_list_cons_inv l0 x a H0).
(* x=a *)
intros eq_x_a; rewrite eq_x_a; auto.
(* (in_list_stamp x l0)=true *)
intro y;
 apply
  (le_stamp_trans x (max_list_stamp l0) (max_stamp a (max_list_stamp l0))
     (H x y) (le_stamp_max_r a (max_list_stamp l0))).
Qed.
Hint Resolve lt_max_list.


Lemma max_list_stamp_nil : max_list_stamp nil = Stamp 0.
auto.
Qed.

Lemma max_stamp_O : forall st : stamp, max_stamp (Stamp 0) st = st.
intro st; elim st; intro.
unfold max_stamp in |- *; rewrite max_O_m; auto.
Qed.

Lemma
  max_list_stamp_union_list :
    forall l1 l2 : list stamp,
    max_list_stamp (union_list_stamp l1 l2) =
    max_stamp (max_list_stamp l1) (max_list_stamp l2).
Proof.
induction l1;intros.
simpl union_list_stamp;simpl max_list_stamp.
rewrite max_stamp_O;reflexivity.
simpl.

case_eq (in_list_stamp a l2);intro Hcase;simpl.
rewrite <- max_stamp_ass.
setoid_rewrite max_stamp_commutes at 2.
rewrite max_stamp_ass.
rewrite (in_list_max_stamp l2 a Hcase).
rewrite max_stamp_commutes.
exact (IHl1 l2).

rewrite IHl1.
rewrite max_stamp_ass;reflexivity.
Qed.


Lemma le_stamp_succ_succ :
 forall st st' : stamp,
 le_stamp st st' -> le_stamp (succ_stamp st) (succ_stamp st').
intros st st'; elim st; intro n; elim st'; intro m.
simpl in |- *; auto with *.
Qed.