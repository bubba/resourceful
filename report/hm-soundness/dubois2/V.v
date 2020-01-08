(* Author : Catherine Dubois *)

Require Import langs.
Require Import tools.

Inductive V : Set :=
  | B : stamp -> V
  | F : stamp -> V.

Definition eq_V (v v' : V) :=
  match v, v' with
  | B n, B n' => eq_stamp n n'
  | F n, F n' => eq_stamp n n'
  | _, _ => false
  end.

Lemma V_dec : forall x1 x2 : V, {x1 = x2} + {x1 <> x2}.
simple induction x1; simple induction x2; intros.
elim (stamp_dec s s0).
intro eq; left; rewrite eq; auto.

unfold not in |- *; intros neq; right; intro eqs; apply neq; inversion eqs;
 auto.

right; unfold not in |- *; intro eq; discriminate eq.

right; unfold not in |- *; intro eq; discriminate eq.

elim (stamp_dec s s0).
intro eq; left; rewrite eq; auto.

unfold not in |- *; intros neq; right; intro eqs; apply neq; inversion eqs;
 auto.
Qed.

Lemma V_reflexivity : forall x : V, eq_V x x = true.
simple induction x; intro; simpl in |- *; auto.
Qed.

Lemma V_diff : forall x y : V, x <> y -> eq_V x y = false.
simple induction x; simple induction y; simpl in |- *; intros; auto.

apply eq_stamp_diff.
unfold not in |- *; unfold not in H.
intro; apply H.
rewrite H0; auto.

apply eq_stamp_diff.
unfold not in |- *; unfold not in H.
intro; apply H.
rewrite H0; auto.
Qed.