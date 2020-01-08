(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import Lt.
Require Import Le.
Require Import langs.

Definition succ_stamp (st : stamp) :=
  match st with
  | Stamp n => Stamp (S n)
  end.

Fixpoint map_plus2 (l : list stamp) (m : nat) {struct l} : 
 list stamp :=
  match l with
  | nil => nil (A:=stamp)
  | Stamp n :: l' => Stamp (m + n) :: map_plus2 l' m
  end.

Definition lt_stamp (st1 st2 : stamp) :=
  match st1, st2 with
  | Stamp n1, Stamp n2 => n1 < n2
  end.
Hint Unfold lt_stamp.

Definition le_stamp (st1 st2 : stamp) :=
  match st1, st2 with
  | Stamp n1, Stamp n2 => n1 <= n2
  end.
Hint Unfold le_stamp.

Lemma le_stamp_eq : forall st : stamp, le_stamp st st.

Proof.
simple induction st; auto.
Qed.
Hint Resolve le_stamp_eq.

Lemma lt_le_stamp :
 forall st1 st2 : stamp, lt_stamp st1 st2 -> le_stamp st1 st2.

Proof.
simple induction st1; simple induction st2; auto with *.
Qed.
Hint Resolve lt_le_stamp.

Lemma lt_stamp_S1 :
 forall (st : stamp) (n : nat),
 lt_stamp st (Stamp n) -> lt_stamp st (Stamp (S n)).

Proof.
simple induction st; auto.
Qed.
Hint Resolve lt_stamp_S1.

Lemma lt_stamp_n_Sn : forall n : nat, lt_stamp (Stamp n) (Stamp (S n)).

Proof.
simpl in |- *; auto.
Qed.
Hint Resolve lt_stamp_n_Sn.

Lemma lt_n_m_diff : forall n m : nat, n < m -> n <> m.

Proof.
simple induction n; simple induction m; auto with *.
Qed.
Hint Immediate lt_n_m_diff.

Lemma lt_stamp_n_m_diff :
 forall st1 st2 : stamp, lt_stamp st1 st2 -> st1 <> st2.

Proof.
simple induction st1; simple induction st2; simpl in |- *; intros;
 hnf in |- *; intros; apply (lt_n_m_diff n n0 H); inversion H0; 
 auto.
Qed.
Hint Immediate lt_stamp_n_m_diff.

Lemma lt_le_stamp_trans :
 forall st1 st2 st3 : stamp,
 lt_stamp st1 st2 -> le_stamp st2 st3 -> lt_stamp st1 st3.

Proof.
simple induction st1; simple induction st2; simple induction st3;
 simpl in |- *; intros.
apply (lt_le_trans n n0 n1 H H0).
Qed.
Hint Immediate lt_le_stamp_trans.

Lemma le_lt_stamp_trans :
 forall st1 st2 st3 : stamp,
 le_stamp st1 st2 -> lt_stamp st2 st3 -> lt_stamp st1 st3.

Proof.
simple induction st1; simple induction st2; simple induction st3;
 simpl in |- *; intros.
apply (le_lt_trans n n0 n1 H H0).
Qed.
Hint Immediate le_lt_stamp_trans.

Lemma le_stamp_trans :
 forall st1 st2 st3 : stamp,
 le_stamp st1 st2 -> le_stamp st2 st3 -> le_stamp st1 st3.

Proof.
simple induction st1; simple induction st2; simple induction st3;
 simpl in |- *; intros.
apply (le_trans n n0 n1 H H0).
Qed.

Lemma lt_stamp_trans :
 forall st1 st2 st3 : stamp,
 lt_stamp st1 st2 -> lt_stamp st2 st3 -> lt_stamp st1 st3.

Proof.
simple induction st1; simple induction st2; simple induction st3;
 simpl in |- *; intros.
apply (lt_trans n n0 n1 H H0).
Qed.