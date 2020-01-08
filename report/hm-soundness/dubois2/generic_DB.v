(* Author : Catherine Dubois *)

Require Import langs.
Require Import tools.
Require Import tools_bool.
Require Import List.
Require Import type_scheme.
Require Import FV.
Require Import Minus.
Require Import Le.
Require Import env_poly.
Require Import max.
Require Import disjoints.
Require Import order_stamp.

(***************************************************************************)
(* linear encoding of the type scheme in gen_type*)
(***************************************************************************)

Inductive nth_answer : Set :=
  | Type_not_in : nth_answer
  | Nth_in : type -> nth_answer.

Lemma nth_answer_inv :
 forall n : nth_answer, {t : type | n = Nth_in t} + {n = Type_not_in}.

Proof.
simple induction n.
(* Type_not_in *)
auto.
(* Nth_in *)
intros t; left; exists t; auto.
Qed.

Fixpoint nth (n : nat) (l : list type) {struct l} : nth_answer :=
  match l with
  | nil => Type_not_in
  | x :: y => match n with
              | O => Nth_in x
              | S p => nth p y
              end
  end.

Inductive subst_gen_answer : Set :=
  | Error_subst_gen : subst_gen_answer
  | Some_subst_gen : type -> subst_gen_answer.

Fixpoint apply_subst_gen (s : list type) (ts : type_scheme) {struct ts} :
 subst_gen_answer :=
  match ts with
  | Nat_ts => Some_subst_gen Nat
  | Var_ts v => Some_subst_gen (Var v)
  | Gen_var (Stamp x) =>
      match nth x s with
      | Type_not_in => Error_subst_gen
      | Nth_in t => Some_subst_gen t
      end
  | Arrow_ts ts1 ts2 =>
      match apply_subst_gen s ts1 with
      | Error_subst_gen => Error_subst_gen
      | Some_subst_gen t1 =>
          match apply_subst_gen s ts2 with
          | Error_subst_gen => Error_subst_gen
          | Some_subst_gen t2 => Some_subst_gen (Arrow t1 t2)
          end
      end
  end.

 
Lemma subst_gen_answer_inv :
 forall s : subst_gen_answer,
 {t : type | s = Some_subst_gen t} + {s = Error_subst_gen}.

Proof.
simple induction s.
right; auto.
intros t; left; exists t; auto.
Qed.


Fixpoint max_gen_vars (ts : type_scheme) : nat :=
  match ts with
  | Nat_ts => 0
  | Var_ts s => 0
  | Gen_var (Stamp n) => S n
  | Arrow_ts ts1 ts2 => max (max_gen_vars ts1) (max_gen_vars ts2)
  end.
(*(max_gen_vars ts) = O  means no generic variables
 (max_gen_vars ts) = (S p) means p is the greatest genericc variables appearing in ts*)
 
Lemma apply_subst_gen_arrow_is_some_inversion3 :
 forall (ts1 ts2 : type_scheme) (t : type) (x : list type),
 apply_subst_gen x (Arrow_ts ts1 ts2) = Some_subst_gen t ->
 {t1_t2 : type * type |
 let (t1, t2) return Prop := t1_t2 in
 apply_subst_gen x ts1 = Some_subst_gen t1 /\
 apply_subst_gen x ts2 = Some_subst_gen t2 /\ t = Arrow t1 t2}.
intros ts1 ts2 t x; simpl in |- *.
elim (apply_subst_gen x ts1).
intro pb; discriminate pb.

intro t1; elim (apply_subst_gen x ts2).
intro pb; discriminate pb.

intros t2 eq1.
exists (t1, t2).
inversion eq1; auto.
Qed.

(*********************************************************************)
Lemma apply_subst_gen_type_to_type_scheme :
 forall (s : list type) (t : type),
 apply_subst_gen s (type_to_type_scheme t) = Some_subst_gen t.

Proof.
simple induction t; auto.
intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed.

(*********************************************************************)
Inductive is_gen_instance : type -> type_scheme -> Prop :=
    gen_instance_intro :
      forall (t : type) (ts : type_scheme),
      {sg : list type | apply_subst_gen sg ts = Some_subst_gen t} ->
      is_gen_instance t ts.

(***********************************************************************)

Lemma nth_le :
 forall (sg : list type) (n : nat) (x : type),
 nth n sg = Nth_in x -> S n <= length sg.
simple induction sg.
simpl in |- *; intros n x pb; discriminate pb.

simpl in |- *; intros a l hyp_ind n x; case n.
intro; apply le_n_S.
auto with *.

intros; apply le_n_S.
apply (hyp_ind n0 x H).

Qed.
Hint Resolve nth_le.

(***********************************************************************)
Lemma is_gen_instance_le_max :
 forall (ts : type_scheme) (t : type) (sg : list type),
 apply_subst_gen sg ts = Some_subst_gen t -> max_gen_vars ts <= length sg.
simple induction ts; auto with *.

intros st t sg; elim st; intro n; simpl in |- *.
elim (nth_answer_inv (nth n sg)).
intro H; elim H; clear H; intros x x_def; rewrite x_def; eauto.

intro nth_rwt; rewrite nth_rwt; intro pb; discriminate pb.

intros ts1 ind1 ts2 ind2 t sg Hyp.
elim (apply_subst_gen_arrow_is_some_inversion3 ts1 ts2 t sg Hyp).
intro x; elim x; intros t1 t2 y; elim y; intros; elim H0; intros;
 simpl in |- *.
elim (max_case (max_gen_vars ts1) (max_gen_vars ts2)); intro max_def;
 rewrite max_def.
apply (ind1 t1 sg H).

apply (ind2 t2 sg H1).
Qed.
Hint Resolve is_gen_instance_le_max.

(**************
 generalization 
***************)
Inductive index_answer : Set :=
  | Stamp_not_in : index_answer
  | Index_in : nat -> index_answer.

Fixpoint index (l : list stamp) (v : stamp) {struct l} : index_answer :=
  match l with
  | nil => Stamp_not_in
  | a :: r =>
      if_ index_answer (eq_stamp v a) (Index_in 0)
        match index r v with
        | Stamp_not_in => Stamp_not_in
        | Index_in n => Index_in (S n)
        end
  end.

Fixpoint gen_aux (t : type) (env : environment) (l : list stamp) {struct t} :
 type_scheme * list stamp :=
  match t with
  | Nat => (Nat_ts, l)
  | Var v =>
      if_ (type_scheme * list stamp) (in_list_stamp v (FV_env env))
        (Var_ts v, l)
        match index l v with
        | Stamp_not_in => (Gen_var (Stamp (length l)), l ++ v :: nil)
        | Index_in k => (Gen_var (Stamp k), l)
        end
  | Arrow t1 t2 =>
      match gen_aux t1 env l with
      | (ts1, l1) =>
          match gen_aux t2 env l1 with
          | (ts2, l2) => (Arrow_ts ts1 ts2, l2)
          end
      end
  end.

Definition gen_type (t : type) (env : environment) := fst (gen_aux t env nil).

Fixpoint gen_vars (t : type) (env : environment) {struct t} : 
 list stamp :=
  match t with
  | Nat => nil (A:=stamp)
  | Var v => if_ (list stamp) (in_list_stamp v (FV_env env)) nil (v :: nil)
  | Arrow t1 t2 => union_list_stamp (gen_vars t1 env) (gen_vars t2 env)
  end.

Lemma free_and_bound_are_disjoints :
 forall (env : environment) (t : type),
 are_disjoints (gen_vars t env) (FV_env env).

Proof.
simple induction t.
(* Nat *)
simpl in |- *; auto.
(* Var s *)
intros; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro is_in_list;
 rewrite is_in_list; simpl in |- *; auto.
(* Arrow t0 t1 *)
intros; simpl in |- *.
apply disjoint_list_and_union; auto.
Qed.

(*A property of gen_type*)
Lemma gen_type_add_env_aux :
 forall (env : environment) (ts : type_scheme) (y : identifier) 
   (t : type) (l : list stamp),
 are_disjoints (gen_vars t env) (FV_type_scheme ts) ->
 gen_aux t env l = gen_aux t (add_environment env y ts) l.
simple induction t; auto.
intros; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro y0; rewrite y0;
 simpl in |- *.
rewrite
 (in_second_componant_union_list_stamp (FV_type_scheme ts) (FV_env env) s y0)
 .
simpl in |- *; auto.

simpl in H; rewrite y0 in H; simpl in H.
rewrite not_in_list_union_inversion; auto.

simpl in |- *; intros.
rewrite (H l).
elim (gen_aux t0 (add_environment env y ts) l); intros a b.
rewrite (H0 b); auto.

apply are_disjoints_symetry.
apply disjoint_list_and_union_inversion2 with (l1 := gen_vars t0 env).
apply are_disjoints_symetry; auto.

apply are_disjoints_symetry.
apply disjoint_list_and_union_inversion1 with (l2 := gen_vars t1 env).
apply are_disjoints_symetry; auto.
Qed.



Lemma gen_type_add_env :
 forall (env : environment) (t : type) (ts : type_scheme) (y : identifier),
 are_disjoints (gen_vars t env) (FV_type_scheme ts) ->
 gen_type t env = gen_type t (add_environment env y ts).
Proof.
unfold gen_type in |- *; intros.
generalize (gen_type_add_env_aux env ts y t nil H).
elim (gen_aux t env nil); elim (gen_aux t (add_environment env y ts) nil).
simpl in |- *; intros.
injection H0; auto.
Qed.

(***********************
 fresh generic instance 
***********************)
Fixpoint compute_generic_subst (st : stamp) (n : nat) {struct n} :
 list type * stamp :=
  match n with
  | O => (nil, st)
  | S p =>
      match compute_generic_subst (succ_stamp st) p with
      | (l, st') => (Var st :: l, st')
      end
  end.


Lemma Fst_compute_generic_subst :
 forall (n : nat) (st : stamp),
 fst (compute_generic_subst st (S n)) =
 Var st :: fst (compute_generic_subst (succ_stamp st) n).

Proof.
intros; simpl in |- *.
elim (list_type_and_stamp_inv (compute_generic_subst (succ_stamp st) n)).
intros c; elim c; intros lt st' Pc.
elim Pc; simpl in |- *; auto.
Qed.

Lemma length_compute_generic_subst :
 forall (n : nat) (st : stamp), length (fst (compute_generic_subst st n)) = n.

Proof.
simple induction n.
(* n=O *)
auto.
(* n=(S n0) *)
intros; rewrite Fst_compute_generic_subst; simpl in |- *.
rewrite (H (succ_stamp st)); auto.
Qed.

(******************************************************************)
Lemma Snd_compute_generic_subst :
 forall (n : nat) (st : stamp),
 snd (compute_generic_subst st (S n)) =
 snd (compute_generic_subst (succ_stamp st) n).

Proof.
intros; simpl in |- *.
elim (list_type_and_stamp_inv (compute_generic_subst (succ_stamp st) n)).
intro c; elim c; intros lt st' Pc.
elim Pc; simpl in |- *; auto.
Qed.