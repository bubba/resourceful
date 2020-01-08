(* Author : Catherine Dubois *)

Require Import List.
Require Import langs.
Require Import tools.
Require Import type_scheme.
Require Import smallstep.
Require Import env_poly.
Require Import type_system.
Require Import generic_DB.

Definition empty_env := nil (A:=identifier * type_scheme).


Lemma ground_expr :
 forall (e : expr) (env : environment) (t : type),
 type_of env e t ->
 forall x : identifier,
 assoc_ident_in_env x env = Ident_not_in_env -> ~ est_libre x e.

simple induction e.

unfold not in |- *; intros.
inversion H1.

intros.
inversion_clear H.
unfold not in |- *; intros.
inversion H.
rewrite H5 in H0; rewrite H1 in H0.
discriminate H0.

intros.
inversion H0.
unfold not in |- *; intro libre_hyp.
inversion libre_hyp.
absurd (est_libre x e0); auto.
apply (H (add_environment env i (type_to_type_scheme t0)) t' H6 x).
simpl in |- *; rewrite H10; simpl in |- *; auto.

intros.
inversion H0.
unfold not in |- *; intro libre_hyp.
inversion libre_hyp.
absurd (est_libre x e0); auto.
apply
 (H
    (add_environment (add_environment env i0 (type_to_type_scheme t0)) i
       (type_to_type_scheme (Arrow t0 t'))) t' H7 x).
simpl in |- *; rewrite H12; rewrite H13; simpl in |- *; auto.

intros.
inversion H1.
unfold not in |- *; intro libre_hyp.
inversion libre_hyp.
absurd (est_libre x e0); auto.
exact (H env (Arrow t0 t) H6 x H2).
absurd (est_libre x e1); auto.
exact (H0 env t0 H8 x H2).

intros.
inversion H1.
unfold not in |- *; intro libre_hyp.
inversion libre_hyp.
absurd (est_libre x e0); auto.
exact (H env t0 H8 x H2).
absurd (est_libre x e1); auto.
apply (H0 (add_environment env i (gen_type t0 env)) t H9 x).
simpl in |- *; rewrite H13; simpl in |- *; auto.
Qed.

Lemma type_of_empty_ground :
 forall (e : expr) (t : type),
 type_of empty_env e t -> forall x : identifier, ~ est_libre x e.
Proof.
intros e t typing x; apply (ground_expr e empty_env t typing x).
auto.
Qed.

Lemma substitute_succeeds :
 forall (e e1 : expr) (i : identifier) (t1 : type),
 type_of empty_env e1 t1 ->
 est_valeur e1 -> exists e' : expr, substitute i e1 e e'.
Proof.
simple induction e.

(*n*)
intros.
exists (Const_nat n).
apply Const_subst.

(*var*)
intros.
elim (identifier_dec i i0).
intros i_is_i0; rewrite i_is_i0; exists e1.
apply Var_subst_eq.

intros i_is_not_i0.
exists (Variabl i).
apply Var_subst_diff.
apply eq_identifier_diff; auto.


(*abstraction*)
intros.
elim (identifier_dec i i0).
intro i_is_i0; rewrite i_is_i0.
exists (Lambda i0 e0).
apply Lambda_subst_eq.

intro i_is_not_i0.
elim (H e1 i0 t1 H0 H1).
intros e0' def_e0'.
exists (Lambda i e0').
apply Lambda_subst_diff; auto.
apply eq_identifier_diff; auto.

apply type_of_empty_ground with (t := t1); auto.

(*Recursive fonction*)
intros; elim (identifier_dec i i1).
intro i_is_i1; rewrite i_is_i1.
exists (Rec i1 i0 e0).
apply Rec_subst_eq_2.

intro i_is_not_i1.
elim (identifier_dec i0 i1).
intro i0_is_i1; rewrite i0_is_i1.
exists (Rec i i1 e0).
apply Rec_subst_eq_1.

intro i0_is_not_i1.
elim (H e1 i1 t1 H0 H1).
intros e0' def_e0'.
exists (Rec i i0 e0').
apply Rec_subst_diff; auto.
apply eq_identifier_diff; auto.
apply eq_identifier_diff; auto.
apply type_of_empty_ground with (t := t1); auto.
apply type_of_empty_ground with (t := t1); auto.

(*application*)
intros.
elim (H e2 i t1 H1 H2).
intros e0' def_e0'.
elim (H0 e2 i t1 H1 H2).
intros e1' def_e1'.
exists (Apply e0' e1').
apply Apply_subst; auto.

(*let*)
intros.
elim (H e2 i0 t1 H1 H2).
elim (identifier_dec i i0).
intro i_is_i0; rewrite <- i_is_i0; intros e0' def_e0'.
exists (Let_in i e0' e1).
apply Let_in_subst_eq; auto.

intros i_is_not_i0 e0' def_e0'.
elim (H0 e2 i0 t1 H1 H2).
intros e1' def_e1'.
exists (Let_in i e0' e1').
apply Let_in_subst_diff; auto.
apply type_of_empty_ground with (t := t1); auto.
apply eq_identifier_diff; auto.
Qed.


Lemma value_or_reduction :
 forall (e : expr) (t : type),
 type_of empty_env e t -> (exists e' : expr, reduction e e') \/ est_valeur e.

simple induction e.
(*constant*)
intros; right.
apply Constant_valeur.

(*identifier*)
intros; right.
inversion H.
simpl in H1; discriminate H1.

(*abstraction*)
intros; right.
apply Lambda_valeur.

(*recursive abstraction*)
intros; right.
apply Rec_valeur.

(*application e0 e1*)
intros.
inversion H1.
left.
elim (H (Arrow t0 t) H5).
(** there exists a reduction for e0*)
intro exists_red; elim exists_red.
intros e0' def_e0'.
exists (Apply e0' e1).
(*(reduction (Apply e0 e1) (Apply e0' e1))*)
apply
 (Context_red e0 e0' (fun x : expr => Apply x e1) def_e0'
    (app_left e1 (fun x : expr => x) trou)).


(** e0 is a value*)
intro Hyp_e0_value.
elim (H0 t0 H7).
(** there exists a reduction for e1*)
intro exists_red_e1; elim exists_red_e1.
intros e1' def_e1'.
exists (Apply e0 e1').
(*(reduction (Apply e0 e1) (Apply e0 e1'))*)
apply
 (Context_red e1 e1' (fun x : expr => Apply e0 x) def_e1'
    (app_right e0 Hyp_e0_value (fun x : expr => x) trou)).
(** e1 is a value*)
intro Hyp_e1_value.
inversion Hyp_e0_value.
(* first case (Const_nat n)=e0*)
rewrite <- H8 in H5. (* replace  e0 by n in the typing sequent H5*)
inversion H5.
(* second case (Lambda i e3)=e0*)
elim (substitute_succeeds e3 e1 i t0 H7 Hyp_e1_value).
intros e'' def_e''.
exists e''.
apply Lamb_apply_red_vrai; auto.
(* third case (Rec f i e3)= e0 *)
rewrite <- H8 in H5.
elim
 (substitute_succeeds e3 (Rec f i e3) f (Arrow t0 t) H5 (Rec_valeur f i e3)).
intros er def_er.
elim (substitute_succeeds er e1 i t0 H7 Hyp_e1_value).
intros er' def_er'.
exists er'.
apply Rec_apply_red_vrai with (er := er); auto.


(*Let in*)
intros.
inversion H1.
left.
elim (H t0 H7).
(** there exists a reduction for e0*)
intro exists_red; elim exists_red.
intros e0' def_e0'.
exists (Let_in i e0' e1).
apply
 (Context_red e0 e0' (fun x : expr => Let_in i x e1) def_e0'
    (let_left e1 i (fun x : expr => x) trou)).

(** e0 is a value*)
intro Hyp_e0_value.
elim (substitute_succeeds e1 e0 i t0 H7 Hyp_e0_value).
intros er def_er.
exists er.
apply Let_in_red_vrai; auto.
Qed.

Definition in_nf (e : expr) : Prop := forall v : expr, ~ reduction e v.

Theorem well_typed_exp_in_nf_is_a_value :
 forall (e : expr) (t : type),
 type_of empty_env e t -> in_nf e -> est_valeur e.
intros.
elim (value_or_reduction e t H); auto.

intros Hyp; elim Hyp.
unfold in_nf in H0.
intros e' def_e'.
absurd (reduction e e'); auto.
Qed.