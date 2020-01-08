(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import type_scheme.
Require Import env_poly.
Require Import subst.
Require Import langs.
Require Import tools.

Lemma Ident_in_apply_subst_env :
 forall (env : environment) (i : identifier) (s : substitution)
   (ts : type_scheme),
 assoc_ident_in_env i env = Ident_in_env ts ->
 assoc_ident_in_env i (apply_subst_env env s) =
 Ident_in_env (extend_subst_type_scheme s ts).

Proof.
simple induction env.
simpl in |- *; intros; discriminate H.
do 6 intro; elim a; intros y y0.
elim (identifier_dec y i); intro eq_y_i.
(*y=i*)
simpl in |- *; rewrite eq_y_i; rewrite eq_identifier_reflexivity; intro H0.
inversion_clear H0; auto.
(*y<>i*)
simpl in |- *; rewrite eq_identifier_diff; auto.
simpl in |- *; intro; apply H; auto.
Qed.

Lemma subst_add_type_scheme :
 forall (env : environment) (i : identifier) (s : substitution)
   (ts : type_scheme),
 apply_subst_env (add_environment env i ts) s =
 add_environment (apply_subst_env env s) i (extend_subst_type_scheme s ts).

Proof.
auto.
Qed.

Lemma subst_add_type :
 forall (env : environment) (i : identifier) (s : substitution) (t : type),
 apply_subst_env (add_environment env i (type_to_type_scheme t)) s =
 add_environment (apply_subst_env env s) i
   (type_to_type_scheme (extend_subst_type s t)).

Proof.
intros.
rewrite subst_add_type_scheme.
elim type_to_type_scheme_commutes_with_subst; auto.
Qed.

Lemma subst_add_type_var :
 forall (env : environment) (i : identifier) (s : substitution) (st : stamp),
 apply_subst_env (add_environment env i (type_to_type_scheme (Var st))) s =
 add_environment (apply_subst_env env s) i
   (type_to_type_scheme (apply_substitution s st)).

Proof.
intros.
change
  (apply_subst_env (add_environment env i (type_to_type_scheme (Var st))) s =
   add_environment (apply_subst_env env s) i
     (type_to_type_scheme (extend_subst_type s (Var st)))) 
 in |- *.
apply subst_add_type.
Qed.
