(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import tools.
Require Import tools_bool.
Require Import langs.
Require Import subst.
Require Import type_scheme.
Require Import FV.

Definition environment := list (identifier * type_scheme).

Fixpoint apply_subst_env (l : environment) (S : substitution) {struct l} :
 environment :=
  match l with
  | nil => l
  | liaison :: reste =>
       (*identifier*type_scheme *)
      (fst liaison, extend_subst_type_scheme S (snd liaison))
      :: apply_subst_env reste S
  end.

Lemma empty_subst_is_identity_on_env :
 forall env : environment, apply_subst_env env empty_subst = env. 

Proof.
simple induction env; auto.
simpl in |- *; intros.
elim a; intros; simpl in |- *.
rewrite empty_subst_is_identity_on_type_scheme.
rewrite H; auto.
Qed.

Lemma composition_of_substitutions_env :
 forall (s t : substitution) (env : environment),
 apply_subst_env env (compose_subst s t) =
 apply_subst_env (apply_subst_env env s) t.

Proof.
do 2 intro; simple induction env; auto.
simpl in |- *; intros.
rewrite H.
rewrite composition_of_substitutions_type_scheme; auto.
Qed.

Definition add_environment (env : environment) (x : identifier)
  (sigma : type_scheme) :=  (*identifier*type_scheme*) (x, sigma) :: env.

Inductive ident_in_env : Set :=
  | Ident_not_in_env : ident_in_env
  | Ident_in_env : type_scheme -> ident_in_env.

Lemma ident_in_env_inv :
 forall i : ident_in_env,
 {ts : type_scheme | i = Ident_in_env ts} + {i = Ident_not_in_env}.

Proof.
simple induction i.
right; auto.
intros ts; left; exists ts; auto.
Qed.

Fixpoint assoc_ident_in_env (v : identifier)
 (env : list (identifier * type_scheme)) {struct env} : ident_in_env :=
  match env with
  | nil (*identifier*type_scheme*) => Ident_not_in_env
  |  (*identifier*type_scheme*) vt :: l =>
      if_ ident_in_env (eq_identifier v (fst vt)) (Ident_in_env (snd vt))
        (assoc_ident_in_env v l)
  end.

Fixpoint FV_env (env : list (identifier * type_scheme)) : 
 list stamp :=
  match env with
  | nil => nil (A:=stamp)
  |  (*identifier*type_scheme*) vt :: l =>
      union_list_stamp (FV_type_scheme (snd vt)) (FV_env l)
  end.