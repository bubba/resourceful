(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import langs.
Require Import subst.
Require Import FV.
Require Import DB_gen_stable.

(* Unification *)
Inductive unify_check : Set :=
  | Unification_error : unify_check
  | Some_unifier : substitution -> unify_check.

Lemma unify_check_inv :
 forall u : unify_check,
 {s : substitution | u = Some_unifier s} + {u = Unification_error}.

Proof.
simple induction u.
right; auto.
intros s; left; exists s; auto.
Qed.
(***********************************************************)

Parameter unify : type * type -> unify_check.

Axiom
  mgu_is_correct :
    forall (t1 t2 : type) (U : substitution),
    unify (t1, t2) = Some_unifier U ->
    extend_subst_type U t1 = extend_subst_type U t2.

(***********************************************************)

(* for completness  *)
Inductive unifier : substitution -> type -> type -> Prop :=
    unifier_intro :
      forall (mu : substitution) (t1 t2 : type),
      extend_subst_type mu t1 = extend_subst_type mu t2 -> unifier mu t1 t2.

Inductive has_mgu : type -> type -> substitution -> Prop :=
    intro_has_mgu :
      forall (t1 t2 : type) (s : substitution),
      {mu_sigma : substitution * substitution |
      unify (t1, t2) = Some_unifier (fst mu_sigma) /\
      s = compose_subst (fst mu_sigma) (snd mu_sigma)} -> 
      has_mgu t1 t2 s.

(***********************************************************)
Axiom
  mgu_is_complete :
    forall (t1 t2 : type) (s : substitution),
    unifier s t1 t2 -> has_mgu t1 t2 s.

(***********************************************************)

Axiom
  member_FV_mgu :
    forall (t1 t2 : type) (U : substitution) (x : stamp),
    unify (t1, t2) = Some_unifier U ->
    in_list_stamp x (FV_subst U) = true ->
    in_list_stamp x (union_list_stamp (FV_type t1) (FV_type t2)) = true.

(***********************************************************)