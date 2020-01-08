(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.
Require Import langs.
Require Import FV.
Require Import subst.

Inductive type_scheme : Set :=
  | Nat_ts : type_scheme
  | Var_ts : stamp -> type_scheme
  | Gen_var : stamp -> type_scheme
  | Arrow_ts : type_scheme -> type_scheme -> type_scheme.

Fixpoint type_to_type_scheme (t : type) : type_scheme :=
  match t with
  | Nat => Nat_ts
  | Var v => Var_ts v
  | Arrow tau1 tau2 =>
      Arrow_ts (type_to_type_scheme tau1) (type_to_type_scheme tau2)
  end.

Fixpoint extend_subst_type_scheme (s : substitution) 
 (ts : type_scheme) {struct ts} : type_scheme :=
  match ts with
  | Nat_ts => Nat_ts
  | Var_ts v => type_to_type_scheme (apply_substitution s v)
  | Gen_var v => Gen_var v
  | Arrow_ts ts1 ts2 =>
      Arrow_ts (extend_subst_type_scheme s ts1)
        (extend_subst_type_scheme s ts2)
  end.

Lemma type_to_type_scheme_commutes_with_subst :
 forall (t : type) (s : substitution),
 type_to_type_scheme (extend_subst_type s t) =
 extend_subst_type_scheme s (type_to_type_scheme t).

Proof.
simple induction t; auto.
intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed.

Lemma empty_subst_is_identity_on_type_scheme :
 forall sigma : type_scheme,
 extend_subst_type_scheme empty_subst sigma = sigma.

Proof.
simple induction sigma; auto.
intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed.

Lemma composition_of_substitutions_type_scheme :
 forall (s1 s2 : substitution) (ts : type_scheme),
 extend_subst_type_scheme (compose_subst s1 s2) ts =
 extend_subst_type_scheme s2 (extend_subst_type_scheme s1 ts).

Proof.
simple induction ts; auto.
(*Var_ts*)
simpl in |- *; intro.
rewrite composition_of_substitutions_stamp.
elim type_to_type_scheme_commutes_with_subst; auto.
(*Arrow_ts*)
intros; simpl in |- *.
rewrite H; rewrite H0; auto.
Qed.

Fixpoint FB_type_scheme (ts : type_scheme) : list stamp :=
  match ts with
  | Nat_ts => nil (A:=stamp)
  | Var_ts st => nil (A:=stamp)
  | Gen_var st =>  (*stamp*) st :: nil
  | Arrow_ts ts1 ts2 =>
      union_list_stamp (FB_type_scheme ts1) (FB_type_scheme ts2)
  end.

Fixpoint FV_type_scheme (ts : type_scheme) : list stamp :=
  match ts with
  | Nat_ts => nil (A:=stamp)
  | Var_ts st =>  (*stamp*) st :: nil
  | Gen_var st => nil (A:=stamp)
  | Arrow_ts ts1 ts2 =>
      union_list_stamp (FV_type_scheme ts1) (FV_type_scheme ts2)
  end.


Lemma extend_subst_ts_arrow_rewrite :
 forall (s : substitution) (ts1 ts2 : type_scheme),
 Arrow_ts (extend_subst_type_scheme s ts1) (extend_subst_type_scheme s ts2) =
 extend_subst_type_scheme s (Arrow_ts ts1 ts2).
auto.
Qed.