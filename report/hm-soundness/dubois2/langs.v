(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import List.

Inductive identifier : Set :=
    Ident : nat -> identifier.

Inductive expr : Set :=
  | Const_nat : nat -> expr
  | Variabl : identifier -> expr
  | Lambda : identifier -> expr -> expr
  | Rec : identifier -> identifier -> expr -> expr
  | Apply : expr -> expr -> expr
  | Let_in : identifier -> expr -> expr -> expr.

Inductive stamp : Set :=
    Stamp : nat -> stamp.

Lemma stamp_inv : forall s : stamp, {n : nat | s = Stamp n}.

Proof.
simple induction s; intros n; exists n; auto.
Qed.

Inductive type : Set :=
  | Nat : type
  | Var : stamp -> type
  | Arrow : type -> type -> type.

Lemma list_type_and_stamp_inv :
 forall lt_st : list type * stamp,
 {lt_st1 : list type * stamp | lt_st1 = lt_st}.

Proof.
intros lt_st; exists lt_st; auto.
Qed.

