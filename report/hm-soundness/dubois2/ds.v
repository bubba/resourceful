(* Author : Catherine Dubois *)

(*****************************************************************************)
(*     ML values and contexts are defined with the following mutual       *)
(*     recursive definition                                                  *)
(*****************************************************************************)

Require Import langs.
Require Import tools_bool.
Require Import tools.

Inductive val : Set :=
  | Num : nat -> val
  | Closure : identifier -> expr -> ctx -> val
  | Rec_closure : identifier -> identifier -> expr -> ctx -> val
with ctx : Set :=
  | Cnil : ctx
  | Ccons : identifier -> val -> ctx -> ctx.

(*****************************************************************************)
(* Definition of assoc_ident_in_ctx which associates an identifier with 
its value *)
(*****************************************************************************)

Inductive ident_in_ctx : Set :=
  | Ident_not_in_ctx : ident_in_ctx
  | Ident_in_ctx : val -> ident_in_ctx.

Lemma ident_in_ctx_inv :
 forall i : ident_in_ctx,
 {v : val | i = Ident_in_ctx v} + {i = Ident_not_in_ctx}.
Proof.
simple induction i.
right; auto.
intro v; left; exists v; auto.
Qed.

Fixpoint assoc_ident_in_ctx (v : identifier) (c : ctx) {struct c} :
 ident_in_ctx :=
  match c with
  | Cnil => Ident_not_in_ctx
  | Ccons i vt l =>
      if_ ident_in_ctx (eq_identifier v i) (Ident_in_ctx vt)
        (assoc_ident_in_ctx v l)
  end.

(*****************************************************************************)
(*                   We define now the Mini-ML dynamic semantics 
                     in the style of Natural Semantics  *)
(*****************************************************************************)

Inductive val_of : ctx -> expr -> val -> Prop :=
  | Val_of_num : forall (n : nat) (c : ctx), val_of c (Const_nat n) (Num n)
  | Val_of_ident :
      forall (c : ctx) (i : identifier) (v : val),
      assoc_ident_in_ctx i c = Ident_in_ctx v -> val_of c (Variabl i) v
  | Val_of_lambda :
      forall (c : ctx) (i : identifier) (e : expr),
      val_of c (Lambda i e) (Closure i e c)
  | Val_of_rec :
      forall (c : ctx) (f i : identifier) (e : expr),
      val_of c (Rec f i e) (Rec_closure f i e c)
  | Val_of_apply :
      forall (c c1 : ctx) (e1 e2 e : expr) (i : identifier) (u v : val),
      val_of c e1 (Closure i e c1) ->
      val_of c e2 u -> val_of (Ccons i u c1) e v -> val_of c (Apply e1 e2) v
  | Val_of_apply_rec :
      forall (c c1 : ctx) (e1 e2 e : expr) (f i : identifier) (u v : val),
      val_of c e1 (Rec_closure f i e c1) ->
      val_of c e2 u ->
      val_of (Ccons f (Rec_closure f i e c1) (Ccons i u c1)) e v ->
      val_of c (Apply e1 e2) v
  | Val_of_let :
      forall (c : ctx) (i : identifier) (e1 e2 : expr) (u v : val),
      val_of c e1 u ->
      val_of (Ccons i u c) e2 v -> val_of c (Let_in i e1 e2) v.
