(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import langs.
Require Import env_poly.
Require Import type_scheme.
Require Import generic_DB.

Inductive type_of : environment -> expr -> type -> Prop :=
  | type_of_int_const :
      forall (env : environment) (n : nat), type_of env (Const_nat n) Nat
  | type_of_var :
      forall (env : environment) (x : identifier) (t : type)
        (ts : type_scheme),
      assoc_ident_in_env x env = Ident_in_env ts ->
      is_gen_instance t ts -> type_of env (Variabl x) t
  | type_of_lambda :
      forall (env : environment) (x : identifier) (e : expr) (t t' : type),
      type_of (add_environment env x (type_to_type_scheme t)) e t' ->
      type_of env (Lambda x e) (Arrow t t')
  | type_of_rec_fun :
      forall (env : environment) (f x : identifier) (e : expr) (t t' : type),
      type_of
        (add_environment (add_environment env x (type_to_type_scheme t)) f
           (type_to_type_scheme (Arrow t t'))) e t' ->
      type_of env (Rec f x e) (Arrow t t')
  | type_of_app :
      forall (env : environment) (e e' : expr) (t t' : type),
      type_of env e (Arrow t t') ->
      type_of env e' t -> type_of env (Apply e e') t'
  | type_of_let_in :
      forall (env : environment) (e e' : expr) (x : identifier) (t t' : type),
      type_of env e t ->
      type_of (add_environment env x (gen_type t env)) e' t' ->
      type_of env (Let_in x e e') t'.

Hint Resolve type_of_int_const.


