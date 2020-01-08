(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import langs.
Require Import subst.
Require Import type_scheme.
Require Import env_poly.
Require Import unification.
Require Import generic_DB.
Require Import DB_stable_gen_instance.

Inductive infer_check : Set :=
  | Infer_error : infer_check
  | Some_infer : type -> substitution -> stamp -> infer_check.

Lemma infer_check_inv :
 forall i : infer_check,
 {t_s_st : type * substitution * stamp |
 match t_s_st with
 | (t_s, st) => match t_s with
                | (t, s) => i = Some_infer t s st
                end
 end} + {i = Infer_error}.

Proof.
simple induction i.
right; auto.
intros t s st; left; exists (t, s, st); auto.
Qed.

Fixpoint W (st : stamp) (env : environment) (e : expr) {struct e} :
 infer_check :=
  match e with
  | Const_nat n => Some_infer Nat empty_subst st
  | Variabl x =>
      match assoc_ident_in_env x env with
      | Ident_not_in_env => Infer_error
      | Ident_in_env sigma =>
          match compute_generic_subst st (max_gen_vars sigma) with
          | (l, st') =>
              match apply_subst_gen l sigma with
              | Error_subst_gen => Infer_error
              | Some_subst_gen t => Some_infer t empty_subst st'
              end
          end
      end
  | Lambda x e' =>
      match st with
      | Stamp n =>
          match
            W (Stamp (S n)) (add_environment env x (Var_ts (Stamp n))) e'
          with
          | Infer_error => Infer_error
          | Some_infer t s st2 =>
              Some_infer (Arrow (extend_subst_type s (Var (Stamp n))) t) s
                st2
          end
      end
  | Rec f x e' =>
      match st with
      | Stamp n =>
          match
            W (Stamp (S (S n)))
              (add_environment (add_environment env x (Var_ts (Stamp n))) f
                 (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n))))) e'
          with
          | Infer_error => Infer_error
          | Some_infer t s st3 =>
              match unify (t, extend_subst_type s (Var (Stamp (S n)))) with
              | Unification_error => Infer_error
              | Some_unifier U =>
                  Some_infer
                    (extend_subst_type (compose_subst s U)
                       (Arrow (Var (Stamp n)) (Var (Stamp (S n)))))
                    (compose_subst s U) st3
              end
          end
      end
  | Apply e1 e2 =>
      match W st env e1 with
      | Infer_error => Infer_error
      | Some_infer t1 S1 st1 =>
          match W st1 (apply_subst_env env S1) e2 with
          | Infer_error => Infer_error
          | Some_infer t2 S2 st2 =>
              match st2 with
              | Stamp n =>
                  match
                    unify (extend_subst_type S2 t1, Arrow t2 (Var (Stamp n)))
                  with
                  | Unification_error => Infer_error
                  | Some_unifier U =>
                      Some_infer (extend_subst_type U (Var (Stamp n)))
                        (compose_subst (compose_subst S1 S2) U) 
                        (Stamp (S n))
                  end
              end
          end
      end
  | Let_in x e1 e2 =>
      match W st env e1 with
      | Infer_error => Infer_error
      | Some_infer t1 S1 st1 =>
          match
            W st1
              (add_environment (apply_subst_env env S1) x
                 (gen_type t1 (apply_subst_env env S1))) e2
          with
          | Infer_error => Infer_error
          | Some_infer t2 S2 st2 => Some_infer t2 (compose_subst S1 S2) st2
          end
      end
  end.


