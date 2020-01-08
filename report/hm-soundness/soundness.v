Require Import Coq.Strings.String.
Require Import dubois.subst.

Inductive type: Set := TUnit: type
                     | TVar: stamp -> type
                     | TArrow: type -> type -> type.

Inductive type_scheme: Set := Unit_ts: type_scheme
                            | Gen_var: stamp -> type_scheme
                            | Var_ts: stamp -> type_scheme
                            | Arrow_ts: type_scheme -> type_scheme -> type_scheme.

Definition type_env := list (ident * type_scheme).
Definition substitution := list (stamp * type).

Fixpoint type_to_type_scheme (t : type): type_scheme :=
  match t with
    TUnit => Unit_ts
  | TVar s => Var_ts s
  | TArrow t1 t2 => Arrow_ts (type_to_type_scheme t1) (type_to_type_scheme t2)
  end.

Fixpoint apply_subst_tscheme (s : substitution) (ts: type_scheme): type_scheme :=
  match ts with
    Unit_ts => Unit_ts
  | (Gen_var v) => (Gen_var v)
  | (Var_ts v) => type_to_type_scheme (apply_substitution s v)
  | (Arrow_ts ts1 ts2) => (Arrow_ts (apply_subst_tscheme s ts1)
                                   (apply_subst_tscheme s ts2))
  end.

Definition more_general : type_scheme -> type_scheme -> Prop
  := [ts1, ts2: type_scheme]
       (forall t: type (is_gen_instance t ts2) -> (is_gen_instance t ts1)).
                                                                
                                         

