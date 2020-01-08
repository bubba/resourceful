From Coq Require Import Strings.String.

Module STLC.

  Inductive ty : Type :=
  | Bool : ty
  | Arrow : ty -> ty -> ty.

  Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.
  

  Open Scope string_scope.
  Definition x := "x".
  Definition y := "y".
  Definition z := "z".

  (* Hint Unfold x. *)

  Notation idB := (abs x Bool (var x)).
  Notation idBB := (abs x (Arrow Bool Bool) (var x)).

  Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.

  Reserved Notation "'[' x ':=' s ']' t" (at level 20).

  Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    | var x' =>
      if eqb x x' then s else t
    | abs x' T t_1 =>
      abs x' T (if eqb x x' then t_1 else ([x:=s] t_1))
    | app t_1 t_2 =>
      app ([x:=s] t_1) ([x:=s] t_2)
    | tru => tru
    | fls => fls
    | test t_1 t_2 t_3 =>
      test ([x:=s] t_1) ([x:=s] t_2) ([x:=s] t_3)
    end
  where "'[' x ':=' s ']' t" := (subst x s t).
  
