(* Author : Catherine Dubois *)

Require Import type_scheme.
Require Import langs.
Require Import subst.
Require Import env_poly.
Require Import generic_DB.
Require Import unification.
Require Import W.

Lemma W_var_inversion :
 forall (st st' : stamp) (env : environment) (i : identifier) 
   (t : type) (s : substitution),
 W st env (Variabl i) = Some_infer t s st' ->
 {ts : type_scheme |
 s = empty_subst /\
 assoc_ident_in_env i env = Ident_in_env ts /\
 apply_subst_gen (fst (compute_generic_subst st (max_gen_vars ts))) ts =
 Some_subst_gen t /\ snd (compute_generic_subst st (max_gen_vars ts)) = st'}.

Proof.
simpl in |- *; do 6 intro.
elim (ident_in_env_inv (assoc_ident_in_env i env)).
(* (assoc_ident_in_env i env)=(Ident_in_env ts) *)
intros Ex_ts; elim Ex_ts; intros ts Pts.
rewrite Pts; simpl in |- *.
elim (list_type_and_stamp_inv (compute_generic_subst st (max_gen_vars ts))).
intros lt_st; elim lt_st; intros lt st2 Plt_st2.
elim Plt_st2; simpl in |- *. 
elim (subst_gen_answer_inv (apply_subst_gen lt ts)).
(* (apply_subst_gen lt ts)=(Some_subst_gen t0) *)
intros Ex_t0; elim Ex_t0; intros t0 Pt0.
rewrite Pt0; simpl in |- *.
intros.
exists ts.
inversion H.
split; auto.
split; auto.
split; elim H1; elim Pt0; elim Plt_st2; auto.
(* (apply_subst_gen lt ts)=Error_subst_gen *)
intros wrong; rewrite wrong; intros H; discriminate H.
(* (assoc_ident_in_env i env)=Ident_not_in_env *)
intros wrong; rewrite wrong; intros H; discriminate H.
Qed.

Lemma W_lambda_inversion :
 forall (n : nat) (st' : stamp) (env : environment) 
   (e0 : expr) (i : identifier) (t : type) (s : substitution),
 W (Stamp n) env (Lambda i e0) = Some_infer t s st' ->
 {t1 : type |
 W (Stamp (S n)) (add_environment env i (Var_ts (Stamp n))) e0 =
 Some_infer t1 s st' /\ t = Arrow (extend_subst_type s (Var (Stamp n))) t1}.

Proof.
simpl in |- *; do 7 intro.
elim
 (infer_check_inv
    (W (Stamp (S n)) (add_environment env i (Var_ts (Stamp n))) e0)). 
(* (W  (Stamp (S n)) (add_environment env i (Var_ts (Stamp n))) e0)=
          (Some_infer t' s' st') *)
intros Ex_t_s_st2. elim Ex_t_s_st2; intros t_s_st2; elim t_s_st2; intros t_s st2; elim t_s;
  intros t' s' P_t_s_st.
rewrite P_t_s_st.
intros H; inversion H.
exists t'.
split; auto.
(* (W  (Stamp (S n)) (add_environment env i (Var_ts (Stamp n))) e0)=
   Infer_error *)
intros wrong; rewrite wrong; intros H; discriminate H.
Qed.

Lemma W_rec_inversion :
 forall (n : nat) (st' : stamp) (env : environment) 
   (e : expr) (f x : identifier) (t : type) (s : substitution),
 W (Stamp n) env (Rec f x e) = Some_infer t s st' ->
 {tau_subst_u : type * (substitution * substitution) |
 match tau_subst_u with
 | (tau, subst_u) =>
     match subst_u with
     | (subst, u) =>
         W (Stamp (S (S n)))
           (add_environment (add_environment env x (Var_ts (Stamp n))) f
              (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n))))) e =
         Some_infer tau subst st' /\
         unify (tau, extend_subst_type subst (Var (Stamp (S n)))) =
         Some_unifier u /\
         s = compose_subst subst u /\
         extend_subst_type s (Arrow (Var (Stamp n)) (Var (Stamp (S n)))) = t
     end
 end}.

Proof.
simpl in |- *; do 8 intro.
elim
 (infer_check_inv
    (W (Stamp (S (S n)))
       (add_environment (add_environment env x (Var_ts (Stamp n))) f
          (Arrow_ts (Var_ts (Stamp n)) (Var_ts (Stamp (S n))))) e)).
(* Some_infer *)
intros Ex_tau_subst_st2; elim Ex_tau_subst_st2; intros tau_subst_st2;
 elim tau_subst_st2; intros tau_subst st2; elim tau_subst;
 intros tau subst Ptau_subst_st2.
rewrite Ptau_subst_st2; simpl in |- *.
elim (unify_check_inv (unify (tau, apply_substitution subst (Stamp (S n))))).
(* Some_unifier *)
intros Ex_u; elim Ex_u; intros u Pu; rewrite Pu; simpl in |- *.
intros Eq1; inversion Eq1.
exists (tau, (subst, u)).
split; auto.
(* Unification_error *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
(* Infer_error *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
Qed.

Lemma W_apply_inversion :
 forall (st st' : stamp) (env : environment) (e0 e1 : expr) 
   (t : type) (s : substitution),
 W st env (Apply e0 e1) = Some_infer t s st' ->
 {t1_s1_st1_t2_s2_n2_u
 : type * substitution * stamp * (type * substitution * nat) * substitution |
 match t1_s1_st1_t2_s2_n2_u with
 | (t1_s1_st1_t2_s2_n2, u) =>
     match t1_s1_st1_t2_s2_n2 with
     | (t1_s1_st1, t2_s2_n2) =>
         match t1_s1_st1, t2_s2_n2 with
         | (t1_s1, st1), (t2_s2, n2) =>
             match t1_s1, t2_s2 with
             | (t1, s1), (t2, s2) =>
                 W st env e0 = Some_infer t1 s1 st1 /\
                 W st1 (apply_subst_env env s1) e1 =
                 Some_infer t2 s2 (Stamp n2) /\
                 unify (extend_subst_type s2 t1, Arrow t2 (Var (Stamp n2))) =
                 Some_unifier u /\
                 t = extend_subst_type u (Var (Stamp n2)) /\
                 s = compose_subst (compose_subst s1 s2) u /\
                 st' = Stamp (S n2)
             end
         end
     end
 end}.

Proof.
simpl in |- *; do 7 intro.
elim (infer_check_inv (W st env e0)).
(* (W st env e0)=Some_infer... *)
intros Ex_t_s_st2; elim Ex_t_s_st2; intros t_s_st2; elim t_s_st2;
 intros t_s2 st2; elim t_s2; intros t2 s2 Pt_s_st2.
rewrite Pt_s_st2; simpl in |- *.
elim (infer_check_inv (W st2 (apply_subst_env env s2) e1)).
(* (W st2 (apply_subst_env env s2) e1)=Some_infer... *)
intros Ex_t_s_st3; elim Ex_t_s_st3; intros t_s_st3; elim t_s_st3;
 intros t_s3 st3; elim t_s3; intros t3 s3 Pt_s_st3.
rewrite Pt_s_st3; simpl in |- *.
elim (stamp_inv st3); intros n Pn; rewrite Pn; simpl in |- *.
elim
 (unify_check_inv (unify (extend_subst_type s3 t2, Arrow t3 (Var (Stamp n))))).
(* Some_unifier *)
intros Ex_u; elim Ex_u; intros u Pu; rewrite Pu; simpl in |- *.
intros Eq1; inversion Eq1.
exists (t2, s2, st2, (t3, s3, n), u).
split; auto.
split. elim Pn; auto.
split; auto.
(* Unify_error *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
(* (W st2 (apply_subst_env env s2) e1)=Infer_error *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
(* (W st env e0)=Infer_error *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
Qed.

Lemma W_let_inversion :
 forall (st st' : stamp) (env : environment) (e1 e2 : expr) 
   (x : identifier) (t : type) (s : substitution),
 W st env (Let_in x e1 e2) = Some_infer t s st' ->
 {t1_s1_st1_s2 : type * substitution * stamp * substitution |
 match t1_s1_st1_s2 with
 | (t1_s1_st1, s2) =>
     match t1_s1_st1 with
     | (t1_s1, st1) =>
         match t1_s1 with
         | (t1, s1) =>
             W st env e1 = Some_infer t1 s1 st1 /\
             W st1
               (add_environment (apply_subst_env env s1) x
                  (gen_type t1 (apply_subst_env env s1))) e2 =
             Some_infer t s2 st' /\ s = compose_subst s1 s2
         end
     end
 end}.

Proof.
simpl in |- *; do 8 intro.
elim (infer_check_inv (W st env e1)).
(* (W st env e)=Some_infer... *)
intros Ex_t_s_st2; elim Ex_t_s_st2; intros t_s_st2; elim t_s_st2;
 intros t_s2 st2; elim t_s2; intros t2 s2 Pt_s_st2; 
 rewrite Pt_s_st2; simpl in |- *.
elim
 (infer_check_inv
    (W st2
       (add_environment (apply_subst_env env s2) x
          (gen_type t2 (apply_subst_env env s2))) e2)).
(* (W st2 ... e0)=Some_infer... *)
intros Ex_t_s_st3; elim Ex_t_s_st3; intros t_s_st3; elim t_s_st3;
 intros t_s3 st3; elim t_s3; intros t3 s3 Pt_s_st3; 
 rewrite Pt_s_st3; simpl in |- *.
intros Eq1; inversion Eq1.
exists (t2, s2, st2, s3).
split; elim H2; elim H0; auto.
(* (W st2 ... e0)=Infer_error... *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
(* (W st env e)=Infer_error... *)
intros wrong; rewrite wrong; intros wrong2; discriminate wrong2.
Qed.