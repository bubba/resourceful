(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Require Import tools.
Require Import List.
Require Import langs.
Require Import tools_bool.

Definition substitution := list (stamp * type).

Definition empty_subst : substitution := nil.

Inductive ident_in_subst : Set :=
  | Ident_not_in_subst : ident_in_subst
  | Ident_in_subst : type -> ident_in_subst.

Lemma ident_in_subst_inv :
 forall i : ident_in_subst,
 {t : type | i = Ident_in_subst t} + {i = Ident_not_in_subst}.

Proof.
simple induction i.
right; auto.
intros t; left; exists t; auto.
Qed.

Fixpoint assoc_stamp_in_subst (v : stamp) (s : substitution) {struct s} :
 ident_in_subst :=
  match s with
  | nil => Ident_not_in_subst
  | vt :: l =>
      if_ ident_in_subst (eq_stamp v (fst vt)) (Ident_in_subst (snd vt))
        (assoc_stamp_in_subst v l)
  end.

(* Substitution *)
Definition apply_substitution (s : substitution) (v : stamp) :=
  match assoc_stamp_in_subst v s with
  | Ident_not_in_subst => Var v
  | Ident_in_subst tau => tau
  end.

Fixpoint extend_subst_type (s : substitution) (t : type) {struct t} : type :=
  match t with
  | Nat => Nat
  | Var st => apply_substitution s st
  | Arrow t1 t2 => Arrow (extend_subst_type s t1) (extend_subst_type s t2)
  end.

Lemma empty_substitution_is_identity_on_type :
 forall t : type, extend_subst_type empty_subst t = t.

Proof.
simple induction t; auto.
(*Arrow*) intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed. 
(*Hint empty_substitution_is_identity_on_type.*)

(* Composition *)
Fixpoint mem_assoc (var : stamp) (subst1 : list (stamp * type))
 {struct subst1} : bool :=
  match subst1 with
  | nil => false
  | liaison :: rest1 =>
      if_ bool (eq_stamp var (fst liaison)) true (mem_assoc var rest1)
  end.

Lemma mem_assoc_in_subst :
 forall (st : stamp) (s : substitution),
 assoc_stamp_in_subst st s = Ident_not_in_subst -> mem_assoc st s = false.

Proof.
simple induction s.
(* s=[] *)
auto.
(* s=a::l *)
intros a l H; simpl in |- *.
elim (stamp_dec st (fst a)).
(* st=(Fst a) *)
intros eq_st_fst_a; rewrite eq_st_fst_a; rewrite eq_stamp_reflexivity.
intros wrong; discriminate wrong.
(* st<>(Fst a) *)
intros neq_st_fst_a; rewrite (eq_stamp_diff st (fst a) neq_st_fst_a); auto.
Qed.

Fixpoint subst_diff (s2 s1 : substitution) {struct s2} : substitution :=
  match s2 with
  | nil => nil (A:=stamp * type)
  | var2 :: rest2 =>
      if_ (list (stamp * type)) (mem_assoc (fst var2) s1)
        (subst_diff rest2 s1)
        ( (*(stamp * type)*) var2 :: subst_diff rest2 s1)
  end.

Lemma subst_diff_nil : forall s : substitution, subst_diff s nil = s.

Proof.
simple induction s; simpl in |- *.
(* s=[] *)
auto.
(* s=a::l *)
intros; rewrite H; auto.
Qed.

Lemma if_ident_in_subst :
 forall (st1 st2 : stamp) (t : type) (i : ident_in_subst),
 if_ ident_in_subst (eq_stamp st1 st2) (Ident_in_subst t) i =
 Ident_not_in_subst -> eq_stamp st1 st2 = false /\ i = Ident_not_in_subst.

Proof.
intros st1 st2 t i.
elim (bool_dec (eq_stamp st1 st2)).
(* (eq_stamp st1 st2)=true *)
intros eq_st1_st2; rewrite eq_st1_st2; simpl in |- *.
intros H; discriminate H.
(* (eq_stamp st1 st2)=false *)
intros eq_st1_st2; rewrite eq_st1_st2.
simpl in |- *.
auto.
Qed.

Lemma assoc_stamp_in_subst_diff :
 forall (s1 s2 : substitution) (st : stamp) (t : type),
 assoc_stamp_in_subst st s1 = Ident_in_subst t ->
 assoc_stamp_in_subst st s2 = Ident_not_in_subst ->
 assoc_stamp_in_subst st (subst_diff s1 s2) = Ident_in_subst t.

Proof.
simple induction s1; simpl in |- *.
(* s1=[] *)
auto.
(* s1=a::l1 *)
intros a l H1 s2 st t.
elim (stamp_dec st (fst a)).
(* st=(Fst a)) *)
intros eq_st_fst_a; rewrite eq_st_fst_a; rewrite eq_stamp_reflexivity;
 simpl in |- *.
intros H2 H3.
rewrite (mem_assoc_in_subst (fst a) s2 H3); simpl in |- *.
rewrite eq_stamp_reflexivity; simpl in |- *; auto.
(* st<>(Fst a) *)
intros neq_st_fst_a; rewrite (eq_stamp_diff st (fst a) neq_st_fst_a);
 simpl in |- *.
elim (bool_dec (mem_assoc (fst a) s2)).
(* (mem_assoc (Fst a) s2)=true *)
intros mem_fst_a_s2; rewrite mem_fst_a_s2; simpl in |- *.
intros H2 H3; apply (H1 s2 st t H2 H3).
(* (mem_assoc (Fst a) s2)=false *)
intros not_mem_fst_a_s2; rewrite not_mem_fst_a_s2; simpl in |- *.
rewrite (eq_stamp_diff st (fst a) neq_st_fst_a); simpl in |- *.
intros H2 H3.
apply (H1 s2 st t H2 H3).
Qed.

Lemma assoc_stamp_in_subst_diff3 :
 forall (l l0 : substitution) (st : stamp) (a : stamp * type),
 assoc_stamp_in_subst st l0 = Ident_not_in_subst ->
 assoc_stamp_in_subst st (subst_diff l0 ( (*stamp*type*) a :: l)) =
 Ident_not_in_subst.

Proof.
simple induction l0; simpl in |- *; auto.
(* l= a0::l1 *)
intros; elim (stamp_dec (fst a) (fst a0)).
(* (Fst a) = (Fst a0) *)
intros eq_fst_a_a0; rewrite eq_fst_a_a0;
 rewrite (eq_stamp_reflexivity (fst a0)); simpl in |- *.
apply (H st a0).
elim (if_ident_in_subst st (fst a) (snd a) (assoc_stamp_in_subst st l1) H0);
 intros; assumption.
(* (Fst a) <> (Fst a0) *)
intros neq_fst_a_a0; rewrite (eq_stamp_diff (fst a) (fst a0) neq_fst_a_a0);
 simpl in |- *.
elim (bool_dec (mem_assoc (fst a) l)).
(* (mem_assoc (Fst a) l)=true *)
intros mem_fst_a_l; rewrite mem_fst_a_l; simpl in |- *.
apply (H st a0).
elim (if_ident_in_subst st (fst a) (snd a) (assoc_stamp_in_subst st l1) H0);
 intros; assumption.
(* (mem_assoc (Fst a) l)=false *)
intros mem_fst_a_l; rewrite mem_fst_a_l; simpl in |- *.
elim (if_ident_in_subst st (fst a) (snd a) (assoc_stamp_in_subst st l1) H0);
 intros.
rewrite H1; simpl in |- *.
apply (H st a0 H2).
Qed.

Lemma assoc_stamp_in_subst_diff4 :
 forall (s1 s2 : substitution) (st : stamp) (liaison : stamp * type),
 assoc_stamp_in_subst st (subst_diff s2 s1) = Ident_not_in_subst ->
 assoc_stamp_in_subst st (subst_diff s2 ( (*stamp*type*) liaison :: s1)) =
 Ident_not_in_subst.

Proof.
simple induction s2.
(* s2=[] *)
simpl in |- *; auto.
(* s2=a::l *)
simpl in |- *; intros.
elim (stamp_dec (fst a) (fst liaison)).
(* (Fst a)=(Fst liaison) *)
intros eq_fst; rewrite eq_fst; rewrite (eq_stamp_reflexivity (fst liaison)). 
simpl in |- *.
apply (H st liaison).
generalize H0.
elim (bool_dec (mem_assoc (fst a) s1)).
(* (mem_assoc (Fst a) s1)=true *)
intros mem_fst_a_s1; rewrite mem_fst_a_s1; simpl in |- *; auto.
(* (mem_assoc (Fst a) s1)=false *)
intros mem_fst_a_s1; rewrite mem_fst_a_s1; simpl in |- *; intros.
elim
 (if_ident_in_subst st (fst a) (snd a)
    (assoc_stamp_in_subst st (subst_diff l s1)) H1); 
 auto.
(* (Fst a)<>(Fst liaison) *)
intros neq_fst; rewrite (eq_stamp_diff (fst a) (fst liaison) neq_fst);
 simpl in |- *.
generalize H0; elim (bool_dec (mem_assoc (fst a) s1)).
(* (mem_assoc (Fst a) s1)=true *)
intros mem_fst_a_s1; rewrite mem_fst_a_s1; simpl in |- *.
intros H1; apply (H st liaison H1).
(* (mem_assoc (Fst a) s1)=false *)
intros mem_fst_a_s1; rewrite mem_fst_a_s1; simpl in |- *.
elim (stamp_dec st (fst a)).
(* st=(Fst a) *)
intros eq_st_fst_a; rewrite eq_st_fst_a;
 rewrite (eq_stamp_reflexivity (fst a)); simpl in |- *; 
 auto.
(* st<>(Fst a) *)
intros neq_st_fst_a; rewrite (eq_stamp_diff st (fst a) neq_st_fst_a);
 simpl in |- *.
intros H1; apply (H st liaison H1).
Qed.

Lemma assoc_stamp_in_subst_diff5 :
 forall (s2 l : substitution) (a : stamp * type) (t : type),
 assoc_stamp_in_subst (fst a) ( (*stamp*type*) a :: l) = Ident_in_subst t ->
 assoc_stamp_in_subst (fst a) (subst_diff s2 ( (*stamp*type*) a :: l)) =
 Ident_not_in_subst.

Proof.
simple induction s2; simpl in |- *; auto.
intros a l H l0 a0 t.
rewrite (eq_stamp_reflexivity (fst a0)); simpl in |- *.
intros H0; inversion H0.
elim (stamp_dec (fst a) (fst a0)).
(* (Fst a)=(Fst a0) *)
intros eq_fst; rewrite eq_fst; simpl in |- *.
rewrite (eq_stamp_reflexivity (fst a0)); simpl in |- *.
apply (H l0 a0 (snd a0)).
rewrite (eq_stamp_reflexivity (fst a0)); simpl in |- *; auto.
(* (Fst a)<>(Fst a0) *)
intros neq_fst; rewrite (eq_stamp_diff (fst a) (fst a0) neq_fst);
 simpl in |- *.
elim (bool_dec (mem_assoc (fst a) l0)).
(* (mem_assoc (Fst a) l0)=true *)
intros mem_fst_a_l0; rewrite mem_fst_a_l0; simpl in |- *.
apply (H l0 a0 (snd a0)).
rewrite (eq_stamp_reflexivity (fst a0)); simpl in |- *; auto.
(* (mem_assoc (Fst a) l0)=false *)
intros mem_fst_a_l0; rewrite mem_fst_a_l0; simpl in |- *.
rewrite (eq_stamp_diff (fst a0) (fst a)); simpl in |- *.
apply (H l0 a0 (snd a0)).
rewrite (eq_stamp_reflexivity (fst a0)); simpl in |- *; auto.
auto.
Qed.

Lemma assoc_stamp_in_subst_diff6 :
 forall (s1 s2 : substitution) (st : stamp) (liaison : stamp * type),
 st <> fst liaison ->
 assoc_stamp_in_subst st (subst_diff s2 ( (*stamp*type*) liaison :: s1)) =
 assoc_stamp_in_subst st (subst_diff s2 s1).

Proof.
simple induction s2; simpl in |- *; auto.
intros; simpl in |- *.
elim (stamp_dec (fst a) (fst liaison)).
(* (Fst a) = (Fst liaison) *)
intros eq_fst; rewrite eq_fst; rewrite (eq_stamp_reflexivity (fst liaison));
 simpl in |- *.
rewrite (H st liaison H0).
elim (bool_dec (mem_assoc (fst liaison) s1)).
(* (mem_assoc (Fst liaison) s1)=true *)
intros mem_fst_s1; rewrite mem_fst_s1; simpl in |- *; auto.
(* (mem_assoc (Fst liaison) s1)=false *)
intros mem_fst_s1; rewrite mem_fst_s1; simpl in |- *.
rewrite eq_fst; rewrite (eq_stamp_diff st (fst liaison) H0); simpl in |- *;
 auto.
(* (Fst a) <> (Fst liaison) *)
intros neq_fst; rewrite (eq_stamp_diff (fst a) (fst liaison) neq_fst);
 simpl in |- *.
elim (bool_dec (mem_assoc (fst a) s1)).
(* (mem_assoc (Fst a) s1)=true *)
intros mem_fst_s1; rewrite mem_fst_s1; simpl in |- *; auto.
(* (mem_assoc (Fst a) s1)=false *)
intros mem_fst_s1; rewrite mem_fst_s1; simpl in |- *.
elim (stamp_dec st (fst a)).
(* st = (Fst a) *)
intros eq_st_fst_a; rewrite eq_st_fst_a;
 rewrite (eq_stamp_reflexivity (fst a)); simpl in |- *; 
 auto.
(* st <> (Fst a) *)
intros neq_st_fst_a; rewrite (eq_stamp_diff st (fst a) neq_st_fst_a);
 simpl in |- *.
apply (H st liaison H0).
Qed.

Lemma assoc_stamp_in_subst_app :
 forall (s1 s2 : substitution) (st : stamp) (t : type),
 assoc_stamp_in_subst st s1 = Ident_not_in_subst ->
 assoc_stamp_in_subst st s2 = Ident_in_subst t ->
 assoc_stamp_in_subst st ( (*stamp*type*) s1 ++ s2) = Ident_in_subst t.

Proof. 
intros.
generalize H; elim s1; simpl in |- *.
(* s1=[] *)
auto.
(* s1=a::l *) 
intros.
elim (if_ident_in_subst st (fst a) (snd a) (assoc_stamp_in_subst st l) H2).
intros neq_st_fst_a; rewrite neq_st_fst_a.
simpl in |- *.
assumption.
Qed.

Lemma assoc_stamp_in_subst_app2 :
 forall (s1 s2 : substitution) (st : stamp) (t : type),
 assoc_stamp_in_subst st s1 = Ident_in_subst t ->
 assoc_stamp_in_subst st ( (*stamp*type*) s1 ++ s2) = Ident_in_subst t.

Proof. 
intros s1 s2 st t.
elim s1.
(* s1 = [] *)
simpl in |- *; intros H0; discriminate H0.
(* s1=a::l *)
simpl in |- *; intros a l H.
elim (bool_dec (eq_stamp st (fst a))).
(* (eq_stamp st (Fst a))=true *)
intros eq_st_fst_a; rewrite eq_st_fst_a; simpl in |- *; auto.
(* (eq_stamp st (Fst a))=false *)
intros neq_st_fst_a; rewrite neq_st_fst_a; simpl in |- *.
assumption.
Qed.

Lemma assoc_stamp_in_subst_app3 :
 forall (s1 s2 : substitution) (st : stamp),
 assoc_stamp_in_subst st s1 = Ident_not_in_subst ->
 assoc_stamp_in_subst st s2 = Ident_not_in_subst ->
 assoc_stamp_in_subst st ( (*stamp*type*) s1 ++ s2) = Ident_not_in_subst.

Proof.
simple induction s1.
(* s1 = [] *)
simpl in |- *; auto.
(* s1=a::l *)
simpl in |- *; intros.
elim (if_ident_in_subst st (fst a) (snd a) (assoc_stamp_in_subst st l) H0).
intros.
rewrite H2; simpl in |- *.
apply (H s2 st H3 H1).
Qed.

Lemma assoc_stamp_in_subst_app3_inversion :
 forall (s1 s2 : substitution) (st : stamp),
 assoc_stamp_in_subst st ( (*stamp*type*) s1 ++ s2) = Ident_not_in_subst ->
 assoc_stamp_in_subst st s1 = Ident_not_in_subst /\
 assoc_stamp_in_subst st s2 = Ident_not_in_subst.

Proof.
simple induction s1.
(* s1 = [] *)
simpl in |- *; auto.
(* s1=a::l *)
simpl in |- *; intros.
elim
 (if_ident_in_subst st (fst a) (snd a)
    (assoc_stamp_in_subst st ( (*stamp*type*) l ++ s2)) H0).
intros.
rewrite H1; simpl in |- *.
apply (H s2 st H2).
Qed.

Lemma assoc_stamp_in_subst_app4_inversion :
 forall (s1 s2 : substitution) (st : stamp) (t : type),
 assoc_stamp_in_subst st ( (*stamp*type*) s1 ++ s2) = Ident_in_subst t ->
 assoc_stamp_in_subst st s1 = Ident_in_subst t \/
 assoc_stamp_in_subst st s1 = Ident_not_in_subst /\
 assoc_stamp_in_subst st s2 = Ident_in_subst t.

Proof.
simple induction s1; simpl in |- *; auto.
intros a l H s2 st t.
elim (stamp_dec st (fst a)).
(* st=(Fst a) *)
intros eq_st_fst_a; rewrite eq_st_fst_a;
 rewrite (eq_stamp_reflexivity (fst a)); simpl in |- *.
left; auto.
(* st<>(Fst a) *)
intros neq_st_fst_a; rewrite (eq_stamp_diff st (fst a) neq_st_fst_a);
 simpl in |- *.
intros.
apply (H s2 st t H0).
Qed.

Fixpoint apply_subst_list (s1 s2 : substitution) {struct s1} :
 substitution :=
  match s1 with
  | nil => nil (A:=stamp * type)
  | liaison :: rest =>
       (*(stamp * type)*) 
      (fst liaison, extend_subst_type s2 (snd liaison))
      :: apply_subst_list rest s2
  end.

Lemma assoc_stamp_in_apply_subst_list :
 forall (s1 s2 : substitution) (st : stamp) (a : stamp * type),
 eq_stamp st (fst a) = false ->
 assoc_stamp_in_subst st (apply_subst_list s1 s2) = Ident_not_in_subst ->
 assoc_stamp_in_subst st (apply_subst_list s1 ( (*stamp*type*) a :: s2)) =
 Ident_not_in_subst.

Proof.
simple induction s1; simpl in |- *; intros.
(* s1 = [] *)
auto.
(* s1 = a::l *)
elim (stamp_dec st (fst a)).
(* st=(Fst a) *)
intros eq_st_fst_a; generalize H1; elim eq_st_fst_a;
 rewrite (eq_stamp_reflexivity st); simpl in |- *.
intros H2; discriminate H2.
(* st <> (Fst a) *)
intros H2. rewrite (eq_stamp_diff st (fst a) H2); simpl in |- *.
apply (H s2 st a0 H0).
elim
 (if_ident_in_subst st (fst a) (extend_subst_type s2 (snd a))
    (assoc_stamp_in_subst st (apply_subst_list l s2)) H1); 
 auto.
Qed.

Lemma assoc_stamp_in_apply_subst_list_inversion2 :
 forall (s1 s2 : substitution) (st : stamp) (a : stamp * type),
 assoc_stamp_in_subst st (apply_subst_list ( (*stamp*type*) a :: s1) s2) =
 Ident_not_in_subst ->
 assoc_stamp_in_subst st (apply_subst_list s1 s2) = Ident_not_in_subst.

Proof.
simpl in |- *; intros.
elim
 (if_ident_in_subst st (fst a) (extend_subst_type s2 (snd a))
    (assoc_stamp_in_subst st (apply_subst_list s1 s2)) H); 
 auto.
Qed.

Lemma extend_subst_type_nil : forall t : type, extend_subst_type nil t = t.

Proof.
simple induction t; simpl in |- *; auto.
intros.
rewrite H; rewrite H0.
auto.
Qed.

Lemma apply_subst_list_nil :
 forall s : substitution, apply_subst_list s nil = s.

Proof.
simple induction s; simpl in |- *; auto.
intros.
rewrite (extend_subst_type_nil (snd a)).
rewrite H.
elim a; auto.
Qed.

Definition compose_subst (s1  (* apply s1 and then s2 *)
                          s2 : substitution) :=
   (*(stamp * type)*) subst_diff s2 s1 ++ apply_subst_list s1 s2.

Lemma assoc_in_compose_subst_yes :
 forall (s1 s2 : substitution) (liaison : stamp * type) 
   (st : stamp) (t : type),
 st <> fst liaison ->
 assoc_stamp_in_subst st (compose_subst s1 s2) = Ident_in_subst t ->
 assoc_stamp_in_subst st (compose_subst ( (*stamp*type*) liaison :: s1) s2) =
 Ident_in_subst t.

Proof.
unfold compose_subst in |- *.
simpl in |- *.
intros.
elim
 (assoc_stamp_in_subst_app4_inversion (subst_diff s2 s1)
    (apply_subst_list s1 s2) st t H0).
(* (assoc_stamp_in_subst st (subst_diff s2 s1))=(Ident_in_subst t) *)
intros H1.
apply assoc_stamp_in_subst_app2.
rewrite (assoc_stamp_in_subst_diff6 s1 s2 st liaison H); assumption.
(* (assoc_stamp_in_subst st (subst_diff s2 s1))=Ident_not_in_subst
   /\ (assoc_stamp_in_subst st (apply_subst_list s1 s2))=(Ident_in_subst t) *)
intros H1. elim H1; intros H2 H3.
apply assoc_stamp_in_subst_app.
rewrite (assoc_stamp_in_subst_diff6 s1 s2 st liaison H); assumption.
simpl in |- *.
rewrite (eq_stamp_diff st (fst liaison) H); simpl in |- *; assumption.
Qed.

Lemma assoc_in_compose_subst_no :
 forall (s1 s2 : substitution) (liaison : stamp * type) (st : stamp),
 st <> fst liaison ->
 assoc_stamp_in_subst st (compose_subst s1 s2) = Ident_not_in_subst ->
 assoc_stamp_in_subst st (compose_subst ( (*stamp*type*) liaison :: s1) s2) =
 Ident_not_in_subst.

Proof.
unfold compose_subst in |- *.
simpl in |- *.
intros.
apply assoc_stamp_in_subst_app3.
elim
 (assoc_stamp_in_subst_app3_inversion (subst_diff s2 s1)
    (apply_subst_list s1 s2) st H0); intros.
apply (assoc_stamp_in_subst_diff4 s1 s2 st liaison H1).
simpl in |- *; rewrite (eq_stamp_diff st (fst liaison) H); simpl in |- *.
elim
 (assoc_stamp_in_subst_app3_inversion (subst_diff s2 s1)
    (apply_subst_list s1 s2) st); auto.
Qed.

Lemma assoc_in_compose_subst :
 forall (s1 s2 : substitution) (liaison : stamp * type) (st : stamp),
 st <> fst liaison ->
 assoc_stamp_in_subst st (compose_subst ( (*stamp*type*) liaison :: s1) s2) =
 assoc_stamp_in_subst st (compose_subst s1 s2).

Proof.
intros s1 s2 liaison st.
elim (ident_in_subst_inv (assoc_stamp_in_subst st (compose_subst s1 s2))).
(* (assoc_stamp_in_subst st (compose_subst s1 s2))=(Ident_in_subst t) *)
intros H; elim H; intros t Pt; rewrite Pt.
intros.
apply (assoc_in_compose_subst_yes s1 s2 liaison st t H0 Pt).
(* (assoc_stamp_in_subst st (compose_subst s1 s2))=Ident_not_in_subst *)
intros H H0.
rewrite H.
apply (assoc_in_compose_subst_no s1 s2 liaison st H0 H).
Qed.

Lemma assoc_in_compose_subst2 :
 forall (s1 s2 : substitution) (st : stamp),
 assoc_stamp_in_subst st s1 = Ident_not_in_subst ->
 assoc_stamp_in_subst st (compose_subst s1 s2) = assoc_stamp_in_subst st s2.

Proof.
simple induction s1.
(* s1=[] *)
unfold compose_subst in |- *.
simpl in |- *.
intros.
rewrite (subst_diff_nil s2).
elim (app_nil_end (*stamp*type*)  s2).
auto.
(* s1=a::l *)
simpl in |- *; intros.
elim (if_ident_in_subst st (fst a) (snd a) (assoc_stamp_in_subst st l) H0).
intros.
unfold compose_subst in |- *.
elim (ident_in_subst_inv (assoc_stamp_in_subst st s2)).
(* (assoc_stamp_in_subst st s2)=(Ident_in_subst t) *)
intros H3; elim H3; intros t Pt.
rewrite
 (assoc_stamp_in_subst_app2 (subst_diff s2 ( (*stamp*type*) a :: l))
    (apply_subst_list ( (*stamp*type*) a :: l) s2) st t)
 .
auto.
apply (assoc_stamp_in_subst_diff s2 ( (*stamp*type*) a :: l) st t Pt).
simpl in |- *; rewrite H1; simpl in |- *.
assumption.
(* (assoc_stamp_in_subst st s2)=Ident_not_in_subst *)
intros y; rewrite y.
generalize y.
elim s2.
(* s2 = [] *)
simpl in |- *; rewrite H1; simpl in |- *.
rewrite (apply_subst_list_nil l).
intros; assumption.
(* s2 = a0::l0 *)
intros.
elim (stamp_dec (fst a0) (fst a)).
(* (Fst a0)=(Fst a) *)
intros eq_fst_a0_a; simpl in |- *; rewrite eq_fst_a0_a.
rewrite (eq_stamp_reflexivity (fst a)); simpl in |- *.
apply
 (assoc_stamp_in_subst_app3 (subst_diff l0 ( (*stamp*type*) a :: l))
    ( (*stamp*type*) (fst a,
                     extend_subst_type ( (*stamp*type*) a0 :: l0) (snd a))
     :: apply_subst_list l ( (*stamp*type*) a0 :: l0)) st).
elim
 (assoc_stamp_in_subst_app3_inversion
    (subst_diff l0 ( (*stamp*type*) a :: l))
    (apply_subst_list ( (*stamp*type*) a :: l) l0) st).
auto.
apply H3.
generalize y0; simpl in |- *; intros H4;
 elim
  (if_ident_in_subst st (fst a0) (snd a0) (assoc_stamp_in_subst st l0) H4);
 intros; assumption.
simpl in |- *; rewrite H1; simpl in |- *.
apply (assoc_stamp_in_apply_subst_list l l0 st a0).
rewrite eq_fst_a0_a; assumption.
apply (assoc_stamp_in_apply_subst_list_inversion2 l l0 st a).
elim
 (assoc_stamp_in_subst_app3_inversion
    (subst_diff l0 ( (*stamp*type*) a :: l))
    (apply_subst_list ( (*stamp*type*) a :: l) l0) st); 
 auto.
apply H3.
generalize y0; simpl in |- *; intros H4;
 elim
  (if_ident_in_subst st (fst a0) (snd a0) (assoc_stamp_in_subst st l0) H4);
 intros; assumption.
(* (Fst a0)<>(Fst a) *)
intros neq_fst_a0_a; simpl in |- *;
 rewrite (eq_stamp_diff (fst a0) (fst a) neq_fst_a0_a); 
 simpl in |- *.
apply assoc_stamp_in_subst_app3.
elim (bool_dec (mem_assoc (fst a0) l)).
(* (mem_assoc (Fst a0) l)=true *)
intros mem_fst_a0_l; rewrite mem_fst_a0_l; simpl in |- *.
apply (assoc_stamp_in_subst_diff3 l l0 st a).
generalize y0; simpl in |- *; intros H4;
 elim
  (if_ident_in_subst st (fst a0) (snd a0) (assoc_stamp_in_subst st l0) H4);
 intros; assumption.
(* (mem_assoc (Fst a0) l)=false *)
intros mem_fst_a0_l; rewrite mem_fst_a0_l; simpl in |- *.
generalize y0; simpl in |- *; intros H4;
 elim
  (if_ident_in_subst st (fst a0) (snd a0) (assoc_stamp_in_subst st l0) H4);
 intros.
rewrite H5; simpl in |- *.
apply (assoc_stamp_in_subst_diff3 l l0 st a H6).
(* no more hypothesis on (mem_assoc (Fst a0) l) *)
simpl in |- *; rewrite H1; simpl in |- *.
apply (assoc_stamp_in_apply_subst_list l l0 st a0).
generalize y0; simpl in |- *; intros H4;
 elim
  (if_ident_in_subst st (fst a0) (snd a0) (assoc_stamp_in_subst st l0) H4);
 auto.
apply (assoc_stamp_in_apply_subst_list_inversion2 l l0 st a).
elim
 (assoc_stamp_in_subst_app3_inversion
    (subst_diff l0 ( (*stamp*type*) a :: l))
    (apply_subst_list ( (*stamp*type*) a :: l) l0) st); 
 auto.
apply H3.
generalize y0; simpl in |- *; intros H4;
 elim
  (if_ident_in_subst st (fst a0) (snd a0) (assoc_stamp_in_subst st l0) H4);
 auto.
Qed.

Lemma composition_of_substitutions_stamp :
 forall (s1 s2 : substitution) (st : stamp),
 apply_substitution (compose_subst s1 s2) st =
 extend_subst_type s2 (apply_substitution s1 st).

Proof.
intros.
elim (ident_in_subst_inv (assoc_stamp_in_subst st s1)).
(* Ident_in_subst t *)
intro y; elim y; intros x y0.
unfold apply_substitution in |- *.
rewrite y0.
generalize y0; elim s1.
intros; discriminate y1.
intros; simpl in |- *.
elim (stamp_dec st (fst a)).
(* (eq_stamp st (Fst a))=true *)
intros eq_st_fst_a. 
unfold compose_subst in |- *.
rewrite eq_st_fst_a.
rewrite
 (assoc_stamp_in_subst_app (subst_diff s2 ( (*stamp*type*) a :: l))
    (apply_subst_list ( (*stamp*type*) a :: l) s2) 
    (fst a) (extend_subst_type s2 x)).
auto.
apply (assoc_stamp_in_subst_diff5 s2 l a x).
elim eq_st_fst_a; assumption.
unfold apply_subst_list in |- *; simpl in |- *;
 rewrite (eq_stamp_reflexivity (fst a)); simpl in |- *.
generalize y1; elim eq_st_fst_a; simpl in |- *; rewrite eq_st_fst_a;
 rewrite (eq_stamp_reflexivity (fst a)); simpl in |- *; 
 intros H0; inversion H0; auto.
(* (eq_stamp st (Fst a))=false *)
intros neq_st_fst_a.
rewrite (assoc_in_compose_subst l s2 a st neq_st_fst_a).
apply H.
generalize y1; simpl in |- *.
rewrite (eq_stamp_diff st (fst a) neq_st_fst_a).
simpl in |- *; auto.
(* Ident_not_in_subst *)
intro y.
unfold apply_substitution in |- *.
rewrite y.
rewrite (assoc_in_compose_subst2 s1 s2 st y).
simpl in |- *; auto.
Qed.

Lemma composition_of_substitutions_type :
 forall (s1 s2 : substitution) (t : type),
 extend_subst_type (compose_subst s1 s2) t =
 extend_subst_type s2 (extend_subst_type s1 t).

Proof.
simple induction t; auto.
(*Var*)
intro; simpl in |- *; rewrite composition_of_substitutions_stamp; auto.
(*Arrow*)
intros; simpl in |- *; rewrite H; rewrite H0; auto.
Qed.

Lemma apply_subst_arrow_rewrite :
 forall (s : substitution) (t1 t2 : type),
 Arrow (extend_subst_type s t1) (extend_subst_type s t2) =
 extend_subst_type s (Arrow t1 t2).

Proof.
auto.
Qed.
Hint Immediate apply_subst_arrow_rewrite.

Lemma apply_subst_stp_rewrite :
 forall (s : substitution) (x : stamp),
 apply_substitution s x = extend_subst_type s (Var x).

Proof.
auto.
Qed.
Hint Immediate apply_subst_stp_rewrite.

Lemma apply_subst_arrow_rewrite2 :
 forall (s : substitution) (st1 st2 : stamp),
 Arrow (apply_substitution s st1) (apply_substitution s st2) =
 extend_subst_type s (Arrow (Var st1) (Var st2)).

Proof.
auto.
Qed.
Hint Immediate apply_subst_arrow_rewrite2.