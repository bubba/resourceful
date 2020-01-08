(* Author : Catherine Dubois *)

Require Import List.
Require Import tools_bool.
Require Import langs.
Require Import tools.
Require Import env_poly.
Require Import type_scheme.
Require Import type_system.
Require Import generic_DB.
Require Import subst.
Require Import DB_stable_gen_instance.
Require Import DB_gen_stable.
Require Import FV.
Require Import subset.
Require Import disjoints.
Require Import tools_more_general.
Require Import stable.
Require Import more_general.
Require Import DMnew.
Require Import s_env_when_s_disjoint_with_env3.
Require Import tools_stable.
Require Import subset_FV_env.

Fixpoint inverse_rename (r : list (stamp * stamp)) : 
 list (stamp * stamp) :=
  match r with
  | nil => nil (A:=stamp * stamp)
  | vv' :: l => (snd vv', fst vv') :: inverse_rename l
  end.



Lemma domain_inverse_rename :
 forall r : list (stamp * stamp),
 domain_of_rename_subst (inverse_rename r) = range_of_rename_subst r.
simple induction r; auto.
intros a; elim a; intros v v'.
simpl in |- *; intros.
rewrite H; auto.
Qed.



Lemma prop_rename :
 forall (l : list (stamp * stamp)) (s x v v' : stamp),
 in_list_stamp s (domain_of_rename_subst l) = true ->
 apply_rename_subst l s = x ->
 is_rename_subst ((v, v') :: l) -> s <> v -> x <> v'.
Proof.
intros.
inversion H1.
cut
 (apply_rename_subst ((v, v') :: l) s <> apply_rename_subst ((v, v') :: l) v).
simpl in |- *; rewrite eq_stamp_reflexivity; simpl in |- *.
rewrite eq_stamp_diff; auto.
simpl in |- *.
rewrite H0; auto.

apply H4; auto.
simpl in |- *.
rewrite eq_stamp_diff; auto.
simpl in |- *.
rewrite eq_stamp_reflexivity; simpl in |- *; auto.
Qed.


Lemma is_rename_tail :
 forall (v v' : stamp) (l : list (stamp * stamp)),
 is_a_set_of_stamps (domain_of_rename_subst ((v, v') :: l)) ->
 is_rename_subst ((v, v') :: l) -> is_rename_subst l.
Proof.
simpl in |- *; intros.
inversion H0.
simpl in H1.
unfold is_rename_subst in |- *.
split.
apply are_disjoint_cons_inv with (v := v) (v' := v'); auto.

do 2 intro.
elim (stamp_dec x v); intro y0.
rewrite y0.
elim (stamp_dec y v); intro y1.
rewrite y1.
intros.
absurd (v = v); auto.

intro.
inversion H.
rewrite H3 in H7; discriminate H7.

elim (stamp_dec y v); intro y1.
rewrite y1; intros.
inversion H.
rewrite H4 in H9; discriminate H9.

intros.
generalize (H2 x y); simpl in |- *.
rewrite eq_stamp_diff; auto.
simpl in |- *.
rewrite eq_stamp_diff; auto.

Qed.

Lemma apply_rename_subst_inverse :
 forall (s x : stamp) (r : list (stamp * stamp)),
 is_a_set_of_stamps (domain_of_rename_subst r) ->
 is_rename_subst r ->
 in_list_stamp s (domain_of_rename_subst r) = true ->
 apply_rename_subst r s = x -> apply_rename_subst (inverse_rename r) x = s.
Proof.
simple induction r; auto.
intros a; elim a; intros v v'.
do 4 intro; simpl in |- *.
elim (stamp_dec s v); intros s_eq_v.
rewrite s_eq_v.
rewrite eq_stamp_reflexivity; simpl in |- *.
intros; rewrite <- H3.
rewrite eq_stamp_reflexivity; simpl in |- *; auto.

rewrite eq_stamp_diff; auto.
simpl in |- *.
intros.
generalize (prop_rename l s x v v' H2 H3 H1 s_eq_v).
intros x_is_not_v'.
rewrite eq_stamp_diff; auto.
simpl in |- *.
apply H; auto.
simpl in H0; inversion H0; auto.

apply is_rename_tail with (v := v) (v' := v'); auto.
Qed.




(************************************************************************)
(*           equivalent environments                                    *)
(************************************************************************)

Inductive env_equiv : environment -> environment -> Prop :=
  | env_equiv_refl : forall env : environment, env_equiv env env
  | env_equiv_trans :
      forall env env' env'' : environment,
      env_equiv env env' -> env_equiv env' env'' -> env_equiv env env''
  | env_equiv_redondant :
      forall (env env' : environment) (i : identifier) (t1 t2 : type_scheme),
      env_equiv env env' ->
      env_equiv ((i, t1) :: (i, t2) :: env) ((i, t1) :: env')
  | env_equiv_cons :
      forall (env env' : environment) (i : identifier) (t1 : type_scheme),
      env_equiv env env' -> env_equiv ((i, t1) :: env) ((i, t1) :: env')
  | env_equiv_commute :
      forall (env env' : environment) (i j : identifier)
        (t1 t2 : type_scheme),
      env_equiv env env' ->
      i <> j ->
      env_equiv ((i, t1) :: (j, t2) :: env) ((j, t2) :: (i, t1) :: env')
  | env_equiv_sym :
      forall env env' : environment, env_equiv env env' -> env_equiv env' env.

Hint Resolve env_equiv_refl.
Hint Resolve env_equiv_cons.
Hint Resolve env_equiv_redondant.

(* ************************************************************************* *)
(* 2 equivalent environements give the same result for assoc_ident_in_env    *)
(* ***************************************************************************)
Lemma assoc_ident_in_env_equiv :
 forall (env env' : environment) (v : identifier),
 env_equiv env env' -> assoc_ident_in_env v env = assoc_ident_in_env v env'.
Proof.
simple induction 1; auto.

(* *)simpl in |- *; intros.
rewrite H1; auto.

(* *)simpl in |- *; intros.
elim (identifier_dec v i); intros hyp.
(*v=i*)rewrite hyp; rewrite eq_identifier_reflexivity; simpl in |- *; auto.

(*~v=i*)rewrite eq_identifier_diff; auto.

(* *)simpl in |- *; intros.
rewrite H1; auto.

(* *)simpl in |- *; intros.
elim (identifier_dec v i); intros hyp.
(*v=i*)rewrite hyp; rewrite eq_identifier_reflexivity; simpl in |- *;
        rewrite eq_identifier_diff; simpl in |- *; 
        auto.
auto.
(*~v=i*)rewrite eq_identifier_diff; auto.
simpl in |- *.
elim (identifier_dec v j); intros hyp2.
(*v=j*)rewrite hyp2; rewrite eq_identifier_reflexivity; simpl in |- *; auto.
(*~v=j*)rewrite eq_identifier_diff; auto.

Qed.

(**********************************************************)
Lemma more_general_gen_renaming_aux :
 forall (env1 env2 : environment) (t0 t : type) (phi : substitution)
   (gv_env2 gv_env1 L P : list stamp) (sg : list type)
   (r : list (stamp * stamp)),
 are_disjoints (FV_env env2) gv_env2 ->
 are_disjoints (FV_env env1) gv_env1 ->
 is_rename_subst r ->
 is_a_set_of_stamps (domain_of_rename_subst r) ->
 are_disjoints (FV_env env2) (range_of_rename_subst r) ->
 are_disjoints (range_of_rename_subst r) (FV_env env1) ->
 are_disjoints (domain_of_rename_subst r) (FV_env env2) ->
 is_subset_list_stamp (gen_vars t0 env2) (domain_of_rename_subst r) ->
 apply_subst_gen sg (fst (gen_aux t0 env2 gv_env2)) = Some_subst_gen t ->
 is_prefixe_free2 (FV_env env2) (snd (gen_aux t0 env2 gv_env2)) L ->
 product_list L sg = Some_product phi ->
 is_prefixe_free2 (FV_env env1)
   (snd (gen_aux (extend_subst_type (rename_to_subst r) t0) env1 gv_env1)) P ->
 apply_subst_gen
   (map_extend_subst_type
      (map_extend_subst_type (type_from_stamp_list P)
         (rename_to_subst (inverse_rename r))) phi)
   (fst (gen_aux (extend_subst_type (rename_to_subst r) t0) env1 gv_env1)) =
 Some_subst_gen t.
simple induction t0; auto.
do 9 intro.
intros disjoint1 disjoint2 r_is_ren ren1 ren2 ren3 ren4.
simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env2))); intros y; rewrite y;
 simpl in |- *.
(**(in_list_stamp s (FV_env env2)) = true*)
do 2 intro.
inversion_clear H0.
rewrite apply_substitution_rename_to_subst_rewrite.
do 2 intro.
rewrite is_not_in_domain.
simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env1))); intros z; rewrite z;
 simpl in |- *.
(* (in_list_stamp s (FV_env env1) = true*)
auto.

(* (in_list_stamp s (FV_env env1) = false*)
elim (index_answer_dec (index gv_env1 s)); intro y0.
(*{n | (index gv_env1 s) = Index_in n*)
elim y0; intros n def_n.
rewrite def_n; simpl in |- *.
intro def_P.
inversion_clear def_P.
elim H2; intros x y1.
elim y1; intros; clear y1.
rewrite H3.
rewrite (type_from_stamp_list_app gv_env1 x).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r))
    (type_from_stamp_list gv_env1) (type_from_stamp_list x))
 .
rewrite
 (map_extend_app phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))
    (map_extend_subst_type (type_from_stamp_list x)
       (rename_to_subst (inverse_rename r)))).
rewrite
 (nth_app
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list gv_env1)
          (rename_to_subst (inverse_rename r))) phi)
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list x)
          (rename_to_subst (inverse_rename r))) phi) n)
 .
rewrite
 (nth_map phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r))) n (Var s))
 .
simpl in |- *.
rewrite is_not_in_domain_subst; auto.
rewrite (domain_product L sg phi); auto.
inversion_clear H0.
elim H5; intros x0 y1.
elim y1; intros.
rewrite H0.
apply not_in_list_stamp_app.
unfold are_disjoints in disjoint1.
apply disjoint1; auto.

unfold are_disjoints in H6.
apply H6; auto.

rewrite
 (nth_map (rename_to_subst (inverse_rename r)) (type_from_stamp_list gv_env1)
    n (Var s)); auto.
simpl in |- *.
rewrite is_not_in_domain_subst; auto.
rewrite domain_of_substitution_rename_to_subst.
rewrite domain_inverse_rename.
apply disjoint_inversion2 with (l' := FV_env env2).
apply are_disjoints_symetry; auto.

auto.

apply index_nth; auto.

rewrite length_map.
rewrite length_map2.
apply index_lt with (st := s); auto.

(*( y0 : (index gv_env1 s)=Stamp_not_in *)
rewrite y0; simpl in |- *.
intros def_P; inversion_clear def_P.
elim H2; intros x y1; elim y1; intros; clear y1.
rewrite H3.
rewrite (type_from_stamp_list_app (gv_env1 ++ s :: nil) x).
rewrite (type_from_stamp_list_app gv_env1 (s :: nil)).
simpl in |- *.
rewrite
 (app_ass (type_from_stamp_list gv_env1) (Var s :: nil)
    (type_from_stamp_list x)).
simpl in |- *.
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r))
    (type_from_stamp_list gv_env1) (Var s :: type_from_stamp_list x))
 .
simpl in |- *.
rewrite (apply_substitution_rename_to_subst_rewrite s (inverse_rename r)).
rewrite (is_not_in_domain s (inverse_rename r)).
rewrite
 (map_extend_app phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))
    (Var s
     :: map_extend_subst_type (type_from_stamp_list x)
          (rename_to_subst (inverse_rename r)))).
simpl in |- *.
rewrite <- (length_map2 (rename_to_subst (inverse_rename r)) gv_env1).
rewrite <-
 (length_map phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))).
rewrite
 (nth_last_gen
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list gv_env1)
          (rename_to_subst (inverse_rename r))) phi)
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list x)
          (rename_to_subst (inverse_rename r))) phi)
    (apply_substitution phi s)).
rewrite is_not_in_domain_subst; auto.
rewrite (domain_product L sg phi); auto.
inversion_clear H0.
elim H5; intros x0 y1.
elim y1; intros.
rewrite H0.
apply not_in_list_stamp_app.
unfold are_disjoints in disjoint1.
apply disjoint1; auto.

unfold are_disjoints in H6.
apply H6; auto.

rewrite domain_inverse_rename.
apply disjoint_inversion2 with (l' := FV_env env2); auto.
apply are_disjoints_symetry; auto.

apply disjoint_inversion2 with (l' := FV_env env2); auto.


(**(in_list_stamp s (FV_env env2))=false*)
intro.
elim (index_answer_dec (index gv_env2 s)); intro.
(*(index gv_env2 s)*)
elim a; intros n def_n.
rewrite def_n; simpl in |- *.
elim (nth_answer_inv (nth n sg)).
intro Hyp.
elim Hyp; clear Hyp.
intros t1 def_t1.
rewrite def_t1; intro.
cut
 {y : stamp |
 in_list_stamp y (range_of_rename_subst r) = true /\
 apply_rename_subst r s = y}.
intros Hyp; elim Hyp.
intros s' Hyp1.
elim Hyp1; clear Hyp; clear Hyp1.
do 4 intro.
rewrite apply_substitution_rename_to_subst_rewrite.
rewrite H2; simpl in |- *.
rewrite (disjoint_inversion2 (FV_env env1) (range_of_rename_subst r) s');
 auto.
simpl in |- *.
elim (index_answer_dec (index gv_env1 s')); intro.
elim a0; clear a0; intros x y1. 
rewrite y1; simpl in |- *; intro.
inversion_clear H5.
elim H6; intros x0 y2.
elim y2; clear y2; intros.
rewrite H5.
rewrite (type_from_stamp_list_app gv_env1 x0).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r))
    (type_from_stamp_list gv_env1) (type_from_stamp_list x0))
 .
rewrite
 (map_extend_app phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))
    (map_extend_subst_type (type_from_stamp_list x0)
       (rename_to_subst (inverse_rename r)))).
rewrite
 (nth_app
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list gv_env1)
          (rename_to_subst (inverse_rename r))) phi)
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list x0)
          (rename_to_subst (inverse_rename r))) phi) x)
 .
rewrite
 (nth_map phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r))) x (Var s))
 .
simpl in |- *.
injection H0; intros t_is_t1; rewrite <- t_is_t1.

rewrite (image_by_product2 L sg s n phi t1); auto.
inversion_clear H3.
elim H8; clear H8; intros x1 y2.
elim y2; clear y2; intros.
rewrite H3.
apply index_app; auto.

rewrite
 (nth_map (rename_to_subst (inverse_rename r)) (type_from_stamp_list gv_env1)
    x (Var s')).
simpl in |- *.
rewrite apply_substitution_rename_to_subst_rewrite.
rewrite (apply_rename_subst_inverse s s' r); auto.
inversion_clear H.
auto.


apply index_nth; auto.

do 2 rewrite length_map.
rewrite length_type_from_stamp_list.
apply index_lt with (st := s'); auto.

(*(index gv_env1 s')=Stamp_not_in*)
rewrite b; simpl in |- *; intro.
inversion_clear H5.
elim H6; intros x y2.
elim y2; intros; clear y2.
rewrite H5.
rewrite (type_from_stamp_list_app (gv_env1 ++ s' :: nil) x).
rewrite (type_from_stamp_list_app gv_env1 (s' :: nil)).
simpl in |- *.
rewrite
 (app_ass (type_from_stamp_list gv_env1) (Var s' :: nil)
    (type_from_stamp_list x)).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r))
    (type_from_stamp_list gv_env1)
    ((Var s' :: nil) ++ type_from_stamp_list x)).
rewrite
 (map_extend_app phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))
    (map_extend_subst_type ((Var s' :: nil) ++ type_from_stamp_list x)
       (rename_to_subst (inverse_rename r)))).
rewrite <- (length_map2 (rename_to_subst (inverse_rename r)) gv_env1).
rewrite <-
 (length_map phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r)) 
    (Var s' :: nil) (type_from_stamp_list x)).
simpl in |- *.
rewrite (apply_substitution_rename_to_subst_rewrite s' (inverse_rename r)).
rewrite (apply_rename_subst_inverse s s' r); auto.
simpl in |- *.
rewrite
 (nth_last_gen
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list gv_env1)
          (rename_to_subst (inverse_rename r))) phi)
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list x)
          (rename_to_subst (inverse_rename r))) phi)
    (apply_substitution phi s)).
rewrite (image_by_product2 L sg s n phi t1); auto.
inversion_clear H3.
elim H8; clear H8; intros x0 y2.
elim y2; clear y2; intros.
rewrite H3.
apply index_app; auto.

inversion_clear H.
auto.

apply are_disjoints_symetry; auto.

apply domain_range_rename_subst.
inversion_clear H.
auto.

(*   (nth n sg)=Type_not_in *)
intro y1; rewrite y1; simpl in |- *.
intro pb; discriminate pb.

(*  (index gv_env2 s)=Stamp_not_in*)
rewrite b; simpl in |- *.
elim (nth_answer_inv (nth (length gv_env2) sg)); intro y1.
elim y1; intros t1 def_t1.
rewrite def_t1.
intro.
cut
 {y : stamp |
 in_list_stamp y (range_of_rename_subst r) = true /\
 apply_rename_subst r s = y}.
intros Hyp; elim Hyp.
intros s' Hyp1.
elim Hyp1; clear Hyp; clear Hyp1.
do 4 intro.
rewrite apply_substitution_rename_to_subst_rewrite.
rewrite H2; simpl in |- *.
rewrite (disjoint_inversion2 (FV_env env1) (range_of_rename_subst r) s');
 auto.
simpl in |- *.
elim (index_answer_dec (index gv_env1 s')); intro y2.
elim y2; clear y2; intros x y2.
rewrite y2; simpl in |- *; intro.
inversion_clear H5.
elim H6; intros x0 y3.
elim y3; clear y3; intros.
rewrite H5.
rewrite (type_from_stamp_list_app gv_env1 x0).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r))
    (type_from_stamp_list gv_env1) (type_from_stamp_list x0))
 .
rewrite
 (map_extend_app phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))
    (map_extend_subst_type (type_from_stamp_list x0)
       (rename_to_subst (inverse_rename r)))).
rewrite
 (nth_app
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list gv_env1)
          (rename_to_subst (inverse_rename r))) phi)
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list x0)
          (rename_to_subst (inverse_rename r))) phi) x)
 .
rewrite
 (nth_map phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r))) x (Var s))
 .
simpl in |- *.
injection H0; intros t_is_t1; rewrite <- t_is_t1.
rewrite (image_by_product2 L sg s (length gv_env2) phi t1); auto.
inversion_clear H3.
elim H8; clear H8; intros x1 y3.
elim y3; clear y3; intros.
rewrite H3.
rewrite app_ass; simpl in |- *.
apply index_app_cons_gen; auto.

rewrite
 (nth_map (rename_to_subst (inverse_rename r)) (type_from_stamp_list gv_env1)
    x (Var s')).
simpl in |- *.
rewrite apply_substitution_rename_to_subst_rewrite.
rewrite (apply_rename_subst_inverse s s' r); auto.

inversion_clear H; auto.

apply index_nth; auto.

do 2 rewrite length_map.
rewrite length_type_from_stamp_list.
apply index_lt with (st := s'); auto.

(*  y2 : (index gv_env1 s')=Stamp_not_in *)
rewrite y2; simpl in |- *; intro.
inversion_clear H5.
elim H6; intros x y3.
elim y3; intros; clear y3.
rewrite H5.
rewrite (type_from_stamp_list_app (gv_env1 ++ s' :: nil) x).
rewrite (type_from_stamp_list_app gv_env1 (s' :: nil)).
simpl in |- *.
rewrite
 (app_ass (type_from_stamp_list gv_env1) (Var s' :: nil)
    (type_from_stamp_list x)).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r))
    (type_from_stamp_list gv_env1)
    ((Var s' :: nil) ++ type_from_stamp_list x)).
rewrite
 (map_extend_app phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))
    (map_extend_subst_type ((Var s' :: nil) ++ type_from_stamp_list x)
       (rename_to_subst (inverse_rename r)))).
rewrite <- (length_map2 (rename_to_subst (inverse_rename r)) gv_env1).
rewrite <-
 (length_map phi
    (map_extend_subst_type (type_from_stamp_list gv_env1)
       (rename_to_subst (inverse_rename r)))).
rewrite
 (map_extend_app (rename_to_subst (inverse_rename r)) 
    (Var s' :: nil) (type_from_stamp_list x)).
simpl in |- *.
rewrite (apply_substitution_rename_to_subst_rewrite s' (inverse_rename r)).
rewrite (apply_rename_subst_inverse s s' r); auto.
simpl in |- *.
rewrite
 (nth_last_gen
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list gv_env1)
          (rename_to_subst (inverse_rename r))) phi)
    (map_extend_subst_type
       (map_extend_subst_type (type_from_stamp_list x)
          (rename_to_subst (inverse_rename r))) phi)
    (apply_substitution phi s)).
rewrite (image_by_product2 L sg s (length gv_env2) phi t1); auto.
inversion_clear H3.
elim H8; clear H8; intros x0 y3.
elim y3; clear y3; intros.
rewrite H3.
rewrite app_ass.
simpl in |- *; apply index_app_cons_gen; auto.

inversion_clear H; auto.

apply are_disjoints_symetry; auto.

apply domain_range_rename_subst.
inversion_clear H; auto.

(* y1 : (nth (length stamp gv_env2) sg)=Type_not_in *)
rewrite y1; simpl in |- *.
intro pb; discriminate pb.

(*Arrow*)
do 20 intro.
rewrite fst_gen_aux_arrow_rewrite.
intro.
elim
 (apply_subst_gen_arrow_is_some_inversion3 (fst (gen_aux t env2 gv_env2))
    (fst (gen_aux t1 env2 (snd (gen_aux t env2 gv_env2)))) t2 sg H9).
intros x; elim x; clear x; do 2 intro; clear H9.
do 2 (intros Hyp; elim Hyp; clear Hyp; intro).
intros rwt_t1; rewrite rwt_t1.
rewrite snd_gen_aux_arrow_rewrite; do 2 intro.
rewrite <- apply_subst_arrow_rewrite.
intro.
rewrite fst_gen_aux_arrow_rewrite.
simpl in |- *.
rewrite (H a phi gv_env2 gv_env1 L P sg r); auto.
rewrite
 (H0 b phi (snd (gen_aux t env2 gv_env2))
    (snd (gen_aux (extend_subst_type (rename_to_subst r) t) env1 gv_env1)) L
    P sg r); auto.
simpl in H8.
 apply subset_of_union_inversion2 with (l1 := gen_vars t env2); auto.

generalize H13.
rewrite snd_gen_aux_arrow_rewrite.
auto.

simpl in H8.
 apply subset_of_union_inversion1 with (l2 := gen_vars t1 env2); auto.

apply is_prefixe2_gen_aux with (t := t1); auto.

generalize H13.
rewrite snd_gen_aux_arrow_rewrite.
intro.
apply
 is_prefixe2_gen_aux with (t := extend_subst_type (rename_to_subst r) t1);
 auto.

Qed.


Lemma more_general_gen_renaming :
 forall (r : list (stamp * stamp)) (t0 : type) (env env' : environment),
 renaming_of_not_concerned_with r (gen_vars t0 env) 
   (FV_env env) (FV_env env') ->
 more_general (gen_type (extend_subst_type (rename_to_subst r) t0) env')
   (gen_type t0 env).
Proof.
intros; apply more_general_intro; intros.
inversion_clear H0; elim H1; clear H1; intros sg.
unfold gen_type in |- *; intros.
elim (product_list_exists t0 env sg); eauto.
intros phi def_phi.
apply gen_instance_intro.
exists
 (map_extend_subst_type
    (map_extend_subst_type
       (type_from_stamp_list
          (snd (gen_aux (extend_subst_type (rename_to_subst r) t0) env' nil)))
       (rename_to_subst (inverse_rename r))) phi).
inversion H.
rewrite
 (more_general_gen_renaming_aux env' env t0 t phi nil nil
    (snd (gen_aux t0 env nil))
    (snd (gen_aux (extend_subst_type (rename_to_subst r) t0) env' nil)) sg r)
 ; try rewrite H1; auto.

apply gen_vars_is_a_set.

apply free_and_bound_are_disjoints.
Qed.


(* ************************************************************************* *)
(* typing is stable under equivalent environments                            *)
(* ************************************************************************* *)

Lemma type_of_env_equiv :
 forall (e : expr) (env env' : environment) (t : type),
 env_equiv env env' -> type_of env e t -> type_of env' e t.
simple induction e; intros.

(* Constant *)

inversion_clear H0.
apply type_of_int_const.

(* Variable *)

inversion_clear H0.
apply type_of_var with (ts := ts); auto.
rewrite <- H1; rewrite <- (assoc_ident_in_env_equiv env env' i H); auto.

(* lambda *)
inversion_clear H1.
apply type_of_lambda.
apply H with (env := add_environment env i (type_to_type_scheme t0)); auto.
unfold add_environment in |- *.
auto.

(* Rec *)

inversion H1.
apply type_of_rec_fun.
apply
 H
  with
    (env := add_environment (add_environment env i0 (type_to_type_scheme t0))
              i (type_to_type_scheme (Arrow t0 t'))); 
 auto.
unfold add_environment in |- *.
auto.

(* Application *)
inversion H2.
apply type_of_app with (t := t0).
apply H with (env := env); auto.
apply H0 with (env := env); auto.

(* Let in *)

inversion H2.
elim
 (exists_renaming_not_concerned_with2 (gen_vars t0 env) 
    (FV_env env) (FV_env env') (gen_vars_is_a_set t0 env)).
intros r ren.
generalize
 (typage_is_stable_by_substitution e0 t0 env (rename_to_subst r) H8).
simpl in |- *.
rewrite s_env_when_s_disjoint_with_env3.
intro.
apply type_of_let_in with (t := extend_subst_type (rename_to_subst r) t0).
apply H with (env := env); auto.

unfold add_environment in |- *.
unfold add_environment in H9.
apply
 typing_in_a_more_general_env with (env2 := (i, gen_type t0 env) :: env').
apply more_general_env_cons; auto.
apply more_general_gen_renaming; auto.

apply H0 with (env := (i, gen_type t0 env) :: env); auto.

inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H11.
apply free_and_bound_are_disjoints.
Qed.


Lemma typing_redundant_env :
 forall (e : expr) (v : identifier) (ts1 ts2 : type_scheme) 
   (t : type) (env : environment),
 type_of ((v, ts1) :: (v, ts2) :: env) e t -> type_of ((v, ts1) :: env) e t.
Proof.
intros.
apply type_of_env_equiv with (env := (v, ts1) :: (v, ts2) :: env); auto.
Qed.

Lemma typing_commute_env :
 forall (e : expr) (v v' : identifier) (ts1 ts2 : type_scheme) 
   (t : type) (env : environment),
 v <> v' ->
 type_of ((v, ts1) :: (v', ts2) :: env) e t ->
 type_of ((v', ts2) :: (v, ts1) :: env) e t.
Proof.
intros.
apply type_of_env_equiv with (env := (v, ts1) :: (v', ts2) :: env); auto.
apply env_equiv_commute; auto.
Qed.

Inductive est_valeur : expr -> Prop :=
  | Constant_valeur : forall n : nat, est_valeur (Const_nat n)
  | Lambda_valeur :
      forall (i : identifier) (e : expr), est_valeur (Lambda i e)
  | Rec_valeur : forall (f i : identifier) (e : expr), est_valeur (Rec f i e).


Inductive est_libre : identifier -> expr -> Prop :=
 (*  Const_libre : (n : nat) (i : identifier) (est_libre i (Const_nat n))
 |*)
  | Var_libre : forall i : identifier, est_libre i (Variabl i)
  | Lamb_libre :
      forall (i j : identifier) (e : expr),
      eq_identifier i j = false -> est_libre i e -> est_libre i (Lambda j e)
  | Rec_libre :
      forall (i j f : identifier) (e : expr),
      eq_identifier i j = false ->
      eq_identifier i f = false -> est_libre i e -> est_libre i (Rec f j e)
  | Apply_libre1 :
      forall (i j : identifier) (e1 e2 : expr),
      est_libre i e1 -> est_libre i (Apply e1 e2)
  | Apply_libre2 :
      forall (i j : identifier) (e1 e2 : expr),
      est_libre i e2 -> est_libre i (Apply e1 e2)
  | Let_in_libre1 :
      forall (i j : identifier) (e1 e2 : expr),
      est_libre i e1 -> est_libre i (Let_in j e1 e2)
  | Let_in_libre2 :
      forall (i j : identifier) (e1 e2 : expr),
      eq_identifier i j = false ->
      est_libre i e2 -> est_libre i (Let_in j e1 e2).


Lemma non_libre_lambda_diff :
 forall (i v : identifier) (e : expr),
 ~ est_libre v (Lambda i e) -> v <> i -> ~ est_libre v e.

Proof.
intros i v e hyp.
unfold not in hyp.
intro diff_v_i.
unfold not in |- *; intro.
apply hyp.
apply Lamb_libre; auto.
apply eq_identifier_diff; auto.
Qed.

Lemma non_libre_apply :
 forall (v : identifier) (e0 e1 : expr),
 ~ est_libre v (Apply e0 e1) -> ~ est_libre v e0 /\ ~ est_libre v e1.

Proof.
intros; split.
unfold not in H; unfold not in |- *.
intro.
apply H.
apply (Apply_libre1 v v e0 e1); auto.

unfold not in |- *; unfold not in H; intro.
apply H.
apply (Apply_libre2 v v e0 e1).
auto.
Qed.

Lemma not_is_free :
 forall (i : identifier) (e : expr), ~ est_libre i (Lambda i e).
unfold not in |- *; intros.
inversion_clear H.
rewrite (eq_identifier_reflexivity i) in H0; discriminate H0.
Qed.
Hint Resolve not_is_free.

Lemma not_is_free_in_rec :
 forall (i f : identifier) (e : expr), ~ est_libre i (Rec f i e).
unfold not in |- *; intros.
inversion_clear H.
rewrite (eq_identifier_reflexivity i) in H0; discriminate H0.
Qed.

Lemma not_is_free_in_rec2 :
 forall (i f : identifier) (e : expr), ~ est_libre f (Rec f i e).
unfold not in |- *; intros.
inversion_clear H.
rewrite (eq_identifier_reflexivity f) in H1; discriminate H1.
Qed.

Lemma non_libre_rec_diff :
 forall (i v f : identifier) (e : expr),
 ~ est_libre v (Rec f i e) -> v <> i -> v <> f -> ~ est_libre v e.
Proof.
unfold not in |- *; intros.
apply H.
apply (Rec_libre v i f e); auto.
apply (eq_identifier_diff v i); auto.
apply (eq_identifier_diff v f); auto.
Qed.

Lemma n_l_let_in_1 :
 forall (v : identifier) (e0 e1 : expr),
 ~ est_libre v (Let_in v e0 e1) -> ~ est_libre v e0.

Proof.
intros; unfold not in |- *; intro.
unfold not in H.
apply H.
apply (Let_in_libre1 v v e0 e1).
auto.
Qed.

Lemma n_l_let_in_2 :
 forall (v j : identifier) (e0 e1 : expr),
 ~ est_libre v (Let_in j e0 e1) ->
 v <> j -> ~ est_libre v e0 /\ ~ est_libre v e1.

Proof.
intros.
split.
unfold not in H; unfold not in |- *.
intro.
apply H.
apply (Let_in_libre1 v j e0 e1).
auto.

unfold not in H; unfold not in |- *.
intro.
apply H.
apply (Let_in_libre2 v j e0 e1).
apply (eq_identifier_diff v j).
auto.

auto.
Qed.

Lemma n_l_let_in :
 forall (v i : identifier) (e0 e1 : expr),
 ~ est_libre v (Let_in i e0 e1) -> ~ est_libre v e0.
Proof.
do 4 intro.
elim (identifier_dec v i); intros hyp.
(*v=i*)
rewrite hyp; intro.
apply n_l_let_in_1 with (e1 := e1); auto.

(*v<>i*)
intro.
elim (n_l_let_in_2 v i e0 e1 H hyp); auto.
Qed.

(* ************************************************************* *)
(*            Definition du predicat substitution 			 *)
(*            Permet de substituer un identificateur             *)
(*            par un terme dans un autre terme.		    		 *)
(* ************************************************************* *)

Inductive substitute : identifier -> expr -> expr -> expr -> Prop :=
  | Const_subst :
      forall (i : identifier) (e : expr) (n : nat),
      substitute i e (Const_nat n) (Const_nat n)
  | Var_subst_diff :
      forall (i j : identifier) (e : expr),
      eq_identifier i j = false -> substitute i e (Variabl j) (Variabl j)
  | Var_subst_eq :
      forall (i : identifier) (e : expr), substitute i e (Variabl i) e
  | Lambda_subst_diff :
      forall (i j : identifier) (e1 e2 er : expr),
      eq_identifier i j = false ->
      ~ est_libre j e1 ->
      substitute i e1 e2 er -> substitute i e1 (Lambda j e2) (Lambda j er)
  | Lambda_subst_eq :
      forall (i : identifier) (e1 e2 : expr),
      substitute i e1 (Lambda i e2) (Lambda i e2)
  | Rec_subst_diff :
      forall (i j f : identifier) (e1 e2 er : expr),
      eq_identifier i j = false ->
      eq_identifier i f = false ->
      ~ est_libre j e1 ->
      ~ est_libre f e1 ->
      substitute i e1 e2 er -> substitute i e1 (Rec f j e2) (Rec f j er)
  | Rec_subst_eq_1 :
      forall (i f : identifier) (e1 e2 : expr),
      substitute i e1 (Rec f i e2) (Rec f i e2)
  | Rec_subst_eq_2 :
      forall (i j : identifier) (e1 e2 : expr),
      substitute i e1 (Rec i j e2) (Rec i j e2)
  | Apply_subst :
      forall (i : identifier) (er1 er2 e1 e2 e : expr),
      substitute i e e1 er1 ->
      substitute i e e2 er2 -> substitute i e (Apply e1 e2) (Apply er1 er2)
  | Let_in_subst_diff :
      forall (j i : identifier) (er1 er2 e1 e2 e : expr),
      ~ est_libre j e ->
      eq_identifier i j = false ->
      substitute i e e1 er1 ->
      substitute i e e2 er2 ->
      substitute i e (Let_in j e1 e2) (Let_in j er1 er2)
  | Let_in_subst_eq :
      forall (i : identifier) (er1 e1 e2 e : expr),
      substitute i e e1 er1 ->
      substitute i e (Let_in i e1 e2) (Let_in i er1 e2).

Lemma inv_subst_var :
 forall (i i0 : identifier) (e0 Er : expr),
 i <> i0 -> substitute i0 e0 (Variabl i) Er -> Er = Variabl i.
intros.
inversion H0; auto.

absurd (i = i0); auto.
Qed.

(**********************************************************************)
(*                         contextes                                  *)
(**********************************************************************)

Definition context := expr -> expr.

Definition apply_context (c : context) (a : expr) : expr := c a.

Inductive est_MLcontext : context -> Prop :=
  | trou : est_MLcontext (fun x : expr => x)
  | app_left :
      forall (e : expr) (c : context),
      est_MLcontext c ->
      est_MLcontext (fun x : expr => Apply (apply_context c x) e)
  | app_right :
      forall v : expr,
      est_valeur v ->
      forall c : context,
      est_MLcontext c ->
      est_MLcontext (fun x : expr => Apply v (apply_context c x))
  | let_left :
      forall (e : expr) (i : identifier) (c : context),
      est_MLcontext c ->
      est_MLcontext (fun x : expr => Let_in i (apply_context c x) e).


   
(**********************************************************************)
(*                         beta-reduction                             *)
(**********************************************************************)

Inductive reduction : expr -> expr -> Prop :=
  | Lamb_apply_red_vrai :
      forall (i : identifier) (e1 e er : expr),
      est_valeur e ->
      substitute i e e1 er -> reduction (Apply (Lambda i e1) e) er
  | Let_in_red_vrai :
      forall (i : identifier) (e1 e2 er : expr),
      est_valeur e1 -> substitute i e1 e2 er -> reduction (Let_in i e1 e2) er
  | Rec_apply_red_vrai :
      forall (i f : identifier) (e1 e er er' : expr),
      est_valeur e ->
      substitute f (Rec f i e1) e1 er ->
      substitute i e er er' -> reduction (Apply (Rec f i e1) e) er'
  | Context_red :
      forall (e1 e2 : expr) (c : context),
      reduction e1 e2 ->
      est_MLcontext c -> reduction (apply_context c e1) (apply_context c e2).




Lemma env_extension_Rec :
 forall (i i0 : identifier) (e : expr),
 (forall (v : identifier) (ts : type_scheme) (t : type) (env : environment),
  ~ est_libre v e -> type_of ((v, ts) :: env) e t -> type_of env e t) ->
 forall (v : identifier) (ts : type_scheme) (t : type) (env : environment),
 ~ est_libre v (Rec i i0 e) ->
 type_of ((v, ts) :: env) (Rec i i0 e) t -> type_of env (Rec i i0 e) t.
Proof.
do 8 intro.
elim (identifier_dec v i); intros v_is_i.
(*v=i *)
rewrite v_is_i.
elim (identifier_dec i i0); intros i_is_i0.
(** i=i0**)
rewrite i_is_i0; intros not_est_libre type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *; unfold add_environment in H0.
apply
 type_of_env_equiv
  with
    (env := (i0, type_to_type_scheme (Arrow t0 t'))
            :: (i0, type_to_type_scheme t0) :: (i0, ts) :: env); 
 auto.
(** ~i=i0**)
intros not_est_libre type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *; unfold add_environment in H0.
apply
 type_of_env_equiv
  with
    (env := (i, type_to_type_scheme (Arrow t0 t'))
            :: (i0, type_to_type_scheme t0) :: (i, ts) :: env); 
 auto.
apply
 env_equiv_trans
  with
    (env' := (i, type_to_type_scheme (Arrow t0 t'))
             :: (i, ts) :: (i0, type_to_type_scheme t0) :: env); 
 auto.
apply env_equiv_cons.
apply env_equiv_commute; auto.

(*~v=i *)
elim (identifier_dec v i0); intros v_is_i0.
(**v=i0 *)
rewrite v_is_i0; intro; intros type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *; unfold add_environment in H1.
apply
 type_of_env_equiv
  with
    (env := (i, type_to_type_scheme (Arrow t0 t'))
            :: (i0, type_to_type_scheme t0) :: (i0, ts) :: env); 
 auto.
(**~v=i0 *)
intro.
intros type_of_cons; inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *; unfold add_environment in H1.
apply H with (v := v) (ts := ts); auto.
apply non_libre_rec_diff with (i := i0) (f := i); auto.

apply
 type_of_env_equiv
  with
    (env := (i, type_to_type_scheme (Arrow t0 t'))
            :: (i0, type_to_type_scheme t0) :: (v, ts) :: env); 
 auto.
apply
 env_equiv_trans
  with
    (env' := (i, type_to_type_scheme (Arrow t0 t'))
             :: (v, ts) :: (i0, type_to_type_scheme t0) :: env); 
 auto.
apply env_equiv_cons.
apply env_equiv_commute; auto.

apply env_equiv_commute; auto.

Qed.

Lemma env_extension :
 forall (e : expr) (v : identifier) (ts : type_scheme) 
   (t : type) (env : environment),
 ~ est_libre v e -> type_of ((v, ts) :: env) e t -> type_of env e t.
Proof.
simple induction e.

(*constante*)
intros.
inversion_clear H0.
apply type_of_int_const.

(*variable*)
do 5 intro.
elim (identifier_dec v i); intros v_i_eq.
(*v=i*)
rewrite v_i_eq; intro.
absurd (est_libre i (Variabl i)); auto.
apply Var_libre.

(*~v=i*)
intros.
inversion_clear H0.
apply type_of_var with (ts := ts0); auto.
simpl in H1.
generalize H1.
rewrite eq_identifier_diff; auto.
simpl in |- *; auto.

(*Lambda*)
do 7 intro.
elim (identifier_dec v i); intro v_is_i.
rewrite v_is_i; intros not_est_libre type_of_cons.
inversion_clear type_of_cons.
apply type_of_lambda.

unfold add_environment in |- *.
unfold add_environment in H0.
apply typing_redundant_env with (ts2 := ts); auto.

intro.
intros type_of_cons.
inversion_clear type_of_cons.
apply type_of_lambda.
unfold add_environment in |- *.
unfold add_environment in H1.
apply H with (v := v) (ts := ts); auto.
exact (non_libre_lambda_diff i v e0 H0 v_is_i).

apply typing_commute_env; auto.

(*Rec*)
exact env_extension_Rec.

(*application*)
intros.
inversion_clear H2.
generalize (non_libre_apply v e0 e1 H1); intro hyp_non_libre;
 elim hyp_non_libre; intros hyp1 hyp2.
apply type_of_app with (t := t0).
apply H with (v := v) (ts := ts); auto.
apply H0 with (v := v) (ts := ts); auto.

(*Let*)
do 9 intro.
elim (identifier_dec v i); intros eq_hyp.
rewrite eq_hyp; intros.
inversion_clear H2.
unfold add_environment in H4.
apply type_of_let_in with (t := t0).
apply H with (v := i) (ts := ts); auto.
apply (n_l_let_in_1 i e0 e1); auto.


unfold add_environment in |- *.
apply typing_redundant_env with (ts2 := ts).
apply
 typing_in_a_more_general_env
  with (env2 := (i, gen_type t0 ((i, ts) :: env)) :: (i, ts) :: env); 
 auto.
apply more_general_env_cons; auto.
apply more_gen_subset_gen.
simpl in |- *; apply l2_subset_of_union_l1_l2.

(* ~ v=i *)
intros.
inversion_clear H2.
apply type_of_let_in with (t := t0).
apply H with (v := v) (ts := ts); auto.
generalize (n_l_let_in_2 v i e0 e1 H1 eq_hyp).
intro Hyp; elim Hyp; auto.

apply H0 with (v := v) (ts := ts).
generalize (n_l_let_in_2 v i e0 e1 H1 eq_hyp).
intro Hyp; elim Hyp; auto.

unfold add_environment in |- *.
unfold add_environment in H4.
apply typing_commute_env; auto.
apply
 typing_in_a_more_general_env
  with (env2 := (i, gen_type t0 ((v, ts) :: env)) :: (v, ts) :: env); 
 auto.
apply more_general_env_cons; auto.
apply more_gen_subset_gen.
simpl in |- *; apply l2_subset_of_union_l1_l2.
Qed.

Lemma env_extension_bis_rec :
 forall (i i0 : identifier) (e : expr),
 (forall (v : identifier) (ts : type_scheme) (t2 : type) (env : environment),
  ~ est_libre v e -> type_of env e t2 -> type_of ((v, ts) :: env) e t2) ->
 forall (v : identifier) (ts : type_scheme) (t2 : type) (env : environment),
 ~ est_libre v (Rec i i0 e) ->
 type_of env (Rec i i0 e) t2 -> type_of ((v, ts) :: env) (Rec i i0 e) t2.
Proof.
do 8 intro.
elim (identifier_dec v i); intros v_is_i.
(* v=i *)
rewrite v_is_i; elim (identifier_dec i i0); intros i_is_i0.
(* i=i0 *)
rewrite i_is_i0; intro; intros type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *.
unfold add_environment in H1.
apply
 type_of_env_equiv
  with
    (env := (i0, type_to_type_scheme (Arrow t t'))
            :: (i0, type_to_type_scheme t) :: env); 
 auto.
apply env_equiv_sym; auto.
(* ~i=i0 *)
intro; intros type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *.
unfold add_environment in H1.
apply
 type_of_env_equiv
  with
    (env := (i, type_to_type_scheme (Arrow t t'))
            :: (i0, type_to_type_scheme t) :: env); 
 auto.
apply
 env_equiv_trans
  with
    (env' := (i, type_to_type_scheme (Arrow t t'))
             :: (i, ts) :: (i0, type_to_type_scheme t) :: env); 
 auto.
apply env_equiv_sym.
apply env_equiv_redondant; auto.

apply env_equiv_cons.
apply env_equiv_commute; auto.

(* ~ v=i *)
elim (identifier_dec v i0); intros v_is_i0.
(* v=i0 *)
rewrite v_is_i0; intro; intros type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *.
unfold add_environment in H1.
apply
 type_of_env_equiv
  with
    (env := (i, type_to_type_scheme (Arrow t t'))
            :: (i0, type_to_type_scheme t) :: env); 
 auto.
apply env_equiv_cons.
apply env_equiv_sym.
apply env_equiv_redondant; auto.
(*~v=i0*)
intro; intro type_of_cons.
inversion_clear type_of_cons.
apply type_of_rec_fun.
unfold add_environment in |- *; unfold add_environment in H1.
apply
 type_of_env_equiv
  with
    (env := (v, ts)
            :: (i, type_to_type_scheme (Arrow t t'))
               :: (i0, type_to_type_scheme t) :: env).
apply
 env_equiv_trans
  with
    (env' := (i, type_to_type_scheme (Arrow t t'))
             :: (v, ts) :: (i0, type_to_type_scheme t) :: env); 
 auto.
apply env_equiv_commute; auto.

apply env_equiv_cons; auto.
apply env_equiv_commute; auto.

apply H with (v := v) (ts := ts); auto.
apply non_libre_rec_diff with (f := i) (i := i0); auto.

Qed.




Lemma env_extension_bis :
 forall (e : expr) (v : identifier) (ts : type_scheme) 
   (t2 : type) (env : environment),
 ~ est_libre v e -> type_of env e t2 -> type_of ((v, ts) :: env) e t2.

Proof.

simple induction e.

(*constante*)
intros; inversion_clear H0.
apply type_of_int_const.

(*variable*)
do 5 intro.
elim (identifier_dec v i); intros v_i_eq.
(*v=i*)
rewrite v_i_eq; intro.
absurd (est_libre i (Variabl i)); auto.
apply Var_libre.

(*~v=i*)
intros.
inversion_clear H0.
apply type_of_var with (ts := ts0); auto.
simpl in |- *; rewrite eq_identifier_diff; auto.

(*Lambda*)
do 7 intro.
elim (identifier_dec v i); intro v_is_i.
(*v=i*)
rewrite v_is_i; intros not_est_libre type_of_cons.
inversion_clear type_of_cons.
apply type_of_lambda.

unfold add_environment in |- *.
unfold add_environment in H0.
apply type_of_env_equiv with (env := (i, type_to_type_scheme t) :: env); auto.
apply env_equiv_sym; auto.

(*v<>i*)
intros.
inversion H1.
apply type_of_lambda.
unfold add_environment in |- *.
unfold add_environment in H6.
apply typing_commute_env; auto.

apply H; auto.
apply non_libre_lambda_diff with (i := i); auto.

(*Rec*)
exact env_extension_bis_rec.
(*Do 8 Intro.
(Elim (identifier_dec v i); Intros v_is_i).
(* v=i *)
(Rewrite -> v_is_i; Elim (identifier_dec i i0); Intros i_is_i0).
(* i=i0 *)
Rewrite -> i_is_i0; Intros.
Inversion_clear H1.
Unfold add_environment in H2.
Apply type_of_rec_fun.
Unfold add_environment.
(Apply type_of_env_equiv with env:=(cons 
                                     (i0,
                                      (type_to_type_scheme (Arrow t t')))
                                     (cons 
                                       (i0,(type_to_type_scheme t)) env));
 Auto).
(Apply env_equiv_sym; Auto).

(* i<>i0 *)
Inversion_clear H1.
Unfold add_environment in H2.
Apply type_of_rec_fun.
Unfold add_environment.
Apply type_of_env_equiv with env:=(cons 
           (i,(type_to_type_scheme (Arrow t t')))
           (cons (i0,(type_to_type_scheme t))
             env));Auto.
(Apply env_equiv_sym; Auto).
*)

(*application*)
do 10 intro.
inversion_clear H2.
elim (non_libre_apply v e0 e1 H1); intros.
apply type_of_app with (t := t).
apply H; auto.
apply H0; auto.

(*Let*)
do 11 intro.
inversion_clear H2.
unfold add_environment in H4.
elim
 (exists_renaming_not_concerned_with2 (gen_vars t env) 
    (FV_env env) (FV_type_scheme ts) (gen_vars_is_a_set t env)).
intros r ren.
inversion ren.
generalize (typage_is_stable_by_substitution e0 t env (rename_to_subst r) H3).
rewrite s_env_when_s_disjoint_with_env3.
intro.
apply type_of_let_in with (t := extend_subst_type (rename_to_subst r) t).
apply H; auto.
apply n_l_let_in with (e1 := e1) (i := i); auto.

unfold add_environment in |- *.
change
  (type_of
     ((i,
      gen_type (extend_subst_type (rename_to_subst r) t)
        (add_environment env v ts)) :: (v, ts) :: env) e1 t2) 
 in |- *.
rewrite <-
 (gen_type_add_env env (extend_subst_type (rename_to_subst r) t) ts v)
 .
rewrite <- gen_alpha4_bis; auto.
elim (identifier_dec i v); intros v_is_i.
rewrite <- v_is_i; intros.
(*v=i*)
apply type_of_env_equiv with (env := (i, gen_type t env) :: env); auto.
apply env_equiv_sym; auto.

(*v<>i*)
apply typing_commute_env; auto.
apply H0; auto.
elim (n_l_let_in_2 v i e0 e1); auto.

apply are_disjoints_symetry.
apply disjoint_subset_bis with (l2 := range_of_rename_subst r); auto.

apply is_subset_gen_vars2; auto.
rewrite H5.
apply free_and_bound_are_disjoints.

rewrite H5; auto.

rewrite domain_of_substitution_rename_to_subst.
rewrite H5.
apply free_and_bound_are_disjoints.

Qed.



Lemma inverse_rename_rename_is_identity :
 forall (r : list (stamp * stamp)) (t : type),
 are_disjoints (range_of_rename_subst r) (FV_type t) ->
 is_a_set_of_stamps (domain_of_rename_subst r) ->
 is_rename_subst r ->
 extend_subst_type (rename_to_subst (inverse_rename r))
   (extend_subst_type (rename_to_subst r) t) = t.

simple induction t; auto.

(*Var*)
simpl in |- *; intros.
rewrite apply_substitution_rename_to_subst_rewrite.
elim (bool_dec (in_list_stamp s (domain_of_rename_subst r))); intro y.
(*(in_list_stamp s (domain_of_rename_subst r))=true*)
elim (domain_range_rename_subst r s y).
intros x y0; elim y0; clear y0; intros.
rewrite H3; simpl in |- *.
rewrite apply_substitution_rename_to_subst_rewrite.
rewrite (apply_rename_subst_inverse s x r); auto.

(*(in_list_stamp s (domain_of_rename_subst r))=false*)
rewrite is_not_in_domain; auto.
simpl in |- *; rewrite apply_substitution_rename_to_subst_rewrite.
rewrite is_not_in_domain; auto.
rewrite domain_inverse_rename.
apply disjoint_inversion2 with (l' := s :: nil); auto.

(*Arrow*)
simpl in |- *; intros.
rewrite H; auto.
rewrite H0; auto.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type t0); auto.

apply disjoint_list_and_union_inversion1 with (l2 := FV_type t1); auto.
Qed.


Lemma disjoints_ren :
 forall (r : list (stamp * stamp)) (env : environment) (t0 t1 : type),
 renaming_of_not_concerned_with r (gen_vars t0 env) (FV_env env) (FV_type t1) ->
 are_disjoints (gen_vars t0 env)
   (FV_type (extend_subst_type (rename_to_subst r) t1)).

simple induction t1; auto.
simpl in |- *.
intros.
elim (bool_dec (in_list_stamp s (domain_of_rename_subst r))); intros Hyp.
elim (domain_range_rename_subst r s Hyp).
intros x Def_x.
elim Def_x; clear Def_x.
intros.
rewrite apply_substitution_rename_to_subst_rewrite.
rewrite H1.
simpl in |- *.
inversion H.
inversion H2.
rewrite <- H3.
apply are_disjoints_symetry.
apply disjoint_cons_nil.
generalize
 (are_disjoints_symetry (domain_of_rename_subst r) 
    (range_of_rename_subst r) H10).
intro.
unfold are_disjoints in H12.
auto.

simpl in |- *; rewrite apply_substitution_rename_to_subst_rewrite.
rewrite is_not_in_domain; auto.
simpl in |- *.
inversion H.
inversion H0.
rewrite <- H1.
apply are_disjoints_symetry.
apply disjoint_cons_nil.
auto.

simpl in |- *; intros.
apply are_disjoints_symetry.
inversion H1.
apply disjoint_list_and_union; apply are_disjoints_symetry; auto.
apply H.
apply renaming_of_not_concerned_with_intro; auto.
apply disjoint_list_and_union_inversion1 with (l2 := FV_type t2); auto.

apply H0.
apply renaming_of_not_concerned_with_intro; auto.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type t); auto.

Qed.

(**************************************************************)
(*              substitution lemma                            *)
(**************************************************************)


Lemma in_list_eq_stamp :
 forall (l : list stamp) (s s0 : stamp),
 in_list_stamp s l = true ->
 in_list_stamp s0 l = false -> eq_stamp s s0 = false.
do 4 intro.
elim (stamp_dec s0 s); intro y.
rewrite y; rewrite H; intro.
discriminate H0.
rewrite eq_stamp_diff; auto.
Qed.


Lemma disjoint_eq_stamp :
 forall (l l' : list stamp) (x s : stamp),
 are_disjoints l l' ->
 in_list_stamp s l = true ->
 in_list_stamp x l' = true -> eq_stamp s x = false.
do 5 intro.
elim (stamp_dec s x); intro y.
rewrite y; intros.
unfold are_disjoints in H.
rewrite (H x H0) in H1.
rewrite eq_stamp_reflexivity; auto.

rewrite eq_stamp_diff; auto.
Qed.




Lemma not_in_list_rename :
 forall (t1 : type) (env : environment) (r : list (stamp * stamp))
   (s : stamp),
 is_rename_subst r ->
 are_disjoints (domain_of_rename_subst r) (FV_env env) ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 in_list_stamp s (FV_env env) = false ->
 in_list_stamp s (domain_of_rename_subst r) = true ->
 in_list_stamp s
   (FV_type_scheme
      (extend_subst_type_scheme (rename_to_subst r) (type_to_type_scheme t1))) =
 false.
Proof.
intros; elim t1.
(*Nat*)auto.

(*t1=Var s0*)
intro; elim (bool_dec (in_list_stamp s0 (domain_of_rename_subst r))); intro y.
(* (in_list_stamp s0 (domain_of_rename_subst r))=true *)
elim (domain_range_rename_subst r s0 y); intros x y0.
elim y0; intros.
simpl in |- *; rewrite apply_substitution_rename_to_subst_rewrite.
rewrite H5; simpl in |- *.
rewrite
 (disjoint_eq_stamp (domain_of_rename_subst r) (range_of_rename_subst r) x s)
 ; auto.
inversion H; auto.

(*(in_list_stamp s0 (domain_of_rename_subst r))=false*)
simpl in |- *; rewrite apply_substitution_rename_to_subst_rewrite.
rewrite is_not_in_domain; auto.
simpl in |- *.
rewrite (in_list_eq_stamp (domain_of_rename_subst r) s s0); auto.

(*t1=arrow*)
intros; simpl in |- *.
apply not_in_list_union_inversion; auto.
Qed.



Lemma gen_vars_add_environment_rename :
 forall (t0 t1 t' : type) (env : environment) (r : list (stamp * stamp))
   (i0 : identifier),
 is_rename_subst r ->
 are_disjoints (domain_of_rename_subst r) (FV_env env) ->
 are_disjoints (FV_env env) (range_of_rename_subst r) ->
 are_disjoints (union_list_stamp (FV_type t1) (FV_type t'))
   (range_of_rename_subst r) ->
 is_subset_list_stamp (gen_vars t0 env) (domain_of_rename_subst r) ->
 gen_vars t0
   (add_environment env i0
      (extend_subst_type_scheme (rename_to_subst r) (type_to_type_scheme t1))) =
 gen_vars t0 env.
Proof.
simple induction t0.
(*Nat*)auto.

(*Var s*)
do 10 intro; simpl in |- *.
elim (bool_dec (in_list_stamp s (FV_env env))); intro y; rewrite y;
 simpl in |- *; intro.
rewrite in_second_componant_union_list_stamp; auto.

rewrite not_in_list_union_inversion; auto.
apply not_in_list_rename with (env := env); auto.
apply subset_cons_subset with (l' := nil (A:=stamp)); auto.

(*Arrow*)intros; simpl in |- *.
simpl in H5.
rewrite (H t2 t' env r i0); auto.
rewrite (H0 t2 t' env r i0); auto.
apply subset_of_union_inversion2 with (l1 := gen_vars t env); auto.

apply subset_of_union_inversion1 with (l2 := gen_vars t1 env); auto.
Qed.

Lemma conserv_par_sbst_rec_case :
 forall (i i0 : identifier) (e : expr),
 (forall (Er e0 : expr) (i1 : identifier) (env : environment) (t t0 : type),
  substitute i1 e0 e Er ->
  type_of ((i1, gen_type t0 env) :: env) e t ->
  type_of env e0 t0 -> type_of env Er t) ->
 forall (Er e0 : expr) (i1 : identifier) (env : environment) (t t0 : type),
 substitute i1 e0 (Rec i i0 e) Er ->
 type_of ((i1, gen_type t0 env) :: env) (Rec i i0 e) t ->
 type_of env e0 t0 -> type_of env Er t.
Proof.
do 7 intro.
elim (identifier_dec i i0); intros i_is_i0.
(*i=i0*)
rewrite i_is_i0; do 3 intro.
elim (identifier_dec i1 i0); intros i1_is_i0.
(**i1=i0*)rewrite i1_is_i0; intros.
inversion H0.
rewrite (eq_identifier_reflexivity i0) in H6; discriminate H6.

apply (env_extension (Rec i0 i0 e) i0 (gen_type t0 env) t env); auto.
apply not_is_free_in_rec.

apply (env_extension (Rec i0 i0 e) i0 (gen_type t0 env) t env); auto.
apply not_is_free_in_rec.

(**i1<>i0**)
intros; inversion H0.
inversion_clear H1.
apply type_of_rec_fun.
unfold add_environment in H14.
apply
 type_of_env_equiv
  with (env := add_environment env i0 (type_to_type_scheme (Arrow t1 t'))).
unfold add_environment in |- *.
apply env_equiv_sym; auto.

elim
 (exists_renaming_not_concerned_with2 (gen_vars t0 env) 
    (FV_env env) (FV_type (Arrow t1 t')) (gen_vars_is_a_set t0 env)).
intros r ren.
cut
 (type_of
    ((i0, type_to_type_scheme (Arrow t1 t')) :: (i1, gen_type t0 env) :: env)
    e t').
intro.
generalize
 (typage_is_stable_by_substitution e t'
    ((i0, type_to_type_scheme (Arrow t1 t')) :: (i1, gen_type t0 env) :: env)
    (rename_to_subst r) H1).
simpl in |- *.
rewrite s_env_when_s_disjoint_with_env3.
rewrite (s_ts_when_s_disjoint_with_ts (rename_to_subst r) (gen_type t0 env)).
rewrite
 (gen_type_add_env env t0
    (extend_subst_type_scheme (rename_to_subst r)
       (Arrow_ts (type_to_type_scheme t1) (type_to_type_scheme t'))) i0)
 .
intro.
rewrite <- (inverse_rename_rename_is_identity r t').
rewrite <-
 (s_env_when_s_disjoint_with_env3 (rename_to_subst (inverse_rename r)) env)
 .
rewrite <- (inverse_rename_rename_is_identity r t1).
rewrite type_to_type_scheme_commutes_with_subst.

rewrite type_to_type_scheme_commutes_with_subst.
rewrite type_to_type_scheme_commutes_with_subst.
rewrite extend_subst_ts_arrow_rewrite.
rewrite <- subst_add_type_scheme.
apply typage_is_stable_by_substitution.
apply H with (Er := er) (e0 := e0) (i1 := i1) (t0 := t0); auto.
unfold add_environment in |- *.
apply typing_commute_env; auto.
rewrite type_to_type_scheme_commutes_with_subst.
unfold add_environment in H15.
auto.

unfold add_environment in |- *.
apply env_extension_bis; auto.

inversion ren.
simpl in H19.
apply disjoint_list_and_union_inversion1 with (l2 := FV_type t'); auto.

inversion ren.
rewrite H17.
apply gen_vars_is_a_set.

inversion ren; auto.

rewrite domain_of_substitution_rename_to_subst.
rewrite domain_inverse_rename.
inversion ren.
apply are_disjoints_symetry; auto.

inversion ren.
simpl in H19.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type t1); auto.

inversion ren.
rewrite H17.
apply gen_vars_is_a_set.

inversion ren; auto.

inversion ren.
change
  (are_disjoints (gen_vars t0 env)
     (FV_type_scheme
        (extend_subst_type_scheme (rename_to_subst r)
           (type_to_type_scheme (Arrow t1 t'))))) in |- *.
rewrite <- type_to_type_scheme_commutes_with_subst.
rewrite FV_type_scheme_type_to_type_scheme.
apply disjoints_ren; auto.

rewrite domain_of_substitution_rename_to_subst.
inversion ren.
rewrite H16.
unfold gen_type in |- *.
apply disjoint_subset_bis with (l2 := FV_env env).
apply are_disjoints_symetry.
apply free_and_bound_are_disjoints.

apply FV_gen_t_env_included_in_env.

inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H16.
apply free_and_bound_are_disjoints.

apply typing_redundant_env with (ts2 := type_to_type_scheme t1); auto.

absurd (i1 = i0); auto.

absurd (i1 = i0); auto.

(*~i=i0*)
do 3 intro.
elim (identifier_dec i1 i0); intros i1_is_i0.
(**i1=i0*)rewrite i1_is_i0; intros.
inversion H0.
rewrite (eq_identifier_reflexivity i0) in H6; discriminate H6.

apply (env_extension (Rec i i0 e) i0 (gen_type t0 env) t env); auto.
apply not_is_free_in_rec.

 absurd (i = i0); auto.

(**~i1=i0*)
intros; inversion H0.
inversion_clear H1.
apply type_of_rec_fun.
unfold add_environment in H14.
elim
 (exists_renaming_not_concerned_with2 (gen_vars t0 env) 
    (FV_env env) (FV_type (Arrow t1 t')) (gen_vars_is_a_set t0 env)).
intros r ren.
generalize
 (typage_is_stable_by_substitution e t'
    ((i, type_to_type_scheme (Arrow t1 t'))
     :: (i0, type_to_type_scheme t1) :: (i1, gen_type t0 env) :: env)
    (rename_to_subst r) H14).
simpl in |- *.
rewrite s_env_when_s_disjoint_with_env3.
rewrite (s_ts_when_s_disjoint_with_ts (rename_to_subst r) (gen_type t0 env)).
rewrite
 (gen_type_add_env env t0
    (extend_subst_type_scheme (rename_to_subst r) (type_to_type_scheme t1))
    i0).
rewrite
 (gen_type_add_env
    (add_environment env i0
       (extend_subst_type_scheme (rename_to_subst r) (type_to_type_scheme t1)))
    t0
    (extend_subst_type_scheme (rename_to_subst r)
       (Arrow_ts (type_to_type_scheme t1) (type_to_type_scheme t'))) i)
 .
intro.
rewrite <- (inverse_rename_rename_is_identity r t').
rewrite <-
 (s_env_when_s_disjoint_with_env3 (rename_to_subst (inverse_rename r)) env)
 .
rewrite <- (inverse_rename_rename_is_identity r t1).
rewrite type_to_type_scheme_commutes_with_subst.
rewrite type_to_type_scheme_commutes_with_subst.
rewrite type_to_type_scheme_commutes_with_subst.
rewrite extend_subst_ts_arrow_rewrite.
rewrite <- subst_add_type_scheme.
rewrite <- subst_add_type_scheme.
apply typage_is_stable_by_substitution.
apply H with (Er := er) (e0 := e0) (i1 := i1) (t0 := t0); auto.
unfold add_environment in |- *.
rewrite type_to_type_scheme_commutes_with_subst.
unfold add_environment in H1.
apply
 type_of_env_equiv
  with
    (env := (i,
            Arrow_ts
              (extend_subst_type_scheme (rename_to_subst r)
                 (type_to_type_scheme t1))
              (extend_subst_type_scheme (rename_to_subst r)
                 (type_to_type_scheme t')))
            :: (i0,
               extend_subst_type_scheme (rename_to_subst r)
                 (type_to_type_scheme t1))
               :: (i1,
                  gen_type t0
                    ((i,
                     extend_subst_type_scheme (rename_to_subst r)
                       (Arrow_ts (type_to_type_scheme t1)
                          (type_to_type_scheme t')))
                     :: (i0,
                        extend_subst_type_scheme (rename_to_subst r)
                          (type_to_type_scheme t1)) :: env)) :: env).
apply
 env_equiv_trans
  with
    (env' := (i,
             Arrow_ts
               (extend_subst_type_scheme (rename_to_subst r)
                  (type_to_type_scheme t1))
               (extend_subst_type_scheme (rename_to_subst r)
                  (type_to_type_scheme t')))
             :: (i1,
                gen_type t0
                  ((i,
                   Arrow_ts
                     (extend_subst_type_scheme (rename_to_subst r)
                        (type_to_type_scheme t1))
                     (extend_subst_type_scheme (rename_to_subst r)
                        (type_to_type_scheme t')))
                   :: (i0,
                      extend_subst_type_scheme (rename_to_subst r)
                        (type_to_type_scheme t1)) :: env))
                :: (i0,
                   extend_subst_type_scheme (rename_to_subst r)
                     (type_to_type_scheme t1)) :: env).
apply env_equiv_cons.
apply env_equiv_commute; auto.


apply env_equiv_commute; auto.
unfold not in |- *; intro.
rewrite H15 in H7; rewrite (eq_identifier_reflexivity i1) in H7;
 discriminate H7.

auto.

unfold add_environment in |- *.
apply env_extension_bis; auto.
apply env_extension_bis; auto.

inversion ren.
simpl in H18.
apply disjoint_list_and_union_inversion1 with (l2 := FV_type t'); auto.

inversion ren.
rewrite H16.
apply gen_vars_is_a_set.

inversion ren; auto.

rewrite domain_of_substitution_rename_to_subst.
rewrite domain_inverse_rename.
inversion ren.
apply are_disjoints_symetry; auto.

inversion ren.
simpl in H18.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type t1); auto.

inversion ren.
rewrite H16.
apply gen_vars_is_a_set.

inversion ren; auto.

rewrite (gen_vars_add_environment_rename t0 t1 t' env r i0); auto.
change
  (are_disjoints (gen_vars t0 env)
     (FV_type_scheme
        (extend_subst_type_scheme (rename_to_subst r)
           (type_to_type_scheme (Arrow t1 t'))))) in |- *.
rewrite <- type_to_type_scheme_commutes_with_subst.
rewrite FV_type_scheme_type_to_type_scheme.
apply disjoints_ren; auto.

inversion ren; auto.

inversion ren; auto.
rewrite H15.
apply free_and_bound_are_disjoints.

inversion ren.
auto.

inversion ren.
simpl in H17; apply are_disjoints_symetry; auto.

inversion ren.
rewrite H15.
auto.

inversion ren.
apply
 disjoint_list_and_union_inversion1
  with
    (l2 := FV_type_scheme
             (extend_subst_type_scheme (rename_to_subst r)
                (type_to_type_scheme t'))).
change
  (are_disjoints (gen_vars t0 env)
     (FV_type_scheme
        (extend_subst_type_scheme (rename_to_subst r)
           (type_to_type_scheme (Arrow t1 t'))))) in |- *.
rewrite <- type_to_type_scheme_commutes_with_subst.
rewrite FV_type_scheme_type_to_type_scheme.
apply disjoints_ren; auto.

inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H15; simpl in |- *.
apply disjoint_subset_bis with (l2 := FV_env env).
apply are_disjoints_symetry.
apply free_and_bound_are_disjoints.

unfold gen_type in |- *.
apply FV_gen_t_env_included_in_env.

inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H15.
apply free_and_bound_are_disjoints.

absurd (i1 = i0); auto.

rewrite <- H6.
rewrite <- H6 in H1.
apply env_extension with (v := i1) (ts := gen_type t0 env); auto.
apply not_is_free_in_rec2.

Qed.


Lemma substitution_lemma :
 forall (E Er e0 : expr) (i : identifier) (env : environment) (t t0 : type),
 substitute i e0 E Er ->
 type_of ((i, gen_type t0 env) :: env) E t ->
 type_of env e0 t0 -> type_of env Er t.

simple induction E.

(* constante *)
intros.
inversion_clear H.
inversion_clear H0.
auto.

(* Variable *)
do 4 intro.
elim (identifier_dec i i0); intro y.

(* i = i0 *)
rewrite y; intros.
inversion H.
rewrite (eq_identifier_reflexivity i0) in H5; discriminate H5.

rewrite <- H5.
inversion_clear H0.
simpl in H4; rewrite (eq_identifier_reflexivity i0) in H4; simpl in H4.
injection H4.
unfold gen_type in |- *; intro H0.
rewrite <- H0 in H6.
inversion_clear H6.
elim H7; intros.
elim (product_list_exists t0 env x); eauto.
intros phi def_phi.
rewrite <-
 (gen_subst_to_subst_aux_4 env t0 t nil (snd (gen_aux t0 env nil)) x phi)
 ; auto.
rewrite <- (s_env_when_s_disjoint_with_env3 phi env).
apply typage_is_stable_by_substitution; auto.

rewrite (domain_product (snd (gen_aux t0 env nil)) x phi def_phi).
apply are_disjoints_symetry; auto.



(* ~i=i0 *)
intros; inversion H0.
simpl in H3; rewrite (eq_identifier_diff i i0 y) in H3; simpl in H3.
rewrite (inv_subst_var i i0 e0 Er y H).
apply (type_of_var env i t ts); auto.

(* Lambda *)

do 6 intro; elim (identifier_dec i i0); intro y.
(* i = i0 *)
rewrite y; intros.
inversion H0.
rewrite (eq_identifier_reflexivity i0) in H5; discriminate H5.

apply (env_extension (Lambda i0 e) i0 (gen_type t0 env) t env); auto.

(* ~ i=i0 *)
intros.
inversion H0.
inversion_clear H1.
apply type_of_lambda.
unfold add_environment in H11.
elim
 (exists_renaming_not_concerned_with2 (gen_vars t0 env) 
    (FV_env env) (FV_type (Arrow t1 t')) (gen_vars_is_a_set t0 env)).
intros r ren.
generalize
 (typage_is_stable_by_substitution e t'
    ((i, type_to_type_scheme t1) :: (i0, gen_type t0 env) :: env)
    (rename_to_subst r) H11).
simpl in |- *.
rewrite s_env_when_s_disjoint_with_env3.
rewrite (s_ts_when_s_disjoint_with_ts (rename_to_subst r) (gen_type t0 env)).
rewrite
 (gen_type_add_env env t0
    (extend_subst_type_scheme (rename_to_subst r) (type_to_type_scheme t1)) i)
 .
intro.
rewrite <- (inverse_rename_rename_is_identity r t').
rewrite <-
 (s_env_when_s_disjoint_with_env3 (rename_to_subst (inverse_rename r)) env)
 .
rewrite <- (inverse_rename_rename_is_identity r t1).
rewrite <- subst_add_type.
apply typage_is_stable_by_substitution.
apply H with (Er := er) (e0 := e0) (i := i0) (t0 := t0); auto.
unfold add_environment in |- *.
unfold add_environment in H1.
apply typing_commute_env; auto.
rewrite type_to_type_scheme_commutes_with_subst.
auto.

unfold add_environment in |- *.
apply env_extension_bis; auto.

inversion ren.
simpl in H15.
apply disjoint_list_and_union_inversion1 with (l2 := FV_type t'); auto.

inversion ren.
rewrite H13.
apply gen_vars_is_a_set.

inversion ren; auto.

rewrite domain_of_substitution_rename_to_subst.
rewrite domain_inverse_rename.
inversion ren.
apply are_disjoints_symetry; auto.

inversion ren.
simpl in H15.
apply disjoint_list_and_union_inversion2 with (l1 := FV_type t1); auto.

inversion ren.
rewrite H13.
apply gen_vars_is_a_set.

inversion ren; auto.

rewrite <- type_to_type_scheme_commutes_with_subst.
rewrite FV_type_scheme_type_to_type_scheme.
apply disjoints_ren; auto.
inversion ren.
apply renaming_of_not_concerned_with_intro; auto.
simpl in H14.
apply disjoint_list_and_union_inversion1 with (l2 := FV_type t'); auto.


inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H12; simpl in |- *.
unfold gen_type in |- *.
apply disjoint_subset_bis with (l2 := FV_env env).
apply are_disjoints_symetry.
apply free_and_bound_are_disjoints.

apply FV_gen_t_env_included_in_env.

inversion ren.
rewrite domain_of_substitution_rename_to_subst.
rewrite H12; simpl in |- *.
apply free_and_bound_are_disjoints.


absurd (i = i0); auto.

(*Rec*)
exact conserv_par_sbst_rec_case.

(*Apply*)
intros.
inversion_clear H1.
inversion_clear H2.
apply type_of_app with (t := t1).
apply (H er1 e1 i env (Arrow t1 t) t0); auto.

apply (H0 er2 e1 i env t1 t0); auto.

(*Let in*)
 do 8 intro.
elim (identifier_dec i i0); intros eq_hyp.

(*i=i0*)
rewrite eq_hyp; intros.
inversion H1.
rewrite (eq_identifier_reflexivity i0) in H10; simpl in |- *;
 discriminate H10.

inversion_clear H2.
apply type_of_let_in with (t := t1); auto.
apply (H er1 e1 i0 env t1 t0); auto.
unfold add_environment in H11.
generalize
 (typing_redundant_env e0 i0 (gen_type t1 ((i0, gen_type t0 env) :: env))
    (gen_type t0 env) t env H11).
intro Hyp.
apply
 typing_in_a_more_general_env
  with (env2 := (i0, gen_type t1 ((i0, gen_type t0 env) :: env)) :: env);
 auto.
unfold add_environment in |- *.
apply more_general_env_cons; auto.
apply more_gen_subset_gen.
simpl in |- *; apply l2_subset_of_union_l1_l2.

(*i~=i0*)
intros; inversion H1.
inversion_clear H2.
apply type_of_let_in with (t := t1); auto.
apply (H er1 e1 i0 env t1 t0); auto.
unfold add_environment in H15.
apply (H0 er2 e1 i0 (add_environment env i (gen_type t1 env)) t t0); auto.
unfold add_environment in |- *.
apply
 typing_in_a_more_general_env
  with (env2 := (i0, gen_type t0 env) :: (i, gen_type t1 env) :: env); 
 auto.
apply more_general_env_cons; auto.
apply more_gen_subset_gen.
simpl in |- *.
apply union_subset; auto.
unfold gen_type in |- *.
apply FV_gen_t_env_included_in_env.

apply typing_commute_env; auto.
apply
 typing_in_a_more_general_env
  with
    (env2 := (i, gen_type t1 ((i0, gen_type t0 env) :: env))
             :: (i0, gen_type t0 env) :: env); auto.
apply more_general_env_cons; auto.
apply more_gen_subset_gen.
simpl in |- *; apply l2_subset_of_union_l1_l2.


unfold add_environment in |- *.
apply (env_extension_bis e1 i (gen_type t1 env) t0 env H7 H3).

absurd (i = i0); auto.
Qed.

(****************************************************************************)
(*              reduction preserves types                                   *)
(****************************************************************************)

Lemma reduction_preserves_types_red :
 forall (env : environment) (e1 e2 : expr) (c : context),
 reduction e1 e2 ->
 (forall t : type, type_of env e1 t -> type_of env e2 t) ->
 est_MLcontext c ->
 forall t : type,
 type_of env (apply_context c e1) t -> type_of env (apply_context c e2) t.

do 6 intro.
simple induction 1; unfold apply_context in |- *; intros.
auto.

inversion_clear H4.
apply type_of_app with (t := t0); auto.

inversion_clear H5.
apply type_of_app with (t := t0); auto.

inversion_clear H4.
apply type_of_let_in with (t := t0); auto.
Qed.


Theorem reduction_preserves_types :
 forall (e1 e2 : expr) (env : environment),
 reduction e1 e2 -> forall t : type, type_of env e1 t -> type_of env e2 t.
(*Preuve par recurrence sur la structure de la reduction *)
simple induction 1; auto.

(* Lambda *)
intros; inversion H2.
apply (substitution_lemma e0 er e i env t t0); auto.
inversion H6.
unfold add_environment in H11.
apply
 typing_in_a_more_general_env
  with (env2 := (i, type_to_type_scheme t0) :: env); 
 auto.
apply more_general_env_cons; auto.
apply gen_t_env_more_general_than_t.


(* Let_in_red_vrai *)
intros; inversion H2.
apply (substitution_lemma e3 er e0 i env t t0); auto.

(* Rec_in_red_vrai *)
intros; inversion H3.
apply (substitution_lemma er er' e i env t t0); auto.
inversion H7.
unfold add_environment in H12.
apply
 typing_in_a_more_general_env
  with (env2 := (i, type_to_type_scheme t0) :: env); 
 auto.
apply more_general_env_cons; auto.
apply gen_t_env_more_general_than_t.

apply
 (substitution_lemma e0 er (Rec f i e0) f
    ((i, type_to_type_scheme t0) :: env) t (Arrow t0 t)); 
 auto.
apply
 typing_in_a_more_general_env
  with
    (env2 := (f, type_to_type_scheme (Arrow t0 t))
             :: (i, type_to_type_scheme t0) :: env); 
 auto.
apply more_general_env_cons; auto.
rewrite <- bind_list_gen_type_rwt.
apply bind_l_ts_more_gen_than_ts.

apply env_extension_bis; auto.
apply not_is_free_in_rec.

(*context*)
exact (reduction_preserves_types_red env).

Qed.

(* NON utilise
Lemma not_in_range_of_rename_subst : 
(r: (list stamp*stamp))(s : stamp)
 (in_list_stamp s (range_of_rename_subst r))=false
-> (in_list_stamp s (range_of_substitution (rename_to_subst r)))=false
Induction r;Auto.
 
Intro;Elim a; Intros v v'; Do 3 Intro;Simpl.
(Elim (stamp_dec s v'); Intro).
Rewrite -> y;Rewrite -> eq_stamp_reflexivity;Simpl.
(Intros PB; Discriminate PB).

(Rewrite -> eq_stamp_diff; Auto).
Simpl;Intro.
Elim (bool_dec
        (in_list_stamp v' (range_of_substitution (rename_to_subst l))));
 Intro;Rewrite -> y0; Simpl.
Auto.

(Rewrite -> eq_stamp_diff; Auto).
Simpl;Auto.
Qed.
*)
