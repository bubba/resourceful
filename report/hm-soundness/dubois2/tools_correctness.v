(* Author : Catherine Dubois *)

Require Import generic_DB.
Require Import langs.
Require Import type_scheme.


Lemma compute_generic_subst_create_generic_instance :
 forall (ts : type_scheme) (st : stamp) (t : type),
 apply_subst_gen (fst (compute_generic_subst st (max_gen_vars ts))) ts =
 Some_subst_gen t -> is_gen_instance t ts.

Proof.
intros.
apply (gen_instance_intro t ts).
exists (fst (compute_generic_subst st (max_gen_vars ts))).
auto.
Qed.






