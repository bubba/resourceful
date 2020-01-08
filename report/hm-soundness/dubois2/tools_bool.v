(* Authors : Catherine Dubois, Valerie Menissier-Morain *)

Definition if_ (T : Set) (b : bool) (then_case else_case : T) :=
  match b with
  | true => then_case
  | _ => else_case
  end.

Lemma if_same_results_true :
 forall b b1 b2 : bool, b1 = true -> b2 = true -> if_ bool b b1 b2 = true.

Proof.
intros b b1 b2 eq1 eq2; rewrite eq1; rewrite eq2.
elim b; simpl in |- *; auto.
Qed.

Lemma if_true_false :
 forall b b2 : bool, if_ bool b true b2 = false -> b = false /\ b2 = false.

Proof.
simple induction b.
(* b=true *)
simpl in |- *; intros; inversion H.
(* b=false *)
simpl in |- *; auto.
Qed.

Lemma if_true_false_inversion :
 forall b b2 : bool, b = false -> b2 = false -> if_ bool b true b2 = false.

Proof.
simple induction b.
(* b=true *)
simpl in |- *; intros; inversion H.
(* b=false *)
simpl in |- *; auto.
Qed.

Lemma if_false_true :
 forall b b1 : bool, if_ bool b b1 false = true -> b = true /\ b1 = true.

Proof.
simple induction b.
(* b=true *)
simpl in |- *; auto.
(* b=false *)
simpl in |- *; intros; inversion H.
Qed.

Lemma bool_dec : forall b : bool, {b = true} + {b = false}.

Proof.
simple induction b; auto.
Qed.

Lemma contrapp :
 forall b1 b2 : bool, (b1 = true -> b2 = true) -> b2 = false -> b1 = false.

Proof.
simple induction b1; simple induction b2.
intros; assumption.
intros; symmetry  in |- *; apply H; auto.
auto.
auto.
Qed.

Lemma contrapp2 :
 forall b1 b2 b3 : bool,
 (b1 = true -> b2 = true \/ b3 = true) ->
 b2 = false -> b3 = false -> b1 = false.

Proof.
simple induction b1; simple induction b2; simple induction b3; auto.
intros; elim H; auto.
Qed.

(* Auxiliary lemma *)
Lemma not_true_is_false : forall b : bool, b <> true -> b = false.

Proof.
simple induction b.
(* true *)
intro; elim H; auto.
(* false *)
intro; auto.
Qed.
