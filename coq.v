Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A. 
 Qed.

Theorem forward_small: (forall A B: Prop, A -> (A->B) -> B).
Proof.
  intros A.
  intros B.
  intros proof_of_A.
  intros A_implies_B.
  pose (proof_of_B := A_implies_B proof_of_A).
  exact proof_of_B.
Qed.

Theorem backward_small: (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros A B.
  intros proof_of_A A_implies_B.
  refine (A_implies_B _).
    exact proof_of_A.
Qed.

Theorem backward_large : (forall A B C : Prop, A -> (A -> B) -> (B -> C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B B_implies_C.
  refine (B_implies_C _).
  refine (A_implies_B _).
  exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B A_imp_B_imp_C.
  refine (A_imp_B_imp_C _ _).
  exact proof_of_A.
  refine (A_implies_B proof_of_A).
Qed.

Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
  intros A B C.
  intros proofA AimpB AimpBimpC.
  pose (proofB := AimpB proofA).
  pose (proofC := AimpBimpC proofA proofB).
  exact proofC.
  Show Proof.
Qed.

Theorem True_can_be_proven : True.
  exact I.
Qed.

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven_again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem Thm_true_imp_true : True -> True.
Proof.
  intros proof_of_True.
  exact I.
Qed.

Theorem Thm_true_imp_false : ~(True -> False).
Proof.
  intros T_implies_F.
  refine (T_implies_F I).
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~A -> C.
Proof.
  intros A C.
  intros proofA notA.
  unfold not in notA.
  pose (proofFalse := notA proofA).
  case proofFalse.
Qed.

Require Import Bool.

Theorem true_is_True : Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    simpl.
    exact I.

    simpl.
    exact I.
Qed.

  
