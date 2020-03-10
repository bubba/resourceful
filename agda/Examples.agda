module Examples where

open import Resourceful
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

_ : ∅ ⊢ readFile ⋎ readNet ⦂ IO (` File ∪  ` Net) (□ × □)
_ = ⊢⋎ ⊢readFile ⊢readNet (DHZ λ ())

_ : ∅ ⊢ readFile >>= ƛ "x" ⇒ readNet ⦂ IO (` File ∪ ` Net) □
_ = ⊢>>= (⊢IOsub ⊢readFile (≥:∪₂ ≥:Refl)) (⊢ƛ (⊢IOsub ⊢readNet (≥:∪₁ ≥:Refl)))

_ : ∅ ⊢ readFile >>= ƛ "x" ⇒ readNet ⦂ IO World □
_ = ⊢>>= (⊢IOsub ⊢readFile (≥:World)) (⊢ƛ (⊢IOsub ⊢readNet ≥:World))

_ : ∅ ⊢ readFile >>= ƛ "x" ⇒ readFile ⦂ IO (` File) □
_ = ⊢>>= ⊢readFile (⊢ƛ ⊢readFile)



noResourceClash : ∀ {Γ e τ ρ} → ¬ (Γ ⊢ e ⦂ IO (ρ ∪ ρ) τ)
noResourceClash (⊢` x x₁) = {!!}
noResourceClash (⊢· ⊢e ⊢e₁) = {!!}
noResourceClash (⊢lt ⊢e ⊢e₁) = {!!}
noResourceClash (⊢π₁ ⊢e) = {!!}
noResourceClash (⊢π₂ ⊢e) = {!!}
noResourceClash (⊢⟦⟧ ⊢e) = {!!}
noResourceClash (⊢>>= ⊢e ⊢e₁) = {!!}
noResourceClash (⊢⋎ ⊢e ⊢e₁ x) = {!!}
noResourceClash (⊢IOsub ⊢e x) = {!!}

n : ¬ (∅ ⊢ readFile ⋎ readFile ⦂ IO (` File ∪  ` File) (□ × □))
n (⊢⋎ ⊢e ⊢e₁ (DHZ x)) = x refl
n (⊢IOsub ⊢e x) = {!!}
