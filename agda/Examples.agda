module Examples where

open import Resourceful
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

_ : ∅ ⊢ use File □ ⋎ use Net □ ⦂ IO (` File ∪  ` Net) (□ × □)
_ = ⊢⋎ (⊢use ⊢□) (⊢use ⊢□) (DHZ λ ())

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use Net □ ⦂ IO (` File ∪ ` Net) □
_ = ⊢>>= (⊢IOsub (⊢use ⊢□) (≥:∪₂ ≥:Refl)) (⊢ƛ (⊢IOsub (⊢use ⊢□) (≥:∪₁ ≥:Refl)))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use Net □ ⦂ IO World □
_ = ⊢>>= (⊢IOsub (⊢use ⊢□) (≥:World)) (⊢ƛ (⊢IOsub (⊢use ⊢□) ≥:World))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use File □ ⦂ IO (` File) □
_ = ⊢>>= (⊢use ⊢□) (⊢ƛ (⊢use ⊢□))

z : ∀ {Γ r} → Γ ⊢ ⟦ □ ⟧ ⦂ IO (` r ∪ ` r) □
z = ⊢⟦⟧ ⊢□
-- mustBeConc : ∀ {Γ e τ ρ} → 

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

-- n : ¬ (∅ ⊢ use File □ ⋎ use File □ ⦂ IO (` File ∪  ` File) (□ × □))
-- n (⊢⋎ ⊢e ⊢e₁ (DHZ x)) = x refl
-- n (⊢IOsub ⊢e x) = let z = n ⊢e in ?
