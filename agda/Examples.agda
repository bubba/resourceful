module Examples where

open import Resourceful
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

_ : ∅ ⊢ use File □ ⋎ use Net □ ⦂ IO (` File ∪  ` Net) (□ × □)
_ = ⊢⋎ (⊢use ⊢□) (⊢use ⊢□) (OkS OkZ OkZ (DHZ λ ()))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use Net □ ⦂ IO (` File ∪ ` Net) □
_ = let ok = OkS OkZ OkZ (DHZ λ ())
        in ⊢>>= (⊢IOsub (⊢use ⊢□) (≥:∪₂ ≥:Refl) ok)
                (⊢ƛ (⊢IOsub (⊢use ⊢□) (≥:∪₁ ≥:Refl) ok))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use Net □ ⦂ IO World □
_ = ⊢>>= (⊢IOsub (⊢use ⊢□) (≥:World) OkWorld) (⊢ƛ (⊢IOsub (⊢use ⊢□) ≥:World OkWorld))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use File □ ⦂ IO (` File) □
_ = ⊢>>= (⊢use ⊢□) (⊢ƛ (⊢use ⊢□))

¬x∩x=∅ : ∀ {ρ} → ¬ (ρ ∩ ρ =∅)
¬x∩x=∅ (DHZ x) = x refl
¬x∩x=∅ (DHL dist dist₁ dist₂) = ¬x∩x=∅ (distinct-∪ˡ (distinct-sym dist))
¬x∩x=∅ (DHR dist dist₁ dist₂) = ¬x∩x=∅ (distinct-∪ʳ (distinct-sym dist₁))
¬okρ∪ρ : ∀ {ρ} → ¬ Ok (ρ ∪ ρ)
¬okρ∪ρ (OkS ok ok₁ dist) = ¬x∩x=∅ dist

z : ∀ {Γ r} → ¬ (Γ ⊢ ⟦ □ ⟧ ⦂ IO (` r ∪ ` r) □)
z (⊢⟦⟧ ⊢e ok) = ¬okρ∪ρ ok
z (⊢IOsub _ _ ok) = ¬okρ∪ρ ok

-- mustBeConc : ∀ {Γ e τ ρ} → 


-- n : ¬ (∅ ⊢ use File □ ⋎ use File □ ⦂ IO (` File ∪  ` File) (□ × □))
-- n (⊢⋎ ⊢e ⊢e₁ (DHZ x)) = x refl
-- n (⊢IOsub ⊢e x) = let z = n ⊢e in ?

_ : ∅ ⊢ lt "x" ⇐ (ƛ "y" ⇒ ⟦ □ ⟧) in' ((` "x" · □) >>= (ƛ "z" ⇒ use File (` "z"))) ⦂ IO (` File) □
_ = ⊢lt (⊢ƛ {τ' = ` "α"}
            (⊢⟦⟧ ⊢□ OkZ))
        (⊢>>= (⊢· (⊢` Z (General (SS "α" □ SZ) refl refl))
                  ⊢□)
              (⊢ƛ (⊢use (⊢` Z (General SZ refl subTSZ)))))
