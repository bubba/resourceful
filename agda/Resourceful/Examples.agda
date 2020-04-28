module Resourceful.Examples where

open import Resourceful.Semantics.Static
open import Resourceful.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

_ : ∅ ⊢ use File □ ⋎ use Net □ ⦂ IO (` File ∪  ` Net) (□ × □)
_ = ⊢⋎ (⊢use ⊢□) (⊢use ⊢□) (OkS OkZ OkZ (DHZ λ ()))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use Net □ ⦂ IO (` File ∪ ` Net) □
_ = let ok = OkS OkZ OkZ (DHZ λ ())
        in ⊢>>= (⊢sub (⊢use ⊢□) (≥:∪ˡ ≥:refl) ok)
                (⊢ƛ (⊢sub (⊢use ⊢□) (≥:∪ʳ ≥:refl) ok))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use Net □ ⦂ IO World □
_ = ⊢>>= (⊢sub (⊢use ⊢□) (≥:World) OkWorld) (⊢ƛ (⊢sub (⊢use ⊢□) ≥:World OkWorld))

_ : ∅ ⊢ use File □ >>= ƛ "x" ⇒ use File □ ⦂ IO (` File) □
_ = ⊢>>= (⊢use ⊢□) (⊢ƛ (⊢use ⊢□))


z : ∀ {Γ r} → ¬ (Γ ⊢ ⟦ □ ⟧ ⦂ IO (` r ∪ ` r) □)
z (⊢⟦⟧ ⊢e ok) = ¬okρ∪ρ ok
z (⊢sub _ _ ok) = ¬okρ∪ρ ok

-- monadic binding and how lifting adapts to the resource
_ : ∅ ⊢ lt "x" ⇐ (ƛ "y" ⇒ ⟦ □ ⟧) in' ((` "x" · □) >>= (ƛ "z" ⇒ use File (` "z"))) ⦂ IO (` File) □
_ = ⊢lt (⊢ƛ {τ' = ` "α"}
            (⊢⟦⟧ ⊢□ OkZ))
        (⊢>>= (⊢· (⊢` Z (Inst (SS "α" □ SZ) refl refl))
                  ⊢□)
              (⊢ƛ (⊢use (⊢` Z (Inst SZ refl subTSZ)))))

-- let polymoprhism
_ : ∅ ⊢ lt "x" ⇐ (ƛ "z" ⇒ ` "z") in' (` "x" · ` "x") · (` "x" · □ ) ⦂ □
_ = ⊢lt (⊢ƛ {τ' = ` "α"} {τ = ` "α"} (⊢` Z (Inst SZ refl refl)))
        (⊢· (⊢· (⊢` Z (Inst (SS "α" (□ ⇒ □) SZ) refl refl))
                (⊢` Z (Inst (SS "α" □ SZ) refl refl)))
            (⊢· (⊢` Z (Inst (SS "α" □ SZ) refl refl))
                ⊢□))

-- a simple usage of the concurrency operator
_ : ∅ ⊢ ((ƛ "x" ⇒ use File (` "x")) · □) ⋎ (use Net □) ⦂ IO (` File ∪ ` Net) (□ × □)
_ = ⊢⋎ (⊢· (⊢ƛ (⊢use (⊢` Z (Inst SZ refl refl))))
           ⊢□)
       (⊢use ⊢□) (OkS OkZ OkZ (DHZ (λ ())))


-- an example of how IO monads can be subsumed into using more resources
-- than necessary
_ : ∅ , "writeFile" ⦂ ` (□ ⇒ IO (` File) □)
    ⊢ (use File □) ⋎ (use Net □) >>= ƛ "x" ⇒ (` "writeFile") · (π₁ (` "x"))
      ⦂ IO (` File ∪ ` Net) (□)
_ = ⊢>>= (⊢⋎ (⊢use ⊢□) (⊢use ⊢□) okFN)
         (⊢ƛ (⊢sub (⊢· (⊢` (S Z (λ ())) (Inst SZ refl refl))
                         (⊢π₁ (⊢` Z (Inst SZ refl refl))))
                     (≥:∪ˡ ≥:refl)
                     okFN))
  where okFN : Ok (` File ∪ ` Net)
        okFN = OkS OkZ OkZ (DHZ (λ ()))
