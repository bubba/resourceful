-- Proofs relating to well-typed heaps (Section 6.2)
module Resourceful.HeapProperties where

open import Resourceful.Grammar
open import Resourceful.Substitution
open import Resourceful.Semantics.Static
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Well formed types
data OkT : Type → Set where
  Ok□ : OkT □
  Ok⇒ : ∀ {τ τ'}
      → OkT τ
      → OkT τ'
      → OkT (τ ⇒ τ')
  Ok× : ∀ {τ τ'}
      → OkT τ → OkT τ'
      → OkT (τ × τ')
  OkIO : ∀ {ρ τ}
      → OkT τ
      → Ok ρ
      → OkT (IO ρ τ)

-- Well formed type schemes
data OkTS : TypeScheme → Set where
  OkTSVV : ∀ {αs τ}
         → OkT τ
         → OkTS (VV αs τ)

-- Well formed contexts
data OkC : Context → Set where
  OkCZ : OkC ∅
  OkCS : ∀ {Γ x σ}
       → OkC Γ
       → OkTS σ
       → OkC (Γ , x ⦂ σ)


oktsub : ∀ {s τ} → OkT τ → OkT (subT s τ)
oktsub {s} {τ ⇒ τ₁} (Ok⇒ okt okt₁) = Ok⇒ (oktsub okt) (oktsub okt₁)
oktsub {s} {IO x τ} (OkIO okt x₁) = OkIO (oktsub okt) x₁ 
oktsub {s} {□} okt = Ok□
oktsub {s} {τ × τ₁} (Ok× okt okt₁) = Ok× (oktsub okt) (oktsub okt₁)

oktstoτ : ∀ {σ τ} → OkTS σ → σ > τ → OkT τ
oktstoτ {σ} (OkTSVV {αs} {τ} okτ) (Inst s x₁ refl) with oktsub {s} okτ | TStype (VV αs τ) | TStype≡ {αs} {τ}
... | oks | .τ | refl = oks

mustBeOk : ∀ {Γ e ρ τ} → OkC Γ → Γ ⊢ e ⦂ IO ρ τ → Ok ρ
-- too narrow: need to expand from ∅
-- but with ` x, someone can just stick in a type x ⦂ IO (`File∪`File) □ ∈ Γ
-- key observation here:
-- for a type of IO ρ τ to be introduced
-- it must come from either ⊢⟦⟧ or ⊢use
mustBeOk (OkCS okc x) (⊢` Z σ>τ) with oktstoτ x σ>τ
... | OkIO z okρ = okρ
mustBeOk (OkCS okc x) (⊢` (S x∈ x₁) σ>τ) = mustBeOk okc (⊢` x∈ σ>τ)
mustBeOk okc (⊢· ⊢e ⊢e') = {!!}
mustBeOk OkCZ (⊢lt ⊢e ⊢e') = let eok = mustBeOk (OkCS OkCZ {!OkTS!}) ⊢e' in {!!}
mustBeOk (OkCS okc x) (⊢lt ⊢e ⊢e') = let eok = mustBeOk (OkCS okc {!!}) {!!} in {!!}
mustBeOk okc (⊢π₁ ⊢e) = {!!}
mustBeOk okc (⊢π₂ ⊢e) = {!!}
mustBeOk okc (⊢⟦⟧ ⊢e ok) = ok
mustBeOk okc (⊢>>= ⊢e ⊢e₁) = mustBeOk okc ⊢e
mustBeOk okc (⊢⋎ ⊢e₁ ⊢e₂ ok) = ok
mustBeOk okc (⊢sub ⊢e x ok) = ok
mustBeOk okc (⊢use ⊢e) = OkZ

okIO : ∀ {Γ e τ ρ} → OkC Γ → Γ ⊢ e ⦂ IO ρ τ → OkT (IO ρ τ)
okIO okc ⊢e = {!!}

