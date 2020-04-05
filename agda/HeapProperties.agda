module HeapProperties where

open import Resourceful
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

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

data OkTS : TypeScheme → Set where
  OkTSZ : ∀ {αs τ} → OkT τ → OkTS (VV αs τ)
  -- OkTSZ : ∀ {τ}
  --       → OkT τ
  --       → OkTS (` τ)
  -- OkTSS : ∀ {σ α}
  --       → OkTS σ
  --       → OkTS (V α · σ)

data OkC : Context → Set where
  OkCZ : OkC ∅
  OkCS : ∀ {Γ x σ}
       → OkC Γ
       → OkTS σ
       → OkC (Γ , x ⦂ σ)


-- OkC Γ → x ⦂ σ ∈ Γ → OkT 
-- if ∅ ⊢ e ⦂ IO ρ τ, then either (∃ v ρ' τ'. st ρ'≥ρ and ∅ ⊢ ⟦ v ⟧ IO ρ' τ') or (∃ v r τ'. st ` r≥:ρ ∅ ⊢ use r v ⦂ IO ρ τ')

-- IOroot : ∀ {e ρ τ}
--        → ∅ ⊢ e ⦂
-- OkT τ →  > τ → OkT τ  
oktsub : ∀ {s τ} → OkT τ → OkT (subT s τ)
oktsub {s} {τ ⇒ τ₁} (Ok⇒ okt okt₁) = Ok⇒ (oktsub okt) (oktsub okt₁)
oktsub {s} {IO x τ} (OkIO okt x₁) = OkIO (oktsub okt) x₁ 
oktsub {s} {□} okt = Ok□
oktsub {s} {τ × τ₁} (Ok× okt okt₁) = Ok× (oktsub okt) (oktsub okt₁)

oktstoτ : ∀ {σ τ} → OkTS σ → σ > τ → OkT τ
oktstoτ {σ} (OkTSZ {αs} {τ} okτ) (Inst s x₁ refl) with oktsub {s} okτ | TStype (VV αs τ) | extractVV≡ {αs} {τ}
... | oks | .τ | refl = oks

mustBeOk : ∀ {Γ e ρ τ} → OkC Γ → Γ ⊢ e ⦂ IO ρ τ → Ok ρ
absHelper : ∀ {Γ τ τ' e' e ρ}
          → OkC Γ
          → Γ ⊢ e' ⦂ τ
          → Γ ⊢ e ⦂ τ ⇒ IO ρ τ'
          → Ok ρ

absHelper okc ⊢e' (⊢` Z x₁) = {!!}
absHelper okc ⊢e' (⊢` (S x x₂) x₁) = {!!}
absHelper okc ⊢e' (⊢ƛ ⊢e) = mustBeOk (OkCS okc {!!}) ⊢e
absHelper okc ⊢e' (⊢· ⊢e ⊢e₁) = {!!}
absHelper okc ⊢e' (⊢lt ⊢e ⊢e₁) = {!!}
absHelper okc ⊢e' (⊢π₁ ⊢e) = {!!}
absHelper okc ⊢e' (⊢π₂ ⊢e) = {!!}

negasdf : ∀ {Γ e τ ρ} → ¬ (Γ ⊢ e ⦂ IO ρ τ → ¬ (Ok ρ))
negasdf ⊢e = {!!}

asdf : ∀ {Γ e τ ρ} → OkC Γ → Γ ⊢ e ⦂ IO ρ τ → OkT (IO ρ τ)
asdf (OkCS okc okts) (⊢` Z σ>τ) = oktstoτ okts σ>τ
asdf (OkCS okc okts) (⊢` (S x∈ x₁) σ>τ) = asdf okc (⊢` x∈ σ>τ)
-- asdf okc (⊢ƛ ⊢e) = let z = asdf (OkCS okc {!!}) ⊢e in {!!}
-- this can always be typed: (λ x . x) : IO wrong t → IO wrong τ
asdf okc (⊢· ⊢e ⊢e₁) = {!!} -- ⊢e can be (λ x . x) : IO wrong t → IO wrong t
asdf okc (⊢lt ⊢e ⊢e₁) = {!!}
asdf okc (⊢π₁ ⊢e) = {!!}
asdf okc (⊢π₂ ⊢e) = {!!}
asdf okc (⊢⟦⟧ ⊢e x) = {!!}
asdf okc (⊢>>= ⊢e ⊢e₁) = {!!}
asdf okc (⊢⋎ ⊢e ⊢e₁ x) = {!!}
asdf okc (⊢IOsub ⊢e x x₁) = {!!}
asdf okc (⊢use ⊢e) = {!!}

-- absHelper okc (⊢` x x₁) = let z = mustBeOk okc {!⊢` x x₁!} in {!!}
-- absHelper okc (⊢ƛ ⊢e) = mustBeOk (OkCS okc (OkTSZ {!!})) ⊢e
-- absHelper okc (⊢· ⊢e ⊢e₁) = {!!}
-- absHelper okc (⊢lt ⊢e ⊢e₁) = {!!}
-- absHelper okc (⊢π₁ ⊢e) = {!!}
-- absHelper okc (⊢π₂ ⊢e) = {!!}

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
mustBeOk okc (⊢IOsub ⊢e x ok) = ok
mustBeOk okc (⊢use ⊢e) = OkZ
