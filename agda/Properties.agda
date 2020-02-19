module Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; ≢-sym)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import Resourceful

V¬-↝ : ∀ {e e'}
     → Value e
       -------
     → ¬ (e ↝ e')
V¬-↝ V-□ ()
V¬-↝ V-ƛ ()
V¬-↝ V-⟦⟧ ()

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x e τ τ'}
      → ∅ , x ⦂ ` τ' ⊢ e ⦂ τ
        ------------------
      → Canonical (ƛ x ⇒ e) ⦂ (τ' ⇒ τ)

  C-□ : Canonical □ ⦂ □

  C-⟦⟧ : ∀ {e τ σ}
       → ∅ ⊢ e ⦂ τ
         ----------------------
       → Canonical ⟦ e ⟧ ⦂ IO σ τ

canonical : ∀ {v τ}
          → ∅ ⊢ v ⦂ τ
          → Value v
            -----------
          → Canonical v ⦂ τ
canonical (⊢ƛ ⊢e) V-ƛ = C-ƛ ⊢e
canonical (⊢□) V-□ = C-□
canonical (⊢⟦⟧ ⊢e) V-⟦⟧ = C-⟦⟧ ⊢e

data Progress (e : Term) : Set where
  step : ∀ {e'}
       → e ↝ e'
         ------
       → Progress e
  done : Value e
         ----------
       → Progress e


progress : ∀ {e τ} → ∅ ⊢ e ⦂ τ → Progress e
progress (⊢ƛ ⊢e) = done V-ƛ
progress (⊢· ⊢e₁ ⊢e₂) with progress ⊢e₁
... | step e₁↝e₁' = step (ξ-·₁ e₁↝e₁')
... | done ve₁ with progress ⊢e₂
...   | step e₂↝e₂' = step (ξ-·₂ e₂↝e₂')
...   | done ve₂ with canonical ⊢e₁ ve₁
...     | C-ƛ x = step (β-ƛ  ve₂)
progress (⊢⟦⟧ x) = done V-⟦⟧
progress (⊢>>= ⊢m ⊢f) with progress ⊢m
... | step m↝m' = step (ξ->>= m↝m')
... | done vm with canonical ⊢m vm
...   | C-⟦⟧ _ = step β->>=
progress ⊢□ = done V-□
progress (⊢lt ⊢e₁ ⊢e₂) = step β-lt

ext : ∀ {Γ Δ}
    → (∀ {x τ} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ)
    → (∀ {x y τ τ'} → x ⦂ τ ∈ Γ , y ⦂ τ' → x ⦂ τ ∈ Δ , y ⦂ τ')
ext p Z = Z
ext p (S x∈Γ x≢y) = S (p x∈Γ) x≢y

renameClose : ∀ {Γ Δ}
            → (∀ {x τ} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ)
            → (∀ {τ} → close Γ τ ≡ close Δ τ)
renameClose p = {!!} 

rename : ∀ {Γ Δ}
       → (∀ {x τ} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ)
       → (∀ {e τ} → Γ ⊢ e ⦂ τ → Δ ⊢ e ⦂ τ)
rename p (⊢` x⦂τ' τ'>τ) = ⊢` (p x⦂τ') τ'>τ
rename p (⊢ƛ Γ⊢e⦂τ) = ⊢ƛ (rename (ext p) Γ⊢e⦂τ)
rename p (⊢· Γ⊢e⦂τ Γ⊢e⦂τ₁) = ⊢· (rename p Γ⊢e⦂τ) (rename p Γ⊢e⦂τ₁)
rename p (⊢⟦⟧ ⊢e) = ⊢⟦⟧ (rename p ⊢e)
rename p (⊢>>= ⊢m ⊢f) = ⊢>>= (rename p ⊢m) (rename p ⊢f)
rename p ⊢□ = ⊢□
rename p (⊢lt Γ⊢e'⦂τ' Γ⊢e'⦂τ) = ⊢lt (rename p Γ⊢e'⦂τ') {!!}
    
weaken : ∀ {Γ e τ} → ∅ ⊢ e ⦂ τ → Γ ⊢ e ⦂ τ
weaken = rename f
  where f : ∀ {x τ Γ} → x ⦂ τ ∈ ∅ → x ⦂ τ ∈ Γ
        f ()

drop : ∀ {Γ x e τ₁ τ₂ τ₃}
     → Γ , x ⦂ τ₁ , x ⦂ τ₂ ⊢ e ⦂ τ₃
     → Γ , x ⦂ τ₂ ⊢ e ⦂ τ₃
drop {Γ} {x} {e} {τ₁} {τ₂} {τ₃} ⊢e = rename ρ ⊢e
  where ρ : ∀ {z τ₃}
          → z ⦂ τ₃ ∈ Γ , x ⦂ τ₁ , x ⦂ τ₂
          -----------------------------
          → z ⦂ τ₃ ∈ Γ , x ⦂ τ₂
        ρ Z = Z
        ρ (S Z x≢x) = ⊥-elim (x≢x refl)
        ρ (S (S z∈ _) z≢x) = S z∈ z≢x

sneakIn : ∀ {Γ x e σ σ' τ}
        → Γ , x ⦂ σ ⊢ e ⦂ τ
        → Γ , x ⦂ σ' , x ⦂ σ ⊢ e ⦂ τ
sneakIn {Γ} {x} {e} {σ} {σ'} {τ} ⊢e = rename ρ ⊢e
  where ρ : ∀ {z σ''} → z ⦂ σ'' ∈ Γ , x ⦂ σ
                      → z ⦂ σ'' ∈ Γ , x ⦂ σ' , x ⦂ σ
        ρ Z = Z
        ρ (S s z≢x) = S (S s z≢x) z≢x

swap : ∀ {Γ x y e a b c}
     → x ≢ y
     → Γ , y ⦂ b , x ⦂ a ⊢ e ⦂ c
       -------------------------
     → Γ , x ⦂ a , y ⦂ b ⊢ e ⦂ c
swap {Γ} {x} {y} {e} {a} {b} x≢y ⊢e = rename ρ ⊢e
  where ρ : ∀ {z τ}
          → z ⦂ τ ∈ Γ , y ⦂ b , x ⦂ a
          → z ⦂ τ ∈ Γ , x ⦂ a , y ⦂ b
        ρ Z = S Z x≢y
        ρ (S Z y≠x) = Z
        ρ (S (S x∈ z≢y) z≢x) = S (S x∈ z≢x) z≢y


splitAbs : ∀ {τ₁ τ₂ τ} → ` (τ₁ ⇒ τ₂) > τ → ∃[ τ₁' ] (∃[ τ₂' ] (τ ≡ ` (τ₁' ⇒ τ₂')))
splitAbs {τ₁} {τ₂} (General SZ refl) = ⟨ τ₁ , ⟨ τ₂ , refl ⟩ ⟩
splitAbs {τ₁} (General s@(SS x x₁ si) refl) = {!!}

splitAbsGeneralL : ∀ {τ₁ τ₂ τ} → ` (τ₁ ⇒ τ₂) > τ → ` τ₁ > τ
splitAbsGeneralL τ'>τ with splitAbs τ'>τ
splitAbsGeneralL (General s refl) | ⟨ τ₁' , ⟨ τ₂' , _ ⟩ ⟩ = {!!}

-- if σ' > σ then either σ' ≡ σ or σ' is of the form ∀ α . σ

subOnType : ∀ {τ} → (s : Substitution) → sub s (` τ) ≡ ` τ
subOnType SZ = refl
subOnType (SS _ _ s) = subOnType s

type>Eq : ∀ {τ σ} → ` τ > σ → σ ≡ ` τ
type>Eq (General s refl) = subOnType s

-- asdf5 : ∀ {σ τ} → (s : Substitution) → sub s (` (IO σ τ)) → sub s (` τ)
-- asdf5 SZ = {!!}
-- asdf5 (SS x x₁ s) = {!!}

splitIO : ∀ {σ τ' τ} → ` (IO σ τ') > τ → ` τ' > τ
splitIO x rewrite sym (type>Eq x) = {! !}

inst : ∀ {Γ e x σ σ' τ} → Γ , x ⦂ σ' ⊢ e ⦂ τ
                        → σ > σ'
                          ------------------
                        → Γ , x ⦂ σ ⊢ e ⦂ τ
inst {Γ} {e} {x = y} {σ} {σ'} {τ} (⊢` {x = x} x⦂τ∈Γ σ'>τ) σ>σ' with x ≟ y
... | yes refl = {!!}
... | no s = {!!}
inst {x = y} (⊢ƛ {x = x} ⊢e) σ>σ' with x ≟ y
... | yes refl = let z = drop ⊢e in ⊢ƛ (sneakIn z)
... | no x≢y = let z = swap x≢y ⊢e
                   z1 = inst z σ>σ' in ⊢ƛ (swap (≢-sym x≢y) z1)
inst (⊢· x x₁) σ'>σ = {!!}
inst (⊢lt x x₁) σ'>σ = {!!}
inst (⊢⟦⟧ x) σ'>σ = {!!}
inst (⊢>>= x x₁) σ'>σ = {!!}
inst ⊢□ σ'>σ = {!!}
-- inst (⊢` x⦂τ'∈Γ τ'>τ'') τ''>τ = ⊢` x⦂τ'∈Γ (>trans τ'>τ'' τ''>τ)
-- inst {Γ} {.(ƛ _ ⇒ _)} (⊢ƛ Γ⊢) y@(General s refl) = {!!}
-- inst (⊢· x x₁) y = {!!}
-- inst (⊢lt x x₁) y = {!!}
-- inst (⊢⟦⟧ x) y = {!!}
-- inst (⊢>>= x x₁) y = {!!}
-- inst ⊢□ (General SZ refl) = ⊢□
-- inst ⊢□ (General (SS _ _ s) x) = inst ⊢□ (General s x)

subst : ∀ {Γ x e e' τ τ'}
      → ∅ ⊢ e ⦂ τ
      → Γ , x ⦂ ` τ ⊢ e' ⦂ τ'
        -------------------
      → Γ ⊢ e' [ x := e ] ⦂ τ'
subst {x = y} ⊢e (⊢` {x = x} Z τ''>τ) with x ≟ y
...  | yes _ = f (weaken ⊢e)
  where f : ∀ {Γ e τ τ'} → Γ ⊢ e ⦂ τ → Γ ⊢ e ⦂ τ'
        f x = {!!}
...  | no x≢y = ⊥-elim (x≢y refl)
subst {x = y} ⊢e (⊢` {x = x} (S x∈ x≢y) τ''>τ) with x ≟ y
...  | yes x≡y = ⊥-elim (x≢y x≡y)
...  | no x≢y' = ⊢` x∈ τ''>τ
subst {x = y} ⊢e (⊢ƛ {x = x} ⊢e') with x ≟ y
...  | yes refl = ⊢ƛ (drop ⊢e')
...  | no x≢y = ⊢ƛ (subst ⊢e (swap x≢y ⊢e'))
subst {x = y} ⊢e (⊢· e e') = ⊢· (subst ⊢e e) (subst ⊢e e')
subst {x = y} ⊢e ⊢□ = ⊢□
subst {x = y} ⊢e (⊢⟦⟧ ⊢e') = ⊢⟦⟧ (subst ⊢e ⊢e')
subst {x = y} ⊢e (⊢>>= ⊢m ⊢f) = ⊢>>= (subst ⊢e ⊢m) (subst ⊢e ⊢f)
subst {x = y} ⊢e (⊢lt x x₁) = {!!}

preservation : ∀ {e e' τ}
             → ∅ ⊢ e ⦂ τ
             → e ↝ e'
               ----------
             → ∅ ⊢ e' ⦂ τ
preservation (⊢· ⊢e ⊢e') (ξ-·₁ e↝e') = ⊢· (preservation ⊢e e↝e') ⊢e'
preservation (⊢· ⊢e ⊢e') (ξ-·₂ e↝e') = ⊢· ⊢e (preservation ⊢e' e↝e')
preservation (⊢· (⊢ƛ ⊢e) ⊢e') (β-ƛ x) = subst ⊢e' ⊢e
preservation (⊢>>= ⊢m ⊢f) (ξ->>= m↝m') = ⊢>>= (preservation ⊢m m↝m') ⊢f
preservation (⊢>>= (⊢⟦⟧ ⊢e) ⊢f) β->>= = ⊢· ⊢f ⊢e
