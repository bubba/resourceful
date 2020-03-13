module Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; ≢-sym)

open import Data.List using (List; _∷_; [_]; []; _++_; any)
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Any

open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)

open import Data.String.Properties using (≡-setoid)
import Data.List.Relation.Binary.Subset.Setoid as Subset
open module SubsetString = Subset ≡-setoid
import Data.List.Membership.Setoid as Membership
open module MembershipString = Membership ≡-setoid using (_∈_;_∉_; find)
open import Data.List.Membership.Setoid.Properties

open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Product
  using (proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩; _×_ to ⟨_×_⟩)

import Data.Sum using (_⊎_; inj₁; inj₂)

open import Resourceful

V¬-↝ : ∀ {e e'}
     → Value e
       -------
     → ¬ (e ↝ e')
V¬-↝ V-□ ()
V¬-↝ V-ƛ ()
V¬-↝ V-⟦⟧ ()
V¬-↝ (V-× v₁ v₂) (ξ-×₁ e↝e') = (V¬-↝ v₁) e↝e'
V¬-↝ (V-× v₁ v₂) (ξ-×₂ e↝e') = (V¬-↝ v₂) e↝e'

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

  C-× : ∀ {e₁ τ₁ e₂ τ₂}
      → ∅ ⊢ e₁ ⦂ τ₁
      → ∅ ⊢ e₂ ⦂ τ₂
        -------------------
      → Canonical (e₁ × e₂) ⦂ τ₁ × τ₂

  C-use : ∀ {e τ r ρ}
        → ` r ≥: ρ
        → ∅ ⊢ e ⦂ τ
          ----------------
        → Canonical use r e ⦂ IO ρ τ

  -- C-⋎ : ∀ {e₁ e₂ ρ₁ ρ₂ τ₁ τ₂}
  --     → ∅ ⊢ e₁ ⦂ IO ρ₁ τ₁
  --     → ∅ ⊢ e₂ ⦂ IO ρ₂ τ₂
  --     → ρ₁ ∩ ρ₂ =∅
  --       -------------------------------------------
  --     → Canonical (e₁ ⋎ e₁) ⦂ IO (ρ₁ ∪ ρ₂) (τ₁ × τ₂)


unwrap⟦⟧ : ∀ {Γ v ρ τ} → Γ ⊢ ⟦ v ⟧ ⦂ IO ρ τ → Γ ⊢ v ⦂ τ
unwrap⟦⟧ (⊢⟦⟧ ⊢v _) = ⊢v
unwrap⟦⟧ (⊢IOsub ⊢v _ _) = unwrap⟦⟧ ⊢v


-- readFile≡□ : ∀ {Γ ρ τ} → Γ ⊢ readFile ⦂ IO ρ τ → τ ≡ □
-- readFile≡□ (⊢IOsub ⊢rf _ _) = readFile≡□ ⊢rf
-- readFile≡□ ⊢readFile = refl

-- readNet≡□ : ∀ {Γ ρ τ} → Γ ⊢ readNet ⦂ IO ρ τ → τ ≡ □
-- readNet≡□ (⊢IOsub ⊢rf _ _) = readNet≡□ ⊢rf
-- readNet≡□ ⊢readNet = refl

canonical : ∀ {v τ}
          → ∅ ⊢ v ⦂ τ
          → Value v
            -----------
          → Canonical v ⦂ τ
canonical (⊢ƛ ⊢e) V-ƛ = C-ƛ ⊢e
canonical (⊢□) V-□ = C-□
canonical (⊢⟦⟧ ⊢e _) V-⟦⟧ = C-⟦⟧ ⊢e
canonical (⊢× ⊢e₁ ⊢e₂) (V-× _ _) = C-× ⊢e₁ ⊢e₂
-- canonical ⊢readFile V-readFile = C-readFile ≥:Refl
-- canonical ⊢readNet V-readNet = C-readNet ≥:Refl
canonical (⊢use ⊢e) V-use = C-use ≥:Refl ⊢e

canonical (⊢IOsub ⊢e x _) V-ƛ = ⊥-elim (f ⊢e)
  where
  f : ∀ {x e ρ τ} → ¬ (∅ ⊢ ƛ x ⇒ e ⦂ IO ρ τ)
  f (⊢IOsub ⊢e x _) = f ⊢e
canonical (⊢IOsub ⊢e x _) V-⟦⟧ = C-⟦⟧ (unwrap⟦⟧ ⊢e)
canonical (⊢IOsub ⊢e x _) V-□ = ⊥-elim (f ⊢e)
  where
  f : ∀ {ρ τ} → ¬ (∅ ⊢ □ ⦂ IO ρ τ)
  f (⊢IOsub ⊢e x _) = f ⊢e
canonical (⊢IOsub ⊢e x _) (V-× y y₁) = ⊥-elim (f ⊢e)
  where
  f : ∀ {e₁ e₂ ρ τ} → ¬ (∅ ⊢ e₁ × e₂ ⦂ IO ρ τ)
  f (⊢IOsub ⊢e x _) = f ⊢e

-- canonical (⊢IOsub ⊢e ρ≥:ρ' _) V-readFile with canonical ⊢e V-readFile
-- ... | C-readFile f≥:ρ = C-readFile (≥:-trans f≥:ρ ρ≥:ρ')
-- canonical (⊢IOsub ⊢e ρ≥:ρ' _) V-readNet with canonical ⊢e V-readNet
-- ... | C-readNet f≥:ρ = C-readNet (≥:-trans f≥:ρ ρ≥:ρ')
canonical (⊢IOsub ⊢e ρ≥:ρ' _) V-use with canonical ⊢e V-use
... | C-use r≥:ρ ⊢e' = C-use (≥:-trans r≥:ρ ρ≥:ρ') ⊢e'

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
progress (⊢⟦⟧ _ _) = done V-⟦⟧
progress (⊢>>= ⊢m ⊢f) with progress ⊢m
... | step m↝m' = step (ξ->>= m↝m')
... | done vm with canonical ⊢m vm
...   | C-⟦⟧ _ = step β->>=
-- ...   | C-readFile _ = step β-readFile
-- ...   | C-readNet _ = step β-readNet
...   | C-use _ _ = step β-use
progress ⊢□ = done V-□
progress (⊢lt ⊢e ⊢e') = step β-lt
progress (⊢× ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | step e₁↝e₁' | _ = step (ξ-×₁ e₁↝e₁')
... | done ve₁ | step e₂↝e₂' = step (ξ-×₂ e₂↝e₂')
... | done ve₁ | done ve₂ = done (V-× ve₁ ve₂)
progress (⊢π₁ ⊢e) with progress ⊢e
... | step e↝e' = step (ξ-π₁ e↝e')
... | done ve with canonical ⊢e ve
...   | C-× _ _ = step β-π₁
progress (⊢π₂ ⊢e) with progress ⊢e
... | step e↝e' = step (ξ-π₂ e↝e')
... | done ve with canonical ⊢e ve
...   | C-× _ _ = step β-π₂
-- progress ⊢readFile = done V-readFile
-- progress ⊢readNet = done V-readNet
progress (⊢use ⊢e) = done V-use
progress (⊢⋎ ⊢e₁ ⊢e₂ dist) = step β-⋎
progress (⊢IOsub ⊢e _ _) = progress ⊢e

contained  : ∀ { Γ x σ y σ' } → x ≢ y → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Γ , y ⦂ σ'
contained x≢y Z = S Z x≢y
contained x≢y (S x∈Γ x) = S (contained x x∈Γ) x≢y

ext : ∀ {Γ Δ}
    → (∀ {x τ} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ)
    → (∀ {x y τ τ'} → x ⦂ τ ∈ Γ , y ⦂ τ' → x ⦂ τ ∈ Δ , y ⦂ τ')
ext p Z = Z
ext p (S x∈Γ x≢y) = S (p x∈Γ) x≢y

freeVars⊆ : ∀ {Γ Δ} → (∀ {x σ} → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ) → FTVC Γ ⊆ FTVC Δ
freeVars⊆ {Γ , x ⦂ σ} ρ x∈ = {!!}

-- Δ could contain more freeVars? so close could have less free vars?
renameClose : ∀ {Γ Δ}
            → (∀ {x τ} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ)            
            → (∀ {τ τ' x e} → Γ , x ⦂ close Γ τ ⊢ e ⦂ τ' → Δ , x ⦂ close Δ τ ⊢ e ⦂ τ')
renameClose {Γ} {Δ} ρ {τ} ⊢e with freeVars⊆ ρ
... | Γ⊆Δ = {!!}

-- with VV (freeVars τ / freeVarsC Γ) τ | close Γ τ | freeVars≡ ρ
-- ... | zz | z | Γ⊆Δ = {!!}
--   where 

rename : ∀ {Γ Δ}
       → (∀ {x τ} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ)
       → (∀ {e τ} → Γ ⊢ e ⦂ τ → Δ ⊢ e ⦂ τ)
rename p (⊢` x⦂τ' τ'>τ) = ⊢` (p x⦂τ') τ'>τ
rename p (⊢ƛ Γ⊢e⦂τ) = ⊢ƛ (rename (ext p) Γ⊢e⦂τ)
rename p (⊢· Γ⊢e⦂τ Γ⊢e⦂τ₁) = ⊢· (rename p Γ⊢e⦂τ) (rename p Γ⊢e⦂τ₁)
rename p (⊢⟦⟧ ⊢e cl) = ⊢⟦⟧ (rename p ⊢e) cl
rename p (⊢>>= ⊢m ⊢f) = ⊢>>= (rename p ⊢m) (rename p ⊢f)
rename p ⊢□ = ⊢□
rename {Γ} {Δ} ρ (⊢lt Γ⊢e'⦂τ' Γ⊢e'⦂τ) = ⊢lt (rename ρ Γ⊢e'⦂τ') (renameClose ρ Γ⊢e'⦂τ)
rename ρ (⊢× ⊢e₁ ⊢e₂) = ⊢× (rename ρ ⊢e₁) (rename ρ ⊢e₂)
rename ρ (⊢π₁ ⊢e) = ⊢π₁ (rename ρ ⊢e)
rename ρ (⊢π₂ ⊢e) = ⊢π₂ (rename ρ ⊢e)
rename ρ (⊢use ⊢e) = ⊢use (rename ρ ⊢e)
rename ρ (⊢⋎ ⊢e₁ ⊢e₂ dist) = ⊢⋎ (rename ρ ⊢e₁) (rename ρ ⊢e₂) dist
rename ρ (⊢IOsub ⊢e ρ≥:ρ' ok) = ⊢IOsub (rename ρ ⊢e) ρ≥:ρ' ok

extend∈ : ∀ {Γ Δ}
          → (∀ {x σ} → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
          → (∀ {x σ y σ'} → x ⦂ σ ∈ Γ , y ⦂ σ' → x ⦂ σ ∈ Δ , y ⦂ σ')
extend∈ ρ Z = Z
extend∈ ρ (S x∈Γ,y x) = S (ρ x∈Γ,y) x   
        
    
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


extend : ∀ {Γ x σ e τ}
       → Γ ⊢ e ⦂ τ
       → x ∉ FV(e)
       → Γ , x ⦂ σ ⊢ e ⦂ τ
extend {x = x} (⊢` {x = y} x∈ σ>τ) x∉ with x ≟ y
... | yes refl = ⊥-elim (x∉ (here refl))
... | no x≢y = ⊢` (S x∈ (λ z → x≢y (sym z))) σ>τ
extend (⊢× ⊢e₁ ⊢e₂) x∉ with ∉-++⁻ x∉
... | ⟨ ∉e₁ , ∉e₂ ⟩ = ⊢× (extend ⊢e₁ ∉e₁) (extend ⊢e₂ ∉e₂)
extend (⊢π₁ ⊢e) x∉ = ⊢π₁ (extend ⊢e x∉)
extend (⊢π₂ ⊢e) x∉ = ⊢π₂ (extend ⊢e x∉)
extend {x = x} {e = e} (⊢ƛ {x = y} ⊢e) x∉ with x ≟ y
... | yes refl = ⊢ƛ (sneakIn ⊢e)
... | no x≢y = ⊢ƛ (swap x≢y (extend ⊢e (∉-/≢ x∉ x≢y)))
extend (⊢· ⊢e₁ ⊢e₂) x∉ with ∉-++⁻ x∉
... | ⟨ ∉e₁ , ∉e₂ ⟩ = ⊢· (extend ⊢e₁ ∉e₁) (extend ⊢e₂ ∉e₂)
extend {Γ} {x} {σ = σ} (⊢lt {τ' = τ'} {x = y} ⊢e ⊢e') x∉ with x ≟ y | ∉-++⁻ x∉ | close (Γ , y ⦂ σ) τ'
... | yes refl | ⟨ ∉e , ∉e' ⟩ | closeyσ = ⊢lt (extend ⊢e ∉e) (sneakIn {!let z = extend !})
... | no x≢y | ⟨ ∉e , ∉e' ⟩ | foo = ⊢lt (extend ⊢e ∉e) {!!}
extend (⊢⟦⟧ ⊢e cl) x∉ = ⊢⟦⟧ (extend ⊢e x∉) cl
extend {x = x} (⊢>>= {e = e} {e' = e'} ⊢e ⊢e') x∉ with ∉-++⁻ {x} {FV(e)} {FV(e')} x∉
... | ⟨ ∉e , ∉e' ⟩ = ⊢>>= (extend ⊢e ∉e) (extend ⊢e' ∉e')
extend ⊢□ x∉ = ⊢□
extend (⊢use ⊢e) x∉ = ⊢use (extend ⊢e x∉)
extend (⊢⋎ ⊢e₁ ⊢e₂ dist) x∉ with ∉-++⁻ x∉
... | ⟨ ∉e₁ , ∉e₂ ⟩ = ⊢⋎ (extend ⊢e₁ ∉e₁) (extend ⊢e₂ ∉e₂) dist
extend (⊢IOsub ⊢e ρ≥:ρ' ok) x∉ = ⊢IOsub (extend ⊢e x∉) ρ≥:ρ' ok

-- lemma 4.1
-- extra vars in the environment can be ignored
ignore : ∀ {Γ Δ e τ}
       → (∀ {x σ} → x ∈ FV(e) → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
       → Γ ⊢ e ⦂ τ
       → Δ ⊢ e ⦂ τ
ignore ρ (⊢` {x = x} x∈ σ>τ) = ⊢` (ρ (here refl) x∈) σ>τ
ignore ρ (⊢ƛ ⊢e) = ⊢ƛ (ignore (λ x∈FV x∈Γ → let z = extend∈ (ρ {!!}) in {!!}) ⊢e)
ignore ρ (⊢× ⊢e₁ ⊢e₂) = ⊢× {!!} {!!}
ignore ρ (⊢π₁ ⊢e) = {!!}
ignore ρ (⊢π₂ ⊢e) = {!!}
ignore ρ (⊢· ⊢e₁ ⊢e₂) = ⊢· (ignore {!!} {!!}) {!!}
ignore ρ (⊢lt ⊢e ⊢e₁) = ⊢lt {!!} {!!}
ignore ρ (⊢⟦⟧ ⊢e cl) = ⊢⟦⟧ (ignore ρ ⊢e) cl
ignore ρ (⊢>>= {e = e} {e' = e'} ⊢e ⊢e') = ⊢>>= (ignore {!!} ⊢e) {!!}
ignore ρ ⊢□ = ⊢□
ignore ρ (⊢use ⊢e) = ⊢use (ignore ρ ⊢e)
ignore ρ (⊢⋎ z z₁ x) = {!!}
ignore ρ (⊢IOsub z ρ≥:ρ' ok) = ⊢IOsub (ignore ρ z) ρ≥:ρ' ok


closeσ : ∀ {Γ Γ' x y σ σ' e} → ∀ (τ' τ)
       → Γ , x ⦂ close (Γ' , y ⦂ σ') τ' ⊢ e ⦂ τ
       → σ ≥ σ'
       → Γ , x ⦂ close (Γ' , y ⦂ σ) τ' ⊢ e ⦂ τ
closeσ {Γ} {Γ'} {x} {y} {σ} {σ'} {e} τ' τ ⊢e⦂τ' σ>σ' rewrite close> {Γ'} {y} {σ} {σ'} {τ'} σ>σ' = ⊢e⦂τ'

-- wright & felleisen lemma 4.6
gen : ∀ {Γ e x σ σ' τ} → Γ , x ⦂ σ' ⊢ e ⦂ τ
                       → σ ≥ σ'
                         ------------------
                       → Γ , x ⦂ σ ⊢ e ⦂ τ
gen (⊢` {x = y} Z σ'>τ) σ>σ' = ⊢` Z (>trans σ>σ' σ'>τ)
gen (⊢` {x = y} (S y⦂σ'∈Γ y≢x) σ'>τ) σ>σ' = ⊢` (S y⦂σ'∈Γ y≢x) σ'>τ
gen {x = y} (⊢ƛ {x = x} ⊢e) σ>σ' with x ≟ y
... | yes refl = let z = drop ⊢e in ⊢ƛ (sneakIn z)
... | no x≢y = let z = swap x≢y ⊢e
                   z1 = gen z σ>σ' in ⊢ƛ (swap (≢-sym x≢y) z1)
gen (⊢· ⊢e' ⊢e) σ>σ' = ⊢· (gen ⊢e' σ>σ') (gen ⊢e σ>σ')

gen {Γ} {x = y} {σ = σ} {σ' = σ'} (⊢lt {Γ , y ⦂ σ'} {τ = τ} {τ' = τ'} {x = x} ⊢e'⦂τ' ⊢e⦂τ) σ>σ' with x ≟ y
... | yes refl = ⊢lt (gen ⊢e'⦂τ' σ>σ') (sneakIn (closeσ {Γ} {Γ} {x} {y} {σ} {σ'} τ' τ (drop ⊢e⦂τ) σ>σ'))
... | no x≢y =
      let ⊢e⦂τswp = swap x≢y ⊢e⦂τ
          ⊢e⦂τswp' = gen ⊢e⦂τswp σ>σ'
          ⊢e⦂τswp'' = swap (≢-sym x≢y) ⊢e⦂τswp'
          z = closeσ {Γ , y ⦂ σ} {Γ} {x} {y} τ' τ ⊢e⦂τswp'' σ>σ'
          in ⊢lt (gen ⊢e'⦂τ' σ>σ') z

gen (⊢× ⊢e₁ ⊢e₂) σ>σ' = ⊢× (gen ⊢e₁ σ>σ') (gen ⊢e₂ σ>σ')
gen (⊢π₁ ⊢e) σ>σ' = ⊢π₁ (gen ⊢e σ>σ')
gen (⊢π₂ ⊢e) σ>σ' = ⊢π₂ (gen ⊢e σ>σ')
gen (⊢⟦⟧ x cl) σ>σ' = ⊢⟦⟧ (gen x σ>σ') cl
gen (⊢>>= x x₁) σ>σ' = ⊢>>= (gen x σ>σ') (gen x₁ σ>σ')
gen ⊢□ σ>σ' = ⊢□
gen (⊢use ⊢e) σ>σ' = ⊢use (gen ⊢e σ>σ')
gen (⊢⋎ ⊢e₁ ⊢e₂ dist) σ>σ' = ⊢⋎ (gen ⊢e₁ σ>σ') (gen ⊢e₂ σ>σ') dist
gen (⊢IOsub ⊢e ρ≥:ρ' ok) σ>σ' = ⊢IOsub (gen ⊢e σ>σ') ρ≥:ρ' ok

Γcong : ∀ {Γ x e τ σ σ'} → Γ , x ⦂ σ ⊢ e ⦂ τ → σ ≡ σ' → Γ , x ⦂ σ' ⊢ e ⦂ τ
Γcong Γ refl = Γ

Γ⊢cong : ∀ {Γ e τ τ'}
       → τ ≡ τ'
       → Γ ⊢ e ⦂ τ
       → Γ ⊢ e ⦂ τ'
Γ⊢cong refl ⊢e = ⊢e


sub> : ∀ {s σ τ} → σ > τ → sub s σ > subT s τ
sub> {s} {σ} (General s' x y) = General (s' ∘ˢ s) {!!} {!!}

-- tofte lemma 2.6
-- lemma26 : ∀ {s σ σ' τ} → σ > τ → σ ⇒ s ⇒ σ' → σ' > subT s τ)

-- _ : (s : Substitution) → x ⦂ close Γ τ' → 

-- wright and felleisen lemma 4.5,
-- tofte lemma 2.7
subContextTyping : ∀ {Γ e τ}
                   → Γ ⊢ e ⦂ τ
                   → (s : Substitution)
                   → subC s Γ ⊢ e ⦂ subT s τ
subContextTyping {Γ} (⊢` {x = x} {σ} x∈Γ σ>τ) s = let sσ = sub s σ in ⊢` (f x∈Γ) (sub> σ>τ)
  where
  f : ∀ {x σ Γ s} → x ⦂ σ ∈ Γ → x ⦂ sub s σ ∈ subC s Γ
  f Z = Z
  f (S x∈ x≢y) = S (f x∈) x≢y

subContextTyping {Γ} {e} {τ} (⊢ƛ {x = x} {τ' = τ'} {e = e'} ⊢e) s = ⊢ƛ (let z = (subContextTyping ⊢e s) in f z)
  where
  f : ∀ {e Γ s τ' τ x} → subC s Γ , x ⦂ sub s (` τ') ⊢ e ⦂ subT s τ → subC s Γ , x ⦂ ` subT s τ' ⊢ e ⦂ subT s τ
  f {s = s} {τ' = τ'}  ⊢e rewrite subT≡sub {τ'} s = ⊢e

  
subContextTyping (⊢· ⊢e₁ ⊢e₂) s = ⊢· (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)

subContextTyping (⊢lt ⊢e ⊢e') s = ⊢lt (subContextTyping ⊢e s) (f' (subContextTyping ⊢e' s))
  where
  -- equation 2.26 in tofte
  g : ∀ {Γ s τ} → sub s (close Γ τ) ≡ close (subC s Γ) (subT s τ)
  g {Γ} {SZ} {τ} rewrite subCSZ {Γ} | subTSZ {τ} = refl
  g {Γ} {SS id τ' si} {τ} =
    begin
      sub (SS id τ' si) (close Γ τ)
    ≡⟨⟩
      sub (SS id τ' si) (VV (FTVT τ / FTVC Γ) τ)
    ≡⟨⟩
      {!!}
      
  f : ∀ {Γ s x τ} → subC s (Γ , x ⦂ close Γ τ) ≡ subC s Γ , x ⦂ close (subC s Γ) (subT s τ)
  f {Γ} {s} {x} {τ} rewrite g {Γ} {s} {τ} = refl
  f' : ∀ {Γ s x τ' e τ}
     → subC s (Γ , x ⦂ close Γ τ') ⊢ e ⦂ τ
     → subC s Γ , x ⦂ close (subC s Γ) (subT s τ') ⊢ e ⦂ τ
  f' {Γ} {s} {x} {τ'} {e} {τ} ⊢e rewrite (cong (λ z → z ⊢ e ⦂ τ) (f {Γ} {s} {x} {τ'})) = ⊢e

subContextTyping (⊢× ⊢e₁ ⊢e₂) s = ⊢× (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping (⊢π₁ ⊢e) s = ⊢π₁ (subContextTyping ⊢e s)
subContextTyping (⊢π₂ ⊢e) s = ⊢π₂ (subContextTyping ⊢e s)
subContextTyping (⊢⟦⟧ ⊢e cl) s = ⊢⟦⟧ (subContextTyping ⊢e s) cl
subContextTyping (⊢>>= ⊢e₁ ⊢e₂) s = ⊢>>= (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping ⊢□ s = ⊢□
subContextTyping (⊢use ⊢e) s = ⊢use (subContextTyping ⊢e s)
subContextTyping (⊢⋎ ⊢e₁ ⊢e₂ dist) s = ⊢⋎ (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s) dist
subContextTyping (⊢IOsub ⊢e ρ≥:ρ' ok) s = ⊢IOsub (subContextTyping ⊢e s) ρ≥:ρ' ok


-- -- s must cover all of αs
-- fooo : ∀ {τ τ' e Γ}
--      → (s : Substitution)
--      → subT s τ ≡ τ'
--      → Γ ⊢ e ⦂ subT s τ
--      → Γ ⊢ e ⦂ τ'
-- fooo s refl ⊢e = ⊢e

-- data NotInContext : List Id → Context → Set where
--   NotHere : ∀ {Γ} → NotInContext [] Γ
--   NotThere : ∀ {Γ α αs}
--          → α ∉ freeVarsC Γ
--          → NotInContext αs Γ
--          → NotInContext (α ∷ αs) Γ

-- notIn∅ : ∀ {αs : List Id} → NotInContext αs ∅
-- notIn∅ {[]} = NotHere
-- notIn∅ {x ∷ αs} = NotThere (λ ()) notIn∅

-- notInExtend : ∀ {Γ αs x σ} → NotInContext αs Γ → Disjoint αs (freeVarsTS σ) → NotInContext αs (Γ , x ⦂ σ)
-- notInExtend NotHere _ = NotHere
-- notInExtend (NotThere {α = α} ∉σ notin) (DisThere ∉Γ p) = NotThere (∉-++⁺ˡ {α} ∉σ ∉Γ) (notInExtend notin p)

-- absHelper : ∀ {Γ z e x σ} → z ∈ FV e → Γ ⦅ z ⦆ ≡ Γ , x' ⦂ σ ⦅ z ⦆

-- chooses a substitution such that FTV Γ ∩ subRegion s ∩ αs ≡ ∅
absSubChoose : ∀ {Γ x' x αs τ₁ τ e₁ τ₂}
             → Γ , x' ⦂ τ₁ , x ⦂ VV αs τ ⊢ e₁ ⦂ τ₂
             → ∃[ s ] ⟨ Disjoint (FTVC Γ) αs × ⟨ (Disjoint (subRegion (BJS.to s)) αs) × (Disjoint (subRegion (BJS.to s)) (FTVC Γ)) ⟩ ⟩
absSubChoose {αs = αs} ⊢e with freshTypeVars αs
... | ⟨ βs , djαβ ⟩ = {!!}

subC∅ : (s : Substitution) → subC s ∅ ≡ ∅
subC∅ _ = refl

FTVC∉FTV : ∀ {Γ x σ α} → α ∉ FTVC (Γ , x ⦂ σ) → α ∉ FTV σ
FTVC∉FTV {Γ} {x} {σ} ∉Γ with FTV σ |  FTVC (Γ , x ⦂ σ)
... | z | y = {!!}

sub∉FTVC : ∀ {Γ α τ s} → α ∉ FTVC Γ → subC (SS α τ s) Γ ≡ subC s Γ
sub∉FTVC {∅} x∉ = refl
sub∉FTVC {Γ , x ⦂ σ} {α} {τ} {s} x∉ = {!!}
  
disjointSub : ∀ {Γ s} → Disjoint (subDomain s) (FTVC Γ) → subC s Γ ≡ Γ
disjointSub {Γ} {SZ} DisHere = subCSZ
disjointSub {Γ} {SS α σ s} (DisThere x dj) rewrite sub∉FTVC {Γ} {α} {σ} {s} x = disjointSub dj

-- wright & felleisen lemma 4.4
subst : ∀ {Γ x e e' αs τ τ'}
      → Γ ⊢ e ⦂ τ
      → Γ , x ⦂ VV αs τ ⊢ e' ⦂ τ'
      → Disjoint αs (FTVC Γ)
        -------------------
      → Γ ⊢ e' [ x := e ] ⦂ τ'
subst {Γ} {x = y} {e} {αs = αs} {τ = τ} {τ' = τ'} ⊢e (⊢` {x = x} Z (General s ds≡αs refl)) ∉Γ
  rewrite TSvars≡ {αs} {τ} with ds≡αs | x ≟ y
... | refl | yes refl = prf (prt2 prt1)
    where prt1 : subC s Γ ⊢ e ⦂ subT s τ
          prt1 = subContextTyping ⊢e s
          prt2 : subC s Γ ⊢ e ⦂ subT s τ → subC s Γ ⊢ e ⦂ τ'
          prt2 ⊢e rewrite extractVV≡ {αs} {τ} = ⊢e
          SΓ≡Γ : subC s Γ ≡ Γ
          SΓ≡Γ = disjointSub ∉Γ
          prf : subC s Γ ⊢ e ⦂ τ' → Γ ⊢ e ⦂ τ'
          prf ⊢e rewrite SΓ≡Γ = ⊢e
... | refl | no x≢y = ⊥-elim (x≢y refl)

subst {x = y} ⊢e (⊢` {x = x} (S x∈ x≢y) τ''>τ) _ with x ≟ y
...  | yes x≡y = ⊥-elim (x≢y x≡y)
...  | no x≢y' = ⊢` x∈ τ''>τ

-- type vars renamed to match wright & felleisen
subst {Γ} {x = x} {e = v} {e' = e} {αs} {τ} {τ'} ⊢e (⊢ƛ {x = x'} {τ' = τ₁} {τ = τ₂} {e = e₁} ⊢e') p with x' ≟ x
...  | yes refl = ⊢ƛ (drop ⊢e')
...  | no x'≢x = ⊢ƛ prf
     where prf : Γ , x' ⦂ ` τ₁ ⊢ e₁ [ x := v ] ⦂ τ₂
           prf with absSubChoose (swap x'≢x ⊢e')
           prf | ⟨ bjs , ⟨ djΓαs , ⟨ djsαs , djsΓ ⟩ ⟩ ⟩ =
             let swp : Γ , x' ⦂ ` τ₁ , x ⦂ VV αs τ ⊢ e₁ ⦂ τ₂
                 swp = swap x'≢x ⊢e'
                 s = BJS.to bjs
                 s⁻¹ = BJS.from bjs
                 prt2 : Γ , x' ⦂ sub s (` τ₁) , x ⦂ VV αs τ ⊢ e₁ ⦂ subT s τ₂
                 prt2 = {!!} -- subContextTyping ? ?
                 prt3 : Γ , x' ⦂ sub s (` τ₁) ⊢ v ⦂ τ
                 prt3 = ignore {!!} ⊢e
                 prt4 : Disjoint αs (FTVC (Γ , x' ⦂ sub s (` τ₁)))
                 prt4 = {!!}
                 prt5 : Γ , x' ⦂ sub s (` τ₁) ⊢ e₁ [ x := v ] ⦂ subT s τ₂
                 prt5 = subst {Γ , x' ⦂ sub s (` τ₁)} prt3 prt2 prt4
                 prt6 : subC s⁻¹ (Γ , x' ⦂ sub s (` τ₁)) ⊢ e₁ [ x := v ] ⦂ subT s⁻¹ (subT s τ₂)
                 prt6 = subContextTyping prt5 (BJS.from bjs)
                 in roundtripSub bjs prt6

-- variables renamed to match wright & felleisen
subst {x = y} ⊢v (⊢lt {x = x} ⊢e' ⊢e'') p with x ≟ y
... | yes refl = ⊢lt (subst ⊢v ⊢e' p) {!!}
... | no x≢y = ⊢lt (subst ⊢v ⊢e' p)
                   (let swp = (swap x≢y ⊢e'')                        
                        in {!!})
                 
subst {x = y} ⊢e (⊢· e e') p = ⊢· (subst ⊢e e p) (subst ⊢e e' p)
subst {x = y} ⊢e (⊢× ⊢e₁ ⊢e₂) p = ⊢× (subst ⊢e ⊢e₁ p) (subst ⊢e ⊢e₂ p)
subst {x = y} ⊢e (⊢π₁ ⊢e') p = ⊢π₁ (subst ⊢e ⊢e' p)
subst {x = y} ⊢e (⊢π₂ ⊢e') p = ⊢π₂ (subst ⊢e ⊢e' p)
subst {x = y} ⊢e ⊢□ _ = ⊢□
subst {x = y} ⊢e (⊢use ⊢e') p = ⊢use (subst ⊢e ⊢e' p)
subst {x = y} ⊢e (⊢⟦⟧ ⊢e' cl) p = ⊢⟦⟧ (subst ⊢e ⊢e' p) cl
subst {x = y} ⊢e (⊢>>= ⊢m ⊢f) p = ⊢>>= (subst ⊢e ⊢m p) (subst ⊢e ⊢f p)
subst {x = y} ⊢e (⊢⋎ ⊢e₁ ⊢e₂ dist) p = ⊢⋎ (subst ⊢e ⊢e₁ p) (subst ⊢e ⊢e₂ p) dist
subst {x = y} ⊢e (⊢IOsub ⊢e' ρ≥:ρ' ok) p = ⊢IOsub (subst ⊢e ⊢e' p) ρ≥:ρ' ok

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
oktstoτ {σ} (OkTSZ {αs} {τ} okτ) (General s x₁ refl) with oktsub {s} okτ | TStype (VV αs τ) | extractVV≡ {αs} {τ}
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

preservation : ∀ {e e' τ}
             → ∅ ⊢ e ⦂ τ
             → e ↝ e'
               ----------
             → ∅ ⊢ e' ⦂ τ
preservation (⊢· ⊢e ⊢e') (ξ-·₁ e↝e') = ⊢· (preservation ⊢e e↝e') ⊢e'
preservation (⊢· ⊢e ⊢e') (ξ-·₂ e↝e') = ⊢· ⊢e (preservation ⊢e' e↝e')
preservation (⊢· (⊢ƛ ⊢e) ⊢e') (β-ƛ _) = subst ⊢e' ⊢e DisHere
preservation (⊢>>= ⊢m ⊢f) (ξ->>= m↝m') = ⊢>>= (preservation ⊢m m↝m') ⊢f
preservation (⊢>>= (⊢⟦⟧ ⊢e cl) ⊢f) β->>= = ⊢· ⊢f ⊢e
preservation (⊢>>= (⊢IOsub ⊢e ρ≥:ρ' ok) ⊢e') β->>= = ⊢· ⊢e' (unwrap⟦⟧ ⊢e)

preservation (⊢lt {τ' = τ'} ⊢e' ⊢e) β-lt rewrite toVVClose τ' = subst ⊢e' ⊢e disjoint-[]

-- product types
preservation (⊢× ⊢e₁ ⊢e₂) (ξ-×₁ e₁↝e₁') = ⊢× (preservation ⊢e₁ e₁↝e₁') ⊢e₂
preservation (⊢× ⊢e₁ ⊢e₂) (ξ-×₂ e₂↝e₂') = ⊢× ⊢e₁ (preservation ⊢e₂ e₂↝e₂')
preservation (⊢π₁ ⊢e) (ξ-π₁ e↝e') = ⊢π₁ (preservation ⊢e e↝e')
preservation (⊢π₁ (⊢× ⊢e₁ ⊢e₂)) β-π₁ = ⊢e₁
preservation (⊢π₂ ⊢e) (ξ-π₂ e↝e') = ⊢π₂ (preservation ⊢e e↝e')
preservation (⊢π₂ (⊢× ⊢e₁ ⊢e₂)) β-π₂ = ⊢e₂

preservation (⊢IOsub ⊢e ρ≥:ρ' ok) e↝e' = ⊢IOsub (preservation ⊢e e↝e') ρ≥:ρ' ok

-- preservation (⊢⋎ ⊢e₁ ⊢e₂ dist) (ξ-⋎₁ e₁↝e₁') = ⊢⋎ (preservation ⊢e₁ e₁↝e₁') ⊢e₂ dist
-- preservation (⊢⋎ ⊢e₁ ⊢e₂ dist) (ξ-⋎₂ e₂↝e₂') = ⊢⋎ ⊢e₁ (preservation ⊢e₂ e₂↝e₂') dist
preservation (⊢⋎ ⊢e₁ ⊢e₂ ok) β-⋎ =
  let ⊢`v = ⊢` (S Z (λ ())) >self
      ⊢`w = ⊢` Z >self
      ⊢>>=inner = ⊢>>= (⊢IOsub (weaken ⊢e₂) (≥:∪₁ ≥:Refl) ok) (⊢ƛ (⊢⟦⟧ (⊢× ⊢`v ⊢`w) ok))
  in ⊢>>= (⊢IOsub ⊢e₁ (≥:∪₂ ≥:Refl) ok) (⊢ƛ ⊢>>=inner)

-- preservation (⊢>>= ⊢rf ⊢e) β-readFile rewrite readFile≡□ ⊢rf = ⊢· ⊢e ⊢□
-- preservation (⊢>>= ⊢rn ⊢e) β-readNet rewrite readNet≡□ ⊢rn = ⊢· ⊢e ⊢□
preservation (⊢>>= ⊢u ⊢e') β-use = ⊢· ⊢e' (f ⊢u)
  where f : ∀ {Γ r e ρ τ} → Γ ⊢ use r e ⦂ IO ρ τ → Γ ⊢ e ⦂ τ
        f (⊢use ⊢e) = ⊢e
        f (⊢IOsub ⊢e _ _) = f ⊢e

noConcurrentAccess : ∀ {Γ e₁ e₂ ρ τ} → Γ ⊢ e₁ ⋎ e₂ ⦂ IO ρ τ → Ok ρ
noConcurrentAccess (⊢⋎ ⊢e₁ ⊢e₂ ok) = ok
noConcurrentAccess (⊢IOsub ⊢e x ok) = ok
