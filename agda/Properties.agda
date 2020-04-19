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

open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

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
unwrap⟦⟧ (⊢sub ⊢v _ _) = unwrap⟦⟧ ⊢v


-- readFile≡□ : ∀ {Γ ρ τ} → Γ ⊢ readFile ⦂ IO ρ τ → τ ≡ □
-- readFile≡□ (⊢sub ⊢rf _ _) = readFile≡□ ⊢rf
-- readFile≡□ ⊢readFile = refl

-- readNet≡□ : ∀ {Γ ρ τ} → Γ ⊢ readNet ⦂ IO ρ τ → τ ≡ □
-- readNet≡□ (⊢sub ⊢rf _ _) = readNet≡□ ⊢rf
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

canonical (⊢sub ⊢e x _) V-ƛ = ⊥-elim (f ⊢e)
  where
  f : ∀ {x e ρ τ} → ¬ (∅ ⊢ ƛ x ⇒ e ⦂ IO ρ τ)
  f (⊢sub ⊢e x _) = f ⊢e
canonical (⊢sub ⊢e x _) V-⟦⟧ = C-⟦⟧ (unwrap⟦⟧ ⊢e)
canonical (⊢sub ⊢e x _) V-□ = ⊥-elim (f ⊢e)
  where
  f : ∀ {ρ τ} → ¬ (∅ ⊢ □ ⦂ IO ρ τ)
  f (⊢sub ⊢e x _) = f ⊢e
canonical (⊢sub ⊢e x _) (V-× y y₁) = ⊥-elim (f ⊢e)
  where
  f : ∀ {e₁ e₂ ρ τ} → ¬ (∅ ⊢ e₁ × e₂ ⦂ IO ρ τ)
  f (⊢sub ⊢e x _) = f ⊢e

-- canonical (⊢sub ⊢e ρ≥:ρ' _) V-readFile with canonical ⊢e V-readFile
-- ... | C-readFile f≥:ρ = C-readFile (≥:-trans f≥:ρ ρ≥:ρ')
-- canonical (⊢sub ⊢e ρ≥:ρ' _) V-readNet with canonical ⊢e V-readNet
-- ... | C-readNet f≥:ρ = C-readNet (≥:-trans f≥:ρ ρ≥:ρ')
canonical (⊢sub ⊢e ρ≥:ρ' _) V-use with canonical ⊢e V-use
... | C-use r≥:ρ ⊢e' = C-use (≥:-trans r≥:ρ ρ≥:ρ') ⊢e'

data Progress (e : Term) : Set where
  step : ∀ {e'}
       → e ↝ e'
         ------
       → Progress e
  done : Value e
         ----------
       → Progress e


progress : ∀ {e τ}
         → ∅ ⊢ e ⦂ τ
           ----------
         → Progress e
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
...   | C-use _ _ = step β->>=-use
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
progress (⊢use ⊢e) = done V-use
progress (⊢⋎ ⊢e₁ ⊢e₂ dist) = step β-⋎
progress (⊢sub ⊢e _ _) = progress ⊢e

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
rename ρ (⊢sub ⊢e ρ≥:ρ' ok) = ⊢sub (rename ρ ⊢e) ρ≥:ρ' ok

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
extend (⊢sub ⊢e ρ≥:ρ' ok) x∉ = ⊢sub (extend ⊢e x∉) ρ≥:ρ' ok






-- closeσ : ∀ {Γ Γ' x y σ σ' e} → ∀ (τ' τ)
--        → Γ , x ⦂ close (Γ' , y ⦂ σ') τ' ⊢ e ⦂ τ
--        → σ ≥ σ'
--        → Γ , x ⦂ close (Γ' , y ⦂ σ) τ' ⊢ e ⦂ τ
-- closeσ {Γ} {Γ'} {x} {y} {σ} {σ'} {e} τ' τ ⊢e⦂τ' σ>σ' rewrite close> {Γ'} {y} {σ} {σ'} {τ'} σ>σ' = ⊢e⦂τ'

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
... | yes refl = ⊢lt (gen ⊢e'⦂τ' σ>σ') (sneakIn (gen (drop ⊢e⦂τ) (close≥ {Γ} {x} σ>σ')))
... | no x≢y =
      let ⊢e⦂τswp = swap x≢y ⊢e⦂τ
          ⊢e⦂τswp' = gen ⊢e⦂τswp σ>σ'
          ⊢e⦂τswp'' = swap (≢-sym x≢y) ⊢e⦂τswp'
          ⊢e⦂τhyp = gen ⊢e⦂τswp'' (close≥ {Γ} {x} σ>σ')
          in ⊢lt (gen ⊢e'⦂τ' σ>σ') ⊢e⦂τhyp

gen (⊢× ⊢e₁ ⊢e₂) σ>σ' = ⊢× (gen ⊢e₁ σ>σ') (gen ⊢e₂ σ>σ')
gen (⊢π₁ ⊢e) σ>σ' = ⊢π₁ (gen ⊢e σ>σ')
gen (⊢π₂ ⊢e) σ>σ' = ⊢π₂ (gen ⊢e σ>σ')
gen (⊢⟦⟧ x cl) σ>σ' = ⊢⟦⟧ (gen x σ>σ') cl
gen (⊢>>= x x₁) σ>σ' = ⊢>>= (gen x σ>σ') (gen x₁ σ>σ')
gen ⊢□ σ>σ' = ⊢□
gen (⊢use ⊢e) σ>σ' = ⊢use (gen ⊢e σ>σ')
gen (⊢⋎ ⊢e₁ ⊢e₂ dist) σ>σ' = ⊢⋎ (gen ⊢e₁ σ>σ') (gen ⊢e₂ σ>σ') dist
gen (⊢sub ⊢e ρ≥:ρ' ok) σ>σ' = ⊢sub (gen ⊢e σ>σ') ρ≥:ρ' ok

postulate fvsClosed : ∀ {Γ e τ x} → Γ ⊢ e ⦂ τ → x ∈ FV(e) → ∃[ σ ] (x ⦂ σ ∈ Γ)
-- fvsClosed (⊢` {σ = σ} x∈ σ>τ) (here refl) = ⟨ σ , x∈ ⟩
-- fvsClosed {x = x} (⊢ƛ {x = y} ⊢e) x∈fv with x ≟ y
-- ... | yes refl = {!!}
-- ... | no x≢y = {!!}
-- fvsClosed (⊢· ⊢e ⊢e₁) x∈ = {!!}
-- fvsClosed (⊢lt ⊢e ⊢e₁) x∈ = {!!}
-- fvsClosed (⊢× ⊢e ⊢e₁) x∈ = {!!}
-- fvsClosed (⊢π₁ ⊢e) x∈ = {!!}
-- fvsClosed (⊢π₂ ⊢e) x∈ = {!!}
-- fvsClosed (⊢⟦⟧ ⊢e x) x∈ = {!!}
-- fvsClosed (⊢>>= ⊢e ⊢e₁) x∈ = {!!}
-- fvsClosed (⊢⋎ ⊢e ⊢e₁ x) x∈ = {!!}
-- fvsClosed (⊢sub ⊢e x x₁) x∈ = {!!}
-- fvsClosed (⊢use ⊢e) x∈ = {!!}

ignore-++ˡ : ∀ {Γ Δ p q}
      → (∀ {x σ} → x ∈ p ++ q → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
      → (∀ {x σ} → x ∈ p → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
ignore-++ˡ f x∈p = f (∈-++⁺ˡ ≡-setoid x∈p)

ignore-++ʳ : ∀ {Γ Δ p q}
      → (∀ {x σ} → x ∈ p ++ q → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
      → (∀ {x σ} → x ∈ q → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
ignore-++ʳ {p = p} f x∈p = f (∈-++⁺ʳ ≡-setoid p x∈p)

-- lemma 4.1
-- extra vars in the environment can be ignored
ignore : ∀ {Γ Δ e τ}
       → (∀ {x σ} → x ∈ FV(e) → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
       → Γ ⊢ e ⦂ τ
       → Δ ⊢ e ⦂ τ
ignore ρ (⊢` x∈ σ>τ) = ⊢` (ρ (here refl) x∈) σ>τ
ignore {Γ} {Δ} ρ (⊢ƛ {x = y} {τ' = τ'} {e = e} ⊢e) = ⊢ƛ (ignore f ⊢e)
  where
  f : ∀ {x σ} → x ∈ FV e → x ⦂ σ ∈ Γ , y ⦂ ` τ' → x ⦂ σ ∈ Δ , y ⦂ ` τ'
  f x∈FV Z = Z
  f x∈FV (S x∈Γ x≢y) = let z = ρ (/-∈≢ x∈FV x≢y) x∈Γ in S z x≢y

ignore ρ (⊢× ⊢e₁ ⊢e₂) = ⊢× (ignore (ignore-++ˡ ρ) ⊢e₁) (ignore (ignore-++ʳ ρ) ⊢e₂)
ignore ρ (⊢π₁ ⊢e) = ⊢π₁ (ignore ρ ⊢e)
ignore ρ (⊢π₂ ⊢e) = ⊢π₂ (ignore ρ ⊢e)
ignore ρ (⊢· ⊢e₁ ⊢e₂) = ⊢· (ignore (ignore-++ˡ ρ) ⊢e₁) (ignore (ignore-++ʳ ρ) ⊢e₂)
ignore {Γ} {Δ} {e} ρ (⊢lt {e = e'} {e' = e''} {τ = τ} {τ' = τ'} {x = y} ⊢e ⊢e') = ⊢lt (ignore (ignore-++ˡ ρ) ⊢e) (h ⊢e') 
  where

  g : ∀ {x σ} → x ∈ FV e' → x ⦂ σ ∈ Γ , y ⦂ close Δ τ' → x ⦂ σ ∈ Δ , y ⦂ close Δ τ'
  g x∈FV Z = Z
  g {x} x∈FV (S x∈Γ x≢y) with x ≟ y
  ... | yes refl = ⊥-elim (x≢y refl)
  ... | no _ = let z = ignore-++ʳ {Γ} {Δ} {FV(e'')} {FV(e') / [ y ]} ρ
                   y = z (/-∈≢ x∈FV x≢y) x∈Γ in S y x≢y
 
  f : ∀ {Γ Δ τ} → close Δ τ > τ → Disjoint (FTV (close Δ τ)) (TSvars (close Γ τ)) → close Δ τ ≥ close Γ τ
  f clΔ>τ dj = {!!}

  i : ∀ {Γ τ} → close Γ τ > τ
  i {Γ} = {!!}

  h : Γ , y ⦂ close Γ τ' ⊢ e' ⦂ τ → Δ , y ⦂ close Δ τ' ⊢ e' ⦂ τ
  h ⊢e' = let z : Γ , y ⦂ close Δ τ' ⊢ e' ⦂ τ
              z = gen ⊢e' (f {Γ} {Δ} i {!DisThere!})
           in ignore g z

ignore ρ (⊢⟦⟧ ⊢e cl) = ⊢⟦⟧ (ignore ρ ⊢e) cl
ignore ρ (⊢>>= {e = e} {e' = e'} ⊢e ⊢e') = ⊢>>= (ignore (ignore-++ˡ ρ) ⊢e) (ignore (ignore-++ʳ ρ) ⊢e')
ignore ρ ⊢□ = ⊢□
ignore ρ (⊢use ⊢e) = ⊢use (ignore ρ ⊢e)
ignore ρ (⊢⋎ ⊢e₁ ⊢e₂ ok) = ⊢⋎ (ignore (ignore-++ˡ ρ) ⊢e₁) (ignore (ignore-++ʳ ρ) ⊢e₂) ok
ignore ρ (⊢sub z ρ≥:ρ' ok) = ⊢sub (ignore ρ z) ρ≥:ρ' ok

Γcong : ∀ {Γ x e τ σ σ'} → Γ , x ⦂ σ ⊢ e ⦂ τ → σ ≡ σ' → Γ , x ⦂ σ' ⊢ e ⦂ τ
Γcong Γ refl = Γ

Γ⊢cong : ∀ {Γ e τ τ'}
       → τ ≡ τ'
       → Γ ⊢ e ⦂ τ
       → Γ ⊢ e ⦂ τ'
Γ⊢cong refl ⊢e = ⊢e


sub> : ∀ {s σ τ} → σ > τ → sub s σ > subT s τ
sub> {s} {σ} (Inst s' x y) = Inst (s' ∘ˢ s) {!!} {!!}

-- tofte lemma 2.6
-- lemma26 : ∀ {s σ σ' τ} → σ > τ → σ ⇒ s ⇒ σ' → σ' > subT s τ)

-- _ : (s : Substitution) → x ⦂ close Γ τ' → 

postulate closesub : ∀ {Γ τ s} → ∃[ s' ] (sub s (close Γ τ) ≡ close (subC s' Γ) (subT s' τ))

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

subContextTyping {Γ} {e} (⊢ƛ {x = x} {τ' = τ'} {τ = τ} {e = e'} ⊢e) s = ⊢ƛ (f (subContextTyping ⊢e s))
  where
  f : subC s Γ , x ⦂ sub s (` τ') ⊢ e' ⦂ subT s τ → subC s Γ , x ⦂ ` subT s τ' ⊢ e' ⦂ subT s τ
  f ⊢e rewrite subT≡sub {τ'} s = ⊢e

  
subContextTyping (⊢· ⊢e₁ ⊢e₂) s = ⊢· (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)

subContextTyping {Γ} (⊢lt {τ = τ} ⊢e ⊢e') s with sub s (VV (FTVT τ / FTVC Γ) τ) |  closesub {Γ} {τ} {s}
... | z | ⟨ s' , refl ⟩ = {!!}
  -- ⊢lt (subContextTyping ⊢e s)
  --     (let z = (subContextTyping ⊢e' s)
  --          in {!!})
  -- where
  -- -- equation 2.26 in tofte
  -- postulate g : ∀ {Γ τ} → sub s (close Γ τ) ≡ close (subC s Γ) (subT s τ)
      
  -- f : ∀ {Γ s x τ} → subC s (Γ , x ⦂ close Γ τ) ≡ subC s Γ , x ⦂ close (subC s Γ) (subT s τ)
  -- f {Γ} {s} {x} {τ} rewrite g {Γ} {s} {τ} = refl
  -- f' : ∀ {Γ s x τ' e τ}
  --    → subC s (Γ , x ⦂ close Γ τ') ⊢ e ⦂ τ
  --    → subC s Γ , x ⦂ close (subC s Γ) (subT s τ') ⊢ e ⦂ τ
  -- f' {Γ} {s} {x} {τ'} {e} {τ} ⊢e rewrite (cong (λ z → z ⊢ e ⦂ τ) (f {Γ} {s} {x} {τ'})) = ⊢e

subContextTyping (⊢× ⊢e₁ ⊢e₂) s = ⊢× (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping (⊢π₁ ⊢e) s = ⊢π₁ (subContextTyping ⊢e s)
subContextTyping (⊢π₂ ⊢e) s = ⊢π₂ (subContextTyping ⊢e s)
subContextTyping (⊢⟦⟧ ⊢e cl) s = ⊢⟦⟧ (subContextTyping ⊢e s) cl
subContextTyping (⊢>>= ⊢e₁ ⊢e₂) s = ⊢>>= (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping ⊢□ s = ⊢□
subContextTyping (⊢use ⊢e) s = ⊢use (subContextTyping ⊢e s)
subContextTyping (⊢⋎ ⊢e₁ ⊢e₂ dist) s = ⊢⋎ (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s) dist
subContextTyping (⊢sub ⊢e ρ≥:ρ' ok) s = ⊢sub (subContextTyping ⊢e s) ρ≥:ρ' ok

-- chooses a substitution such that FTV Γ ∩ subRegion s ∩ αs ≡ ∅
absSubChoose : ∀ {Γ x' x αs τ₁ τ e₁ τ₂}
             → Γ , x' ⦂ τ₁ , x ⦂ VV αs τ ⊢ e₁ ⦂ τ₂
             → ∃[ s ] ⟨ Disjoint (FTVC Γ) αs × ⟨ (Disjoint (subRegion (BJS.to s)) αs) × (Disjoint (subRegion (BJS.to s)) (FTVC Γ)) ⟩ ⟩
absSubChoose {αs = αs} ⊢e with freshTypeVars αs
... | ⟨ βs , djαβ ⟩ = {!!}

subC∅ : (s : Substitution) → subC s ∅ ≡ ∅
subC∅ _ = refl

-- i know this is true!
postulate sub∉FTVC : ∀ {Γ α τ s} → α ∉ FTVC Γ → subC (SS α τ s) Γ ≡ subC s Γ
-- sub∉FTVC {∅} x∉ = refl
-- sub∉FTVC {Γ , x ⦂ σ} {α} {τ} {s} x∉ = {!!}
  
disjointSub : ∀ {Γ s} → Disjoint (subDomain s) (FTVC Γ) → subC s Γ ≡ Γ
disjointSub {Γ} {SZ} DisHere = subCSZ
disjointSub {Γ} {SS α σ s} (DisThere x dj) rewrite sub∉FTVC {Γ} {α} {σ} {s} x = disjointSub dj

∉∈≢ : ∀ {x y a} → x ∉ a → y ∈ a → x ≢ y
∉∈≢ x∉a y∈a refl = ⊥-elim (x∉a y∈a)

-- Wright & Felleisen lemma 4.4
-- Note, in Wright & Felleisen's proposition, only values can be substitued in.
-- Does this affect our approach here?
subst : ∀ {Γ x e e' αs τ τ'}
      → Γ ⊢ e ⦂ τ
      → Γ , x ⦂ VV αs τ ⊢ e' ⦂ τ'
      → Disjoint αs (FTVC Γ)
        -------------------
      → Γ ⊢ e' [ x := e ] ⦂ τ'
subst {Γ} {x = y} {e} {αs = αs} {τ = τ} {τ' = τ'} ⊢e (⊢` {x = x} Z (Inst s ds≡αs refl)) ∉Γ
  rewrite TSvars≡ {αs} {τ} with ds≡αs | x ≟ y
... | refl | yes refl = prf (prt2 prt1)
    where prt1 : subC s Γ ⊢ e ⦂ subT s τ
          prt1 = subContextTyping ⊢e s
          prt2 : subC s Γ ⊢ e ⦂ subT s τ → subC s Γ ⊢ e ⦂ τ'
          prt2 ⊢e rewrite TStype≡ {αs} {τ} = ⊢e
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
     where subContextSplit : ∀ {Γ s x σ y σ' e τ}
                           → subC s Γ ≡ Γ
                           → subC s (Γ , x ⦂ σ , y ⦂ σ') ⊢ e ⦂ τ
                           → (Γ , x ⦂ (sub s σ), y ⦂ (sub s σ')) ⊢ e ⦂ τ
           subContextSplit {Γ} {s = s} sΓ≡Γ ⊢e with subC s Γ |  sΓ≡Γ
           ... | .Γ | refl = ⊢e


           prt2help : ∀ {Γ s αs τ e τ'}
                    → sub s (VV αs τ) ≡ VV αs τ
                    → Γ , x ⦂ sub s (VV αs τ) ⊢ e ⦂ τ'
                    → Γ , x ⦂ VV αs τ ⊢ e ⦂ τ'
           prt2help {Γ} {s} {αs} {τ} eq ⊢e with sub s (VV αs τ) | eq
           ... | .(VV αs τ) | refl = ⊢e


           prf : Γ , x' ⦂ ` τ₁ ⊢ e₁ [ x := v ] ⦂ τ₂
           prf with absSubChoose (swap x'≢x ⊢e')
           prf | ⟨ bjs , ⟨ djΓαs , ⟨ djsαs , djsΓ ⟩ ⟩ ⟩ =
             let swp : Γ , x' ⦂ ` τ₁ , x ⦂ VV αs τ ⊢ e₁ ⦂ τ₂
                 swp = swap x'≢x ⊢e'
                 s = BJS.to bjs
                 s⁻¹ = BJS.from bjs
                 SΓ≡Γ : subC s Γ ≡ Γ
                 SΓ≡Γ = disjointSubContext djsΓ  -- dom(s) ∩ ftv(Γ) = ∅             

                 prt2' : subC s (Γ , x' ⦂ (` τ₁) , x ⦂ VV αs τ) ⊢ e₁ ⦂ subT s τ₂
                 prt2' = subContextTyping {Γ , x' ⦂ ` τ₁ , x ⦂ VV αs τ} swp s

                 prt2'' : Γ , x' ⦂ sub s (` τ₁) , x ⦂ sub s (VV αs τ) ⊢ e₁ ⦂ subT s τ₂
                 prt2'' = subContextSplit SΓ≡Γ prt2'

                 prt2 : Γ , x' ⦂ sub s (` τ₁) , x ⦂ VV αs τ ⊢ e₁ ⦂ subT s τ₂
                 prt2 = prt2help {s = s} (disjointSubTypeScheme {s = s} djsαs) prt2''

                 prt3' : x' ∉ FV v
                 prt3' = {!!}
                 prt3 : Γ , x' ⦂ sub s (` τ₁) ⊢ v ⦂ τ
                 prt3 = ignore (λ x∈FVv x∈Γ → S x∈Γ (≢-sym (∉∈≢ prt3' x∈FVv))) ⊢e
                 
                 prt4 : Disjoint αs (FTVC (Γ , x' ⦂ sub s (` τ₁)))
                 prt4 = disjoint-sym {!!} -- need to show Disjoint (FTV (sub (BJS.to bjs) (` τ₁))) αs
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
subst {x = y} ⊢e (⊢sub ⊢e' ρ≥:ρ' ok) p = ⊢sub (subst ⊢e ⊢e' p) ρ≥:ρ' ok

preservation : ∀ {e e' τ}
             → ∅ ⊢ e ⦂ τ
             → e ↝ e'
               ----------
             → ∅ ⊢ e' ⦂ τ
preservation (⊢· ⊢e ⊢e') (ξ-·₁ e↝e') = ⊢· (preservation ⊢e e↝e') ⊢e'
preservation (⊢· ⊢e ⊢e') (ξ-·₂ e↝e') = ⊢· ⊢e (preservation ⊢e' e↝e')
preservation (⊢· (⊢ƛ ⊢e) ⊢e') (β-ƛ _) = subst ⊢e' ⊢e DisHere

preservation (⊢lt {τ' = τ'} ⊢e' ⊢e) β-lt rewrite toVVClose τ' = subst ⊢e' ⊢e disjoint-[]

-- product types
preservation (⊢× ⊢e₁ ⊢e₂) (ξ-×₁ e₁↝e₁') = ⊢× (preservation ⊢e₁ e₁↝e₁') ⊢e₂
preservation (⊢× ⊢e₁ ⊢e₂) (ξ-×₂ e₂↝e₂') = ⊢× ⊢e₁ (preservation ⊢e₂ e₂↝e₂')
preservation (⊢π₁ ⊢e) (ξ-π₁ e↝e') = ⊢π₁ (preservation ⊢e e↝e')
preservation (⊢π₁ (⊢× ⊢e₁ ⊢e₂)) β-π₁ = ⊢e₁
preservation (⊢π₂ ⊢e) (ξ-π₂ e↝e') = ⊢π₂ (preservation ⊢e e↝e')
preservation (⊢π₂ (⊢× ⊢e₁ ⊢e₂)) β-π₂ = ⊢e₂

preservation (⊢>>= ⊢m ⊢f) (ξ->>= m↝m') = ⊢>>= (preservation ⊢m m↝m') ⊢f
preservation (⊢>>= ⊢e ⊢f) β->>= = ⊢· ⊢f (unwrap⟦⟧ ⊢e)
preservation (⊢>>= ⊢u ⊢e') β->>=-use = ⊢· ⊢e' (f ⊢u)
  where f : ∀ {Γ r e ρ τ} → Γ ⊢ use r e ⦂ IO ρ τ → Γ ⊢ e ⦂ τ
        f (⊢use ⊢e) = ⊢e
        f (⊢sub ⊢e _ _) = f ⊢e

preservation (⊢⋎ ⊢e₁ ⊢e₂ ok) β-⋎ =
  let ⊢`v = ⊢` (S Z (λ ())) >self 
      ⊢`w = ⊢` Z >self
      ⊢>>=inner = ⊢>>= (⊢sub (weaken ⊢e₂) (≥:∪ʳ ≥:Refl) ok)
                       (⊢ƛ (⊢⟦⟧ (⊢× ⊢`v ⊢`w) ok))
  in ⊢>>= (⊢sub ⊢e₁ (≥:∪ˡ ≥:Refl) ok) (⊢ƛ ⊢>>=inner)

preservation (⊢sub ⊢e ρ≥:ρ' ok) e↝e' = ⊢sub (preservation ⊢e e↝e') ρ≥:ρ' ok

noConcurrentAccess : ∀ {Γ e₁ e₂ ρ τ} → Γ ⊢ e₁ ⋎ e₂ ⦂ IO ρ τ → Ok ρ
noConcurrentAccess (⊢⋎ ⊢e₁ ⊢e₂ ok) = ok
noConcurrentAccess (⊢sub ⊢e x ok) = ok

-- It's impossible for two heaps, unioned together, to be distinct
¬x∩x=∅ : ∀ {ρ} → ¬ (ρ ∩ ρ =∅)
¬x∩x=∅ (DHZ x) = x refl
¬x∩x=∅ (DHL dist dist₁ dist₂) = ¬x∩x=∅ (distinct-∪ˡ (distinct-sym dist))
¬x∩x=∅ (DHR dist dist₁ dist₂) = ¬x∩x=∅ (distinct-∪ʳ (distinct-sym dist₁))

-- It's impossible for two heaps, unioned together, to be well formed
¬okρ∪ρ : ∀ {ρ} → ¬ Ok (ρ ∪ ρ)
¬okρ∪ρ (OkS ok ok₁ dist) = ¬x∩x=∅ dist
