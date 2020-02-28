module Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; ≢-sym)
  
open import Data.List using (List; _∷_; [_]; [])
open import Data.List.Membership.Setoid.Properties

open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)

open import Data.String.Properties using (≈-setoid)
import Data.List.Relation.Binary.Subset.Setoid as Subset
open module SubsetString = Subset ≈-setoid
import Data.List.Membership.Setoid as Membership
open module MembershipString = Membership ≈-setoid using (_∈_;_∉_; find)

open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

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
rename ρ (⊢lt Γ⊢e'⦂τ' Γ⊢e'⦂τ) = ⊢lt (rename ρ Γ⊢e'⦂τ') {!!}
    
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



-- if σ' > σ then either σ' ≡ σ or σ' is of the form ∀ α . σ

-- subOnType : ∀ {τ} → (s : Substitution) → sub s (` τ) ≡ ` τ
-- subOnType SZ = refl
-- subOnType (SS _ _ s) = subOnType s

-- type>Eq : ∀ {τ σ} → ` τ > σ → σ ≡ ` τ
-- type>Eq (General s refl) = subOnType s

-- asdf5 : ∀ {σ τ} → (s : Substitution) → sub s (` (IO σ τ)) → sub s (` τ)
-- asdf5 SZ = {!!}
-- asdf5 (SS x x₁ s) = {!!}

-- asdf5 : ∀ {Γ x y σ σ' e τ τ'}
--       → Γ , x ⦂ close (Γ , y ⦂ σ') τ' ⊢ e ⦂ τ
--       → σ' > σ
--         -------------------------------------
--       → Γ , x ⦂ close (Γ , y ⦂ σ) τ' ⊢ e ⦂ τ
-- asdf5 ⊢e σ'>σ = {!!}

closeσ : ∀ {Γ Γ' x y σ σ' e} → ∀ (τ' τ)
       → Γ , x ⦂ close (Γ' , y ⦂ σ') τ' ⊢ e ⦂ τ
       → σ ≥ σ'
       → Γ , x ⦂ close (Γ' , y ⦂ σ) τ' ⊢ e ⦂ τ
closeσ {Γ} {Γ'} {x} {y} {σ} {σ'} {e} τ' τ ⊢e⦂τ' σ>σ' = {!!}

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
          
gen (⊢⟦⟧ x) σ>σ' = ⊢⟦⟧ (gen x σ>σ')
gen (⊢>>= x x₁) σ>σ' = ⊢>>= (gen x σ>σ') (gen x₁ σ>σ')
gen ⊢□ σ>σ' = ⊢□

subTSZ : ∀ {τ} → subT SZ τ ≡ τ
subTSZ {` x} = refl
subTSZ {τ ⇒ τ'} rewrite subTSZ {τ} | subTSZ {τ'} = refl
subTSZ {IO x τ} = cong (IO x) subTSZ
subTSZ {□} = refl

-- this is wrong? sub on type scheme only instantiates
-- subT~sub : ∀ {τ} → (s : Substitution) → sub s (` τ) ≡ ` (subT s τ)
-- subT~sub {τ} SZ =
--   begin
--     sub SZ (` τ)
--   ≡⟨⟩
--     (` τ)
--   ≡⟨ cong (`_) (sym (subTSZ {τ})) ⟩
--     (` (subT SZ τ))
--   ∎
-- subT~sub {τ} (SS id τ' si) =
--   begin
--     sub (SS id τ' si) (` τ)
--   ≡⟨⟩
--     sub si (substitute id τ' (` τ))
--   ≡⟨⟩
--     sub si (` τ)
--   ≡⟨ subT~sub si ⟩
--     ` (subT si τ)
--   ≡⟨⟩  
--     ` (subT (SS id τ' si) τ)
--   ≡⟨⟩
--     {!!}

Γcong : ∀ {Γ x e τ σ σ'} → Γ , x ⦂ σ ⊢ e ⦂ τ → σ ≡ σ' → Γ , x ⦂ σ' ⊢ e ⦂ τ
Γcong Γ refl = Γ

Γ⊢cong : ∀ {Γ e τ τ'}
       → τ ≡ τ'
       → Γ ⊢ e ⦂ τ
       → Γ ⊢ e ⦂ τ'
Γ⊢cong refl ⊢e = ⊢e

-- tofte lemma 2.6

-- wright and felleisen lemma 4.5,
-- tofte lemma 2.7
subContextTyping : ∀ {Γ e τ}
                   → Γ ⊢ e ⦂ τ
                   → (s : Substitution)
                   → subC s Γ ⊢ e ⦂ subT s τ
subContextTyping {Γ} (⊢` {x = x} {σ} x∈Γ σ>τ) s = {!!}
  where
--  f : x ⦂ σ ∈ Γ → x ⦂ subT s τ ∈ subC s Γ
subContextTyping {Γ} (⊢ƛ {x = x} {τ' = τ'} ⊢e) s = {!!}
  -- ⊢ƛ (Γcong (subContextTyping {Γ , x ⦂ ` τ'} ⊢e s) {!!})
subContextTyping (⊢· ⊢e₁ ⊢e₂) s = ⊢· (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping (⊢lt ⊢e ⊢e') s = {!!}
subContextTyping (⊢⟦⟧ ⊢e) s = ⊢⟦⟧ (subContextTyping ⊢e s)
subContextTyping (⊢>>= ⊢e₁ ⊢e₂) s = ⊢>>= (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping ⊢□ s = ⊢□



-- -- s must cover all of αs
fooo : ∀ {τ τ' e Γ}
     → (s : Substitution)
     → subT s τ ≡ τ'
     → Γ ⊢ e ⦂ subT s τ
     → Γ ⊢ e ⦂ τ'
fooo s refl ⊢e = ⊢e
-- fooo {[]} s sub≡τ' ⊢e = {!!}
--   where
--   g : ∀ {τ}  (s : Substitution) → sub s (` τ) ≡ ` (subT s τ)
--   g {τ} SZ = refl
--   g {τ} (SS id τ' si) =
--     begin
--       sub (SS id τ' si) (` τ)
--     ≡⟨⟩
--       sub si (substitute id τ' (` τ))
--     -- ≡⟨⟩
--     --   sub si (` τ)
--     ≡⟨ g si ⟩
--       ` (subT si (extractTS (substitute id τ' (` τ))))
--     ≡⟨⟩
--       {!!}
--     --    sub s (` τ)
--     -- ≡⟨ g s ⟩
--     --   {!!}
    
  
-- fooo {α ∷ αs} s _ ⊢e = {!!}

-- fooo {[]} SZ refl = refl
-- fooo {α ∷ αs} SZ ()
-- fooo {[]} (SS id type s) p = {!!}
-- fooo {α ∷ αs} (SS id σ s) p with α ≟ id
-- ... | yes refl = {!!}
-- ... | no α≢id = {!!}


data NotInContext : List Id → Context → Set where
  NotHere : ∀ {Γ} → NotInContext [] Γ
  NotThere : ∀ {α αs Γ}
         → α ∉ freeVarsC Γ
         → NotInContext αs Γ
         → NotInContext (α ∷ αs) Γ

notIn∅ : ∀ {αs : List Id} → NotInContext αs ∅
notIn∅ {[]} = NotHere
notIn∅ {x ∷ αs} = NotThere (λ ()) notIn∅

subst : ∀ {Γ x e e' αs τ τ'}
      → ∅ ⊢ e ⦂ τ
      → Γ , x ⦂ VV αs τ ⊢ e' ⦂ τ'
      → NotInContext αs Γ
        -------------------
      → Γ ⊢ e' [ x := e ] ⦂ τ'
subst {x = y} {αs = αs} {τ = τ} ⊢e (⊢` {x = x} Z σ>τ@(General s refl)) ∉Γ rewrite (extractVV≡ {αs} {τ}) with x ≟ y
... | yes refl = let z = subContextTyping ⊢e s
                     in weaken z
-- -- ...  | yes refl = fooo s sub≡τ' (weaken (subContextTyping ⊢e s)) -- with (fooo s sub≡τ')
-- -- ...       | refl = weaken (subContextTyping ⊢e s)
... | no x≢y = ⊥-elim (x≢y refl)

subst {x = y} ⊢e (⊢` {x = x} (S x∈ x≢y) τ''>τ) _ with x ≟ y
...  | yes x≡y = ⊥-elim (x≢y x≡y)
...  | no x≢y' = ⊢` x∈ τ''>τ
subst {x = y} ⊢e (⊢ƛ {x = x} ⊢e') p with x ≟ y
...  | yes refl = ⊢ƛ (drop ⊢e')
...  | no x≢y = ⊢ƛ (subst ⊢e (swap x≢y ⊢e') {!!})
subst {x = y} ⊢e (⊢· e e') p = ⊢· (subst ⊢e e p) (subst ⊢e e' p)
subst {x = y} ⊢e ⊢□ _ = ⊢□
subst {x = y} ⊢e (⊢⟦⟧ ⊢e') p = ⊢⟦⟧ (subst ⊢e ⊢e' p)
subst {x = y} ⊢e (⊢>>= ⊢m ⊢f) p = ⊢>>= (subst ⊢e ⊢m p) (subst ⊢e ⊢f p)
subst {x = y} ⊢e (⊢lt x x₁) _ = {!!}

  
preservation : ∀ {e e' τ}
             → ∅ ⊢ e ⦂ τ
             → e ↝ e'
               ----------
             → ∅ ⊢ e' ⦂ τ
preservation (⊢· ⊢e ⊢e') (ξ-·₁ e↝e') = ⊢· (preservation ⊢e e↝e') ⊢e'
preservation (⊢· ⊢e ⊢e') (ξ-·₂ e↝e') = ⊢· ⊢e (preservation ⊢e' e↝e')
preservation (⊢· (⊢ƛ ⊢e) ⊢e') (β-ƛ _) = subst ⊢e' ⊢e NotHere
preservation (⊢>>= ⊢m ⊢f) (ξ->>= m↝m') = ⊢>>= (preservation ⊢m m↝m') ⊢f
preservation (⊢>>= (⊢⟦⟧ ⊢e) ⊢f) β->>= = ⊢· ⊢f ⊢e
-- x ⦂ VV αs τ' ≡ x ⦂ close ∅ τ'
preservation (⊢lt {τ' = τ'} ⊢e' ⊢e) β-lt with close ∅ τ' | toVVClose τ'
... | ._ | refl = subst ⊢e' ⊢e notIn∅

