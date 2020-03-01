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
rename p (⊢⟦⟧ ⊢e) = ⊢⟦⟧ (rename p ⊢e)
rename p (⊢>>= ⊢m ⊢f) = ⊢>>= (rename p ⊢m) (rename p ⊢f)
rename p ⊢□ = ⊢□
rename {Γ} {Δ} ρ (⊢lt Γ⊢e'⦂τ' Γ⊢e'⦂τ) = ⊢lt (rename ρ Γ⊢e'⦂τ') (renameClose ρ Γ⊢e'⦂τ)
    
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


-- lemma 4.1
-- extra vars in the environment can be ignored
ignore : ∀ {Γ Δ e τ}
       → (∀ {x σ} → x ∈ FV(e) → x ⦂ σ ∈ Γ → x ⦂ σ ∈ Δ)
       → Γ ⊢ e ⦂ τ
       → Δ ⊢ e ⦂ τ
ignore ρ (⊢` {x = x} x∈ σ>τ) = ⊢` (ρ (here (refl)) x∈) σ>τ
ignore ρ (⊢ƛ ⊢e) = ⊢ƛ {!!}
ignore ρ (⊢· ⊢e₁ ⊢e₂) = ⊢· (ignore {!!} {!!}) {!!}
ignore ρ (⊢lt ⊢e ⊢e₁) = ⊢lt {!!} {!!}
ignore ρ (⊢⟦⟧ ⊢e) = ⊢⟦⟧ (ignore ρ ⊢e)
ignore ρ (⊢>>= {e = e} {e' = e'} ⊢e ⊢e') = ⊢>>= (ignore {!!} ⊢e) {!!}
ignore ρ ⊢□ = ⊢□

∉-++⁺ˡ : ∀ {v xs ys} → v ∉ xs → v ∉ ys → v ∉ xs ++ ys
∉-++⁺ˡ {v} {xs} {ys} ∉xs ∉ys x∈ with ∈-++⁻ (≡-setoid) {v} xs {ys} x∈
... | inj₁ ∈xs = ∉xs ∈xs
... | inj₂ ∈ys = ∉ys ∈ys

∉-++⁻ : ∀ {v xs ys} → v ∉ xs ++ ys → v ∉ xs × v ∉ ys
∉-++⁻ {v} {xs} {ys} ∉xs++ys = ⟨ l , r ⟩
  where
    l : v ∉ xs
    l v∈xs = ∉xs++ys (∈-++⁺ˡ ≡-setoid v∈xs)
    r : v ∉ ys
    r v∈ys = ∉xs++ys (∈-++⁺ʳ ≡-setoid xs v∈ys)

∉-/≢ : ∀ {v xs y} → v ∉ xs / (y ∷ []) → v ≢ y → v ∉ xs
∉-/≢ {v} {xs} {y} v∉xs/y v≢y v∈xs = v∉xs/y (/-∈≢ v∈xs v≢y)

extend : ∀ {Γ x σ e τ}
       → Γ ⊢ e ⦂ τ
       → x ∉ FV(e)
       → Γ , x ⦂ σ ⊢ e ⦂ τ
extend {x = x} (⊢` {x = y} x∈ σ>τ) x∉ with x ≟ y
... | yes refl = ⊥-elim (x∉ (here refl))
... | no x≢y = ⊢` (S x∈ (λ z → x≢y (sym z))) σ>τ
extend {x = x} {e = e} (⊢ƛ {x = y} ⊢e) x∉ with x ≟ y
... | yes refl = ⊢ƛ (sneakIn ⊢e)
... | no x≢y = ⊢ƛ (swap x≢y (extend ⊢e (∉-/≢ x∉ x≢y)))
extend (⊢· ⊢e₁ ⊢e₂) x∉ with ∉-++⁻ x∉
... | ⟨ ∉e₁ , ∉e₂ ⟩ = ⊢· (extend ⊢e₁ ∉e₁) (extend ⊢e₂ ∉e₂)
extend {Γ} {σ = σ} (⊢lt {τ' = τ'} ⊢e ⊢e') x∉ with ∉-++⁻ x∉ | close Γ τ'
... | ⟨ ∉e , ∉e' ⟩ | foo = ⊢lt (extend ⊢e ∉e) {!!}
extend (⊢⟦⟧ ⊢e) x∉ = ⊢⟦⟧ (extend ⊢e x∉)
extend {x = x} (⊢>>= {e = e} {e' = e'} ⊢e ⊢e') x∉ with ∉-++⁻ {x} {FV(e)} {FV(e')} x∉
... | ⟨ ∉e , ∉e' ⟩ = ⊢>>= (extend ⊢e ∉e) (extend ⊢e' ∉e')
extend ⊢□ x∉ = ⊢□

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

-- close>' : ∀ {Γ}
--         → Γ , x ⦂ (Γ' , y ⦂ 

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
          
gen (⊢⟦⟧ x) σ>σ' = ⊢⟦⟧ (gen x σ>σ')
gen (⊢>>= x x₁) σ>σ' = ⊢>>= (gen x σ>σ') (gen x₁ σ>σ')
gen ⊢□ σ>σ' = ⊢□

subTSZ : ∀ {τ} → subT SZ τ ≡ τ
subTSZ {` x} = refl
subTSZ {τ ⇒ τ'} rewrite subTSZ {τ} | subTSZ {τ'} = refl
subTSZ {IO x τ} = cong (IO x) subTSZ
subTSZ {□} = refl

subCSZ : ∀ {Γ} → subC SZ Γ ≡ Γ
subCSZ {∅} = refl
subCSZ {Γ , x ⦂ σ} = cong (λ z → z , x ⦂ σ) subCSZ

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
-- lemma26 : ∀ {s σ σ' τ} → σ > τ → σ ⇒ s ⇒ σ' → σ' > subT s τ)

-- _ : (s : Substitution) → x ⦂ close Γ τ' → 

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
subContextTyping (⊢lt ⊢e ⊢e') s = ⊢lt (subContextTyping ⊢e s) {!!}
subContextTyping (⊢⟦⟧ ⊢e) s = ⊢⟦⟧ (subContextTyping ⊢e s)
subContextTyping (⊢>>= ⊢e₁ ⊢e₂) s = ⊢>>= (subContextTyping ⊢e₁ s) (subContextTyping ⊢e₂ s)
subContextTyping ⊢□ s = ⊢□


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

data Disjoint : List Id → List Id → Set where
  DisHere : ∀ {ys} → Disjoint [] ys
  DisThere : ∀ {x xs ys} → x ∉ ys → Disjoint xs ys → Disjoint (x ∷ xs) ys

disjoint-[] : ∀ {a} → Disjoint a []
disjoint-[] {[]} = DisHere
disjoint-[] {x ∷ a} = DisThere (λ ()) disjoint-[]

disjoint-sym : ∀ {a b} → Disjoint a b → Disjoint b a
disjoint-sym DisHere = disjoint-[]
disjoint-sym (DisThere x∉ d) = let z = disjoint-sym d in {!!}

disjointWeaken : ∀ {x xs ys} → Disjoint (x ∷ xs) ys → Disjoint xs ys
disjointWeaken (DisThere _ d) = d

-- notInExtend : ∀ {Γ αs x σ} → NotInContext αs Γ → Disjoint αs (freeVarsTS σ) → NotInContext αs (Γ , x ⦂ σ)
-- notInExtend NotHere _ = NotHere
-- notInExtend (NotThere {α = α} ∉σ notin) (DisThere ∉Γ p) = NotThere (∉-++⁺ˡ {α} ∉σ ∉Γ) (notInExtend notin p)

-- absHelper : ∀ {Γ z e x σ} → z ∈ FV e → Γ ⦅ z ⦆ ≡ Γ , x' ⦂ σ ⦅ z ⦆

-- chooses a substitution such that FTV Γ ∩ subRegion s ∩ αs ≡ ∅
absSubChoose : ∀ {Γ x' x αs τ₁ τ e₁ τ₂}
             → Γ , x' ⦂ τ₁ , x ⦂ VV αs τ ⊢ e₁ ⦂ τ₂
             → ∃[ s ] (Disjoint (FTVC Γ) αs ×
                       Disjoint (subRegion (BJS.to s)) αs ×
                       Disjoint (subRegion (BJS.to s)) (FTVC Γ))
absSubChoose ⊢e₁ = ⟨ {!!} , {!!} ⟩

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
                 
subst {x = y} ⊢e (⊢· e e') p = ⊢· (subst ⊢e e p) (subst ⊢e e' p)
subst {x = y} ⊢e ⊢□ _ = ⊢□
subst {x = y} ⊢e (⊢⟦⟧ ⊢e') p = ⊢⟦⟧ (subst ⊢e ⊢e' p)
subst {x = y} ⊢e (⊢>>= ⊢m ⊢f) p = ⊢>>= (subst ⊢e ⊢m p) (subst ⊢e ⊢f p)

-- variables renamed to match wright & felleisen
subst {x = y} ⊢v (⊢lt {x = x} ⊢e' ⊢e'') p with x ≟ y
... | yes refl = ⊢lt (subst ⊢v ⊢e' p) {!!}
... | no x≢y = ⊢lt (subst ⊢v ⊢e' p)
                   (let swp = (swap x≢y ⊢e'')
                        s = {!!}
                        in {!!})

  
preservation : ∀ {e e' τ}
             → ∅ ⊢ e ⦂ τ
             → e ↝ e'
               ----------
             → ∅ ⊢ e' ⦂ τ
preservation (⊢· ⊢e ⊢e') (ξ-·₁ e↝e') = ⊢· (preservation ⊢e e↝e') ⊢e'
preservation (⊢· ⊢e ⊢e') (ξ-·₂ e↝e') = ⊢· ⊢e (preservation ⊢e' e↝e')
preservation (⊢· (⊢ƛ ⊢e) ⊢e') (β-ƛ _) = subst ⊢e' ⊢e DisHere
preservation (⊢>>= ⊢m ⊢f) (ξ->>= m↝m') = ⊢>>= (preservation ⊢m m↝m') ⊢f
preservation (⊢>>= (⊢⟦⟧ ⊢e) ⊢f) β->>= = ⊢· ⊢f ⊢e
preservation (⊢lt {τ' = τ'} ⊢e' ⊢e) β-lt rewrite toVVClose τ' = subst ⊢e' ⊢e disjoint-[]

