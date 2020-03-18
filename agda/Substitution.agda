module Substitution where

open import Grammar
open import Data.List using (List; _∷_; [])
open import Data.String using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (yes; no)

subType : Id → Type → Type → Type
subType id τ (` α) with id ≟ α
...  | yes _ = τ
...  | no  _ = ` α
subType id τ (a ⇒ b) = subType id τ a ⇒ subType id τ b
subType id τ (IO σ τ') = IO σ (subType id τ τ')
subType id τ (a × b) = subType id τ a × subType id τ b
subType _ _ □ = □


data Substitution : Set where
  SZ : Substitution
  SS : Id → Type → Substitution → Substitution

infix 5 _∘ˢ_
_∘ˢ_ : Substitution → Substitution → Substitution
s ∘ˢ SZ = s
s1 ∘ˢ(SS i τ s2) = SS i τ (s1 ∘ˢ s2)

-- susbtitutes ALL type variables in a type
subT : Substitution → Type → Type
subT s (a ⇒ b) = subT s a ⇒ subT s b
subT s (IO σ τ) = IO σ (subT s τ)
subT s (a × b) = subT s a × subT s b
subT s □ = □
subT SZ (` α) = (` α)
subT (SS id τ s) (` α) with id ≟ α
...  | yes _ = subT s τ
...  | no  _ = subT s (` α)

-- substitutes the FREE type variables
sub : Substitution → TypeScheme → TypeScheme
sub SZ σ = σ
sub s@(SS id τ si) (V α · σ) with α ≟ id
... | yes refl = (V α · sub si σ)
... | no α≢id = (V α · sub s σ)
sub s@(SS id τ si) (` τ') = ` (subT s τ')

-- substitutes the BOUND type variables
inst : Substitution → TypeScheme → TypeScheme
inst SZ σ = σ
inst (SS id type xs) σ = inst xs (substitute id type σ)
  where
    
  instantiate : Id → Type → TypeScheme → TypeScheme
  instantiate id τ (V α · τ') = (V α · instantiate id τ τ')
  instantiate id τ (` τ') = ` (subType id τ τ')

  substitute : Id → Type → TypeScheme → TypeScheme
  substitute id τ (V α · σ) with id ≟ α
  ...  | yes _ = instantiate id τ σ
  ...  | no _  = V α · (substitute id τ σ)
  substitute id τ (` τ') = ` τ'

-- substitutes the FREE type variables in the context's typescheme
subC : Substitution → Context → Context
subC s ∅ = ∅
subC s (Γ , x ⦂ σ) = (subC s Γ) , x ⦂ (sub s σ)

_ : subC (SS "α" □ SZ) (∅ , "x" ⦂ V "α" · (` (` "α" ⇒ ` "α"))) ≡ ∅ , "x" ⦂ V "α" · (` (` "α" ⇒ ` "α"))
_ = refl

subDomain : Substitution → List Id
subDomain SZ = []
subDomain (SS id _ s) = id ∷ subDomain s

-- Some properties

subTSZ : ∀ {τ} → subT SZ τ ≡ τ
subTSZ {` x} = refl
subTSZ {τ ⇒ τ'} rewrite subTSZ {τ} | subTSZ {τ'} = refl
subTSZ {IO x τ} = cong (IO x) subTSZ
subTSZ {□} = refl
subTSZ {a × b} rewrite subTSZ {a} | subTSZ {b} = refl

subCSZ : ∀ {Γ} → subC SZ Γ ≡ Γ
subCSZ {∅} = refl
subCSZ {Γ , x ⦂ σ} = cong (λ z → z , x ⦂ σ) subCSZ

SZ∘ˢ : ∀ {s} → SZ ∘ˢ s ≡ s
SZ∘ˢ {SZ} = refl
SZ∘ˢ {SS i τ s} = cong (SS i τ) SZ∘ˢ

subT≡sub : ∀ {τ} → (s : Substitution) → sub s (` τ) ≡ ` (subT s τ)
subT≡sub {τ} SZ =
  begin
    sub SZ (` τ)
  ≡⟨⟩
    (` τ)
  ≡⟨ cong (`_) (sym (subTSZ {τ})) ⟩
    (` (subT SZ τ))
  ∎
subT≡sub {τ} (SS id τ' si) = refl

-- Bijective substitutions

record BJS : Set where
  field
    to : Substitution
    from : Substitution
    from-to : ∀ {σ} → sub from (sub to σ) ≡ σ
    to-from : ∀ {σ} → sub to (sub from σ) ≡ σ



_ : subT (SS "a" □ SZ) (` "a" ⇒ ` "b") ≡ □ ⇒ ` "b"
_ = refl

_ : (sub (SS "a" □ SZ) (` (` "a"))) ≡ ` □
_ = refl

_ : (inst (SS "a" □ SZ) (` (` "a"))) ≡ ` (` "a")
_ = refl

_ : (inst (SS "b" □ SZ) (V "b" · (` (` "b" ⇒ ` "b")))) ≡ ` (□ ⇒ □)
_ = refl

_ : SZ ∘ˢ (SS "b" □ SZ) ≡ (SS "b" □ SZ)
_ = refl

infixr 3 _>_
data _>_ : TypeScheme → Type → Set where
  Inst : ∀ {σ τ}
    → (s : Substitution)
    → subDomain s ≡ TSvars σ
    → subT s (TStype σ) ≡ τ
    -------------------
    → σ > τ

data _≥_ : (σ : TypeScheme) → (σ' : TypeScheme) → Set where
  Inst : ∀ {σ σ'}
       → (∀ {τ} → σ' > τ → σ > τ)
         -------------------
       → σ ≥ σ'

_ : V "a" · (` (` "a" ⇒ ` "a")) > (□ ⇒ □)
_ = Inst (SS "a" □ SZ) refl refl


-- inst∘ : ∀ (s1 s2 σ) → inst (s2 ∘ s1) σ ≡ inst s2 (sub s1 σ)
-- inst∘ SZ s2 σ = refl
-- inst∘ (SS i τ s1) s2 σ = inst∘ {!!} s2 σ

-- ≥trans : ∀ {σ σ' σ''} → σ ≥ σ' → σ' ≥ σ'' → σ ≥ σ''
-- ≥trans {σ} {σ'} (Inst s1 s1p) (Inst s2 s2p) = Inst (s2 ∘ s1) (trans (trans (asdf s1 s2 σ) a) s2p)
--   where a : sub s2 (sub s1 σ) ≡ sub s2 σ'
--         a = cong (sub s2) s1p

>trans : ∀ {σ σ' τ} → σ ≥ σ' → σ' > τ → σ > τ
>trans {σ} {σ'} (Inst f) σ'>τ = f σ'>τ

≥refl : ∀ {σ} → σ ≥ σ
≥refl = Inst λ x → x

>self : ∀ {τ} → ` τ > τ
>self = Inst SZ refl subTSZ
