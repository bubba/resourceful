module Resourceful where

open import Data.List using (List; _∷_; [_]; []; foldl; any; _++_)
open import Data.List.Membership.DecSetoid
open import Data.String using (String; _≟_; _==_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (yes; no)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Agda.Builtin.Bool

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 9 `_
infix 7 _·_
infix 4 lt_⇐_in'_
infix 5 _>>=_

data Term : Set where
  `_    : Id → Term
  ƛ_⇒_  : Id → Term → Term
  _·_   : Term → Term → Term
  lt_⇐_in'_ : Id → Term → Term → Term
  ⟦_⟧   : Term → Term
  _>>=_ : Term → Term → Term
  □     : Term

data Value : Term → Set where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)
  V-⟦⟧ : ∀ {e} → Value (⟦ e ⟧)
  V-□ : Value □

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := z ] with x ≟ y
... | yes _ = z
... | no  _ = ` x
(ƛ x ⇒ N) [ y := z ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := z ]
(e · e') [ y := z ] = e [ y := z ] · e' [ y := z ]
(lt x ⇐ e' in' e) [ y := z ] with x ≟ y
... | yes _ = lt x ⇐ (e' [ y := z ]) in' e
... | no  _ = lt x ⇐ (e' [ y := z ]) in' (e [ y := z ])
⟦ e ⟧ [ y := z ] = ⟦ e [ y := z ] ⟧
(m >>= f) [ y := z ] = m [ y := z ] >>= f [ y := z ]
□ [ _ := _ ] = □

_ : (ƛ "a" ⇒ ` "b") [ "b" := ` "c" ] ≡ ƛ "a" ⇒ ` "c"
_ = refl

_ : (ƛ "a" ⇒ ` "a") [ "a" := ` "b" ] ≡ ƛ "a" ⇒ ` "a"
_ = refl

_ : (lt "x" ⇐ ` "x" in' ` "x") [ "x" := □ ] ≡ (lt "x" ⇐ □ in' ` "x")
_ = refl

_ : (lt "x" ⇐ ` "y" in' ` "y") [ "y" := □ ] ≡ (lt "x" ⇐ □ in' □)
_ = refl

infix 4 _↝_

data _↝_ : Term → Term → Set where
  ξ-·₁ : ∀ {e₁ e₂ e₁'}
       → e₁ ↝ e₁'
         ------------------
       → e₁ · e₂ ↝ e₁' · e₂
       
  ξ-·₂ : ∀ {e₁ e₂ e₂'}
       → e₂ ↝ e₂'
         ------------------
       → e₁ · e₂ ↝ e₁ · e₂'

  β-ƛ : ∀ {x e e'}
      → Value e'
        ------------------
      → (ƛ x ⇒ e) · e' ↝ e [ x := e' ]

  ξ->>= : ∀ {e₁ e₂ e₁'}
        → e₁ ↝ e₁'
          ----------------------
        → e₁ >>= e₂ ↝ e₁' >>= e₂

  β->>= : ∀ {v e}
          -------------------
        → ⟦ v ⟧ >>= e ↝ e · v

data Resource : Set where
  Net : Resource
  File : Resource

infixr 9 _∪_
data Heap : Set where
  `_ : Resource → Heap
  _∪_ : Resource → Resource → Heap

infixr 7 _⇒_
data Type : Set where
  `_ : Id → Type
  _⇒_ : Type → Type → Type
  IO : Heap → Type → Type
  □ : Type

data TypeScheme : Set where
  V_·_ : Id → TypeScheme → TypeScheme
  `_ : Type → TypeScheme

subType : Id → Type → Type → Type
subType id τ (` α) with id ≟ α
...  | yes _ = τ
...  | no  _ = ` α
subType id τ (a ⇒ b) = subType id τ a ⇒ subType id τ b
subType id τ (IO σ τ') = IO σ (subType id τ τ')
subType _ _ □ = □

instantiate : Id → Type → TypeScheme → TypeScheme
instantiate id τ (V α · τ') = (V α · instantiate id τ τ')
instantiate id τ (` τ') = ` (subType id τ τ')

substitute : Id → Type → TypeScheme → TypeScheme
substitute id τ (V α · σ) with id ≟ α
...  | yes _ = instantiate id τ σ
...  | no _  = V α · (substitute id τ σ)
substitute id τ (` τ') = ` τ'


data Substitution : Set where
  SZ : Substitution
  SS : Id → Type → Substitution → Substitution

infix 5 _∘_
_∘_ : Substitution → Substitution → Substitution
s ∘ SZ = s
s1 ∘ (SS i τ s2) = SS i τ (s1 ∘ s2)
  
sub : Substitution → TypeScheme → TypeScheme
sub SZ σ = σ
sub (SS id type xs) σ = sub xs (substitute id type σ)

_ : (sub (SS "a" □ SZ) (` (` "a"))) ≡ ` (` "a")
_ = refl

_ : (sub (SS "b" □ SZ) (V "b" · (` (` "b" ⇒ ` "b")))) ≡ ` (□ ⇒ □)
_ = refl

_ : SZ ∘ (SS "b" □ SZ) ≡ (SS "b" □ SZ)
_ = refl

infixr 3 _>_
data _>_ : (σ : TypeScheme) → (σ' : TypeScheme) → Set where
  General : ∀ {σ σ'}
    → (s : Substitution)
    → ((sub s σ) ≡ σ')
    -------------------
    → σ > σ'

_ : V "a" · (` (` "a" ⇒ ` "a")) > ` (□ ⇒ □)
_ = General (SS "a" □ SZ) refl

asdf1 : ∀ {s} → SZ ∘ s ≡ s
asdf1 {SZ} = refl
asdf1 {SS i τ s} = cong (SS i τ) asdf1

asdf2 : ∀ {s} → s ∘ SZ ≡ s
asdf2 {SZ} = refl
asdf2 {SS i τ si} = cong (SS i τ) asdf2

asdf3 : ∀ {σ} → sub SZ σ ≡ σ
asdf3 = refl

asdf4 : ∀ (σ i τ s) → sub (SS i τ s) σ ≡ sub s (substitute i τ σ)
asdf4 σ i τ s = refl

asdf : ∀ (s1 s2 σ) → sub (s2 ∘ s1) σ ≡ sub s2 (sub s1 σ)
asdf SZ s2 σ rewrite asdf2 {s2} = refl
asdf (SS i τ s1) s2 σ = asdf s1 s2 (substitute i τ σ)


>trans : ∀ {σ σ' σ''} → σ > σ' → σ' > σ'' → σ > σ''
>trans {σ} {σ'} (General s1 s1p) (General s2 s2p)  = General (s2 ∘ s1) (trans (trans (asdf s1 s2 σ) a) s2p)
  where a : sub s2 (sub s1 σ) ≡ sub s2 σ'
        a = cong (sub s2) s1p


infixl 5 _,_⦂_
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → TypeScheme → Context

infix 5 _/_
_/_ : List Id → List Id → List Id
(x ∷ xs) / ys with any (\a -> a == x) ys
...  | true = xs / ys
...  | false = x ∷ (xs / ys)
[] / ys = []

_ : ("b" ∷ [ "a" ]) / [ "b" ] ≡ [ "a" ]
_ = refl

freeVars : TypeScheme → List Id
freeVars (V α · σ) = freeVars σ / [ α ]
freeVars (` (` α)) = [ α ]
freeVars (` □) = []
freeVars (` (a ⇒ b)) = freeVars (` a) ++ freeVars (` b)
freeVars (` (IO σ τ)) = freeVars (` τ)

freeVarsC : Context → List Id
freeVarsC ∅ = []
freeVarsC (c , x ⦂ σ) = freeVarsC c ++ freeVars σ

close : Context → TypeScheme → TypeScheme
close Γ σ = foldl (λ acc x → V x · acc) σ (freeVars σ / freeVarsC Γ)

_ : freeVarsC (∅ , "x" ⦂ ` (` "a")) ≡ [ "a" ]
_ = refl

_ : freeVars (` (` "a" ⇒ ` "b")) / freeVarsC (∅ , "x" ⦂ ` (` "a")) ≡ [ "b" ]
_ = refl

_ : close (∅ , "x" ⦂ ` (` "a")) (` (` "a" ⇒ ` "b")) ≡ V "b" · (` (` "a" ⇒ ` "b"))
_ = refl

infix 4 _⦂_∈_

data _⦂_∈_ : Id → TypeScheme → Context → Set where
  Z : ∀ {Γ x τ}
      -----------------
    → x ⦂ τ ∈ Γ , x ⦂ τ
    
  S : ∀ {Γ x y τ τ'}
    → x ⦂ τ ∈ Γ
    → x ≢ y
      -----------------
    → x ⦂ τ ∈ Γ , y ⦂ τ'

infix 4 _⊢_⦂_
data _⊢_⦂_ : Context → Term → TypeScheme → Set where

  ⊢` : ∀ {Γ x τ τ'}
     → x ⦂ τ' ∈ Γ
     → τ' > τ
       ---------
     → Γ ⊢ ` x ⦂ τ

  ⊢ƛ : ∀ {Γ x τ' e τ}
     → Γ , x ⦂ ` τ' ⊢ e ⦂ ` τ
       ------------------
     → Γ ⊢ ƛ x ⇒ e ⦂ ` (τ' ⇒ τ)

  ⊢· : ∀ {Γ e e' τ τ'}
     → Γ ⊢ e ⦂ ` ( τ' ⇒ τ )
     → Γ ⊢ e' ⦂ ` τ'
       --------------
     → Γ ⊢ e · e' ⦂ ` τ

  ⊢lt : ∀ {Γ e e' τ τ' x}
      → Γ ⊢ e' ⦂ τ'
      → Γ , x ⦂ close Γ τ' ⊢ e' ⦂ τ
        ----------------------------
      → Γ ⊢ lt x ⇐ e in' e' ⦂ τ

  ⊢⟦⟧ : ∀ {Γ e τ σ}
      → Γ ⊢ e ⦂ ` τ
        ----------------
      → Γ ⊢ ⟦ e ⟧ ⦂ ` IO σ τ
  
  ⊢>>= : ∀ {Γ e e' τ τ' σ}
       → Γ ⊢ e ⦂ ` (IO σ τ')
       → Γ ⊢ e' ⦂ ` (τ' ⇒ IO σ τ)
         -------------------
       → Γ ⊢ e >>= e' ⦂ ` IO σ τ

  ⊢□ : ∀ {Γ}
       
       ---------
     → Γ ⊢ □ ⦂ ` □

_ : ∅ ⊢ ƛ "x" ⇒ □ ⦂ ` ( □ ⇒ □ )
_ = ⊢ƛ ⊢□

_ : ∅ , "x" ⦂ (V "x" · (` (` "x" ⇒ ` "x"))) ⊢ (` "x" · □) ⦂ ` □
_ = ⊢· (⊢` Z (General (SS "x" □ SZ) refl)) ⊢□
