module Resourceful.Grammar where

open import Data.List using (List; _∷_; [])
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 9 `_
infix 7 _·_
infix 4 lt_⇐_in'_
infix 4 _>>=_
infix 5 _×_
infix 5 _⋎_
infix 6 ⟦_⟧
infix 6 use

data Resource : Set where
  Net : Resource
  File : Resource
  Database : Resource
  Printer : Resource

data Term : Set where
  `_    : Id → Term
  ƛ_⇒_  : Id → Term → Term
  _·_   : Term → Term → Term
  lt_⇐_in'_ : Id → Term → Term → Term
  ⟦_⟧   : Term → Term
  _>>=_ : Term → Term → Term
  □     : Term
  use : Resource → Term → Term
  _×_ : Term → Term → Term
  π₁ : Term → Term
  π₂ : Term → Term
  _⋎_ : Term → Term → Term
  
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
use r e [ y := z ] = use r (e [ y := z ])
(e × e') [ y := z ] = e [ y := z ] × e' [ y := z ]
(π₁ e) [ y := z ] = π₁ (e [ y := z ])
(π₂ e) [ y := z ] = π₂ (e [ y := z ])
(e₁ ⋎ e₂) [ y := z ] = e₁ [ y := z ] ⋎ e₂ [ y := z ]

_ : (ƛ "a" ⇒ ` "b") [ "b" := ` "c" ] ≡ ƛ "a" ⇒ ` "c"
_ = refl

_ : (ƛ "a" ⇒ ` "a") [ "a" := ` "b" ] ≡ ƛ "a" ⇒ ` "a"
_ = refl

_ : (lt "x" ⇐ ` "x" in' ` "x") [ "x" := □ ] ≡ (lt "x" ⇐ □ in' ` "x")
_ = refl

_ : (lt "x" ⇐ ` "y" in' ` "y") [ "y" := □ ] ≡ (lt "x" ⇐ □ in' □)
_ = refl


infixr 6 _∪_
data Heap : Set where
  World : Heap
  `_ : Resource → Heap
  _∪_ : Heap → Heap → Heap

infixr 7 _⇒_
data Type : Set where
  `_ : Id → Type
  _⇒_ : Type → Type → Type
  IO : Heap → Type → Type
  □ : Type
  _×_ : Type → Type → Type

infixl 6 V_·_
data TypeScheme : Set where
  V_·_ : Id → TypeScheme → TypeScheme
  `_ : Type → TypeScheme


-- Helper for writing type schemes in the form of
-- ∀ αs . τ
VV : List Id → Type → TypeScheme
VV (α ∷ αs) τ = V α · (VV αs τ)
VV [] τ = ` τ

TStype : TypeScheme → Type
TStype (V _ · σ) = TStype σ
TStype (` τ) = τ

TSvars : TypeScheme → List Id
TSvars (V α · σ) = α ∷ TSvars σ
TSvars (` τ) = []

TStype≡ : ∀ {αs τ} → TStype (VV αs τ) ≡ τ
TStype≡ {[]} {τ} = refl
TStype≡ {α ∷ αs} {τ} = TStype≡ {αs}

TSvars≡ : ∀ {αs τ} → TSvars (VV αs τ) ≡ αs
TSvars≡ {[]} = refl
TSvars≡ {α ∷ αs} = cong (_∷_ α) TSvars≡


infixl 5 _,_⦂_
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → TypeScheme → Context
