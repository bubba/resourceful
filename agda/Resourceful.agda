module Resourceful where

open import Data.Empty using (⊥; ⊥-elim)

open import Data.List using (List; _∷_; [_]; []; foldl; filter; any; _++_)
open import Data.List.Membership.Setoid.Properties


open import Data.String using (String; _≟_; _==_; _≈_)
open import Data.String.Properties using (≡-setoid)

import Data.List.Relation.Binary.Subset.Setoid as Subset
open module SubsetString = Subset ≡-setoid

open import Data.List.Relation.Unary.Any using (Any; here; there)

import Data.List.Membership.Setoid as Membership
open module MembershipString = Membership ≡-setoid using (_∈_; find)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Pred; Decidable)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Agda.Builtin.Bool
open import Data.Bool using (not)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

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

  β-lt : ∀ {x e e'}
         -- TODO: should (Value e')?
         ----------
       → (lt x ⇐ e' in' e) ↝ e [ x := e' ]

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


-- Helper for writing type schemes in the form of
-- ∀ αs . τ
VV : List Id → Type → TypeScheme
VV (α ∷ αs) τ = V α · (VV αs τ)
VV [] τ = ` τ


unwrapTS : TypeScheme → List Id
unwrapTS (V α · σ) = α ∷ unwrapTS σ
unwrapTS (` _) = []

TStype : TypeScheme → Type
TStype (V _ · σ) = TStype σ
TStype (` τ) = τ

TSvars : TypeScheme → List Id
TSvars (V α · σ) = α ∷ TSvars σ
TSvars (` τ) = []

extractVV≡ : ∀ {αs τ} → TStype (VV αs τ) ≡ τ
extractVV≡ {[]} {τ} = refl
extractVV≡ {α ∷ αs} {τ} = extractVV≡ {αs}

TSvars≡ : ∀ {αs τ} → TSvars (VV αs τ) ≡ αs
TSvars≡ {[]} = refl
TSvars≡ {α ∷ αs} = cong (_∷_ α) TSvars≡

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

subDomain : Substitution → List Id
subDomain SZ = []
subDomain (SS id _ s) = id ∷ subDomain s

record BJS : Set where
  field
    to : Substitution
    from : Substitution
    from-to : ∀ {σ} → sub from (sub to σ) ≡ σ
    to-from : ∀ {σ} → sub to (sub from σ) ≡ σ



subT : Substitution → Type → Type
subT s (a ⇒ b) = subT s a ⇒ subT s b
subT s (IO σ τ) = IO σ (subT s τ)
subT s □ = □
subT SZ (` α) = (` α)
subT (SS id τ s) (` α) with id ≟ α
...  | yes _ = subT s τ
...  | no  _ = subT s (` α)

_ : subT (SS "a" □ SZ) (` "a" ⇒ ` "b") ≡ □ ⇒ ` "b"
_ = refl

_ : (sub (SS "a" □ SZ) (` (` "a"))) ≡ ` (` "a")
_ = refl

_ : (sub (SS "b" □ SZ) (V "b" · (` (` "b" ⇒ ` "b")))) ≡ ` (□ ⇒ □)
_ = refl

_ : SZ ∘ (SS "b" □ SZ) ≡ (SS "b" □ SZ)
_ = refl

infixr 3 _>_
data _>_ : TypeScheme → Type → Set where
  General : ∀ {σ τ}
    → (s : Substitution)
    → subDomain s ≡ TSvars σ
    → subT s (TStype σ) ≡ τ
    -------------------
    → σ > τ

data _≥_ : (σ : TypeScheme) → (σ' : TypeScheme) → Set where
  General : ∀ {σ σ'}
            → (∀ {τ} → σ' > τ → σ > τ)
            -------------------
            → σ ≥ σ'

-- data _⇒_⇒_ : (σ : TypeScheme) → (s : Substitution) → (σ' : TypeScheme) → Set where
--  _ : ∀ {αs τ βs τ'}
--      → length αs ≡ length βs
--      -- → αᵢ → βᵢ is bijection?
--      → no β in typevars of of Sₒ
--      → 

-- _ : V "a" · (` (` "a" ⇒ ` "a")) > ` (□ ⇒ □)
-- _ = General (SS "a" □ SZ) refl

-- infixr 3 _>_
-- data _>_ : (σ : TypeScheme) → (σ' : TypeScheme) → Set where
--   General : ∀ {σ σ'}
--     → (s : Substitution)
--     → ((sub s σ) ≡ σ')
--     -------------------
--     → σ > σ'

-- _ : V "a" · (` (` "a" ⇒ ` "a")) > ` (□ ⇒ □)
-- _ = General (SS "a" □ SZ) refl

-- asdf1 : ∀ {s} → SZ ∘ s ≡ s
-- asdf1 {SZ} = refl
-- asdf1 {SS i τ s} = cong (SS i τ) asdf1

-- asdf2 : ∀ {s} → s ∘ SZ ≡ s
-- asdf2 = refl

-- asdf3 : ∀ {σ} → sub SZ σ ≡ σ
-- asdf3 = refl

-- asdf4 : ∀ (σ i τ s) → sub (SS i τ s) σ ≡ sub s (substitute i τ σ)
-- asdf4 σ i τ s = refl

-- asdf : ∀ (s1 s2 σ) → sub (s2 ∘ s1) σ ≡ sub s2 (sub s1 σ)
-- asdf SZ s2 σ rewrite asdf2 {s2} = refl
-- asdf (SS i τ s1) s2 σ = asdf s1 s2 (substitute i τ σ)


-- >trans : ∀ {σ σ' σ''} → σ > σ' → σ' > σ'' → σ > σ''
-- >trans {σ} {σ'} (General s1 s1p) (General s2 s2p)  = General (s2 ∘ s1) (trans (trans (asdf s1 s2 σ) a) s2p)
--   where a : sub s2 (sub s1 σ) ≡ sub s2 σ'
--         a = cong (sub s2) s1p

>trans : ∀ {σ σ' τ} → σ ≥ σ' → σ' > τ → σ > τ
>trans {σ} {σ'} (General f) σ'>τ = f σ'>τ

-- >refl : ∀ {σ} → σ > σ
-- >refl = General SZ refl

infixl 5 _,_⦂_
data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → TypeScheme → Context

data Maybe : (A : Set) → Set where
  Just : ∀ {A} → (x : A) → Maybe A
  Nothing : ∀ {A} → Maybe A

infixl 5 _⦅_⦆
_⦅_⦆ : Context → Id → Maybe TypeScheme
∅ ⦅ x ⦆ = Nothing
(Γ , y ⦂ σ) ⦅ x ⦆ with x ≟ y
... | yes refl = Just σ
... | no x≢y = Γ ⦅ x ⦆


subC : Substitution → Context → Context
subC s ∅ = ∅
subC s (Γ , x ⦂ σ) = (subC s Γ) , x ⦂ (sub s σ)

_ : subC (SS "α" □ SZ) (∅ , "x" ⦂ V "α" · (` (` "α" ⇒ ` "α"))) ≡ ∅ , "x" ⦂ ` (□ ⇒ □)
_ = refl

infix 5 _/_
_/_ : List Id → List Id → List Id
-- xs / [] = xs
-- xs / (y ∷ ys) = (filter (λ x → ¬? (x ≟ y)) xs) / ys
(x ∷ xs) / ys with any (λ a → a == x) ys
...  | true = xs / ys
...  | false = x ∷ (xs / ys)
[] / ys = []

/-empty : ∀ {a : List Id} → a / [] ≡ a
/-empty {[]} = refl
/-empty {x ∷ xs} = cong (_∷_ x) /-empty

filter-[] : ∀ {y} → filter (λ x → ¬? (x ≟ y)) [] ≡ []
filter-[] = refl

/-∈ : ∀ {xs ys v} → v ∈ xs / ys → v ∈ xs
/-∈ {a ∷ as} {bs} {z} z∈as/b with any (λ x → x == a) bs
... | true = there (/-∈ {as} {bs} {z} z∈as/b)
/-∈ {a ∷ as} {bs} {z} (here z≈a) | false = here z≈a
/-∈ {a ∷ as} {bs} {z} (there z∈as/b) | false = there (/-∈ {as} {bs} {z} z∈as/b)

/-∈≢ : ∀ {v xs y} → v ∈ xs → v ≢ y → v ∈ xs / [ y ]
/-∈≢ {v} {x ∷ xs} {y} (here refl) v≢y with y ≟ x
... | yes y≡x = ⊥-elim (v≢y (sym y≡x))
... | no y≢x = here refl
/-∈≢ {v} {x ∷ xs} {y} (there v∈xs) v≢y with y ≟ x
... | yes y≡x = /-∈≢ v∈xs v≢y
... | no y≢x = there (/-∈≢ v∈xs v≢y)

/-⊆ : ∀ {a b} → a / b ⊆ a
/-⊆ {a} {b} {x} = /-∈ {a} {b} {x}

⊆-id : ∀ {a} → a ⊆ a
⊆-id x = x

_ : ("b" ∷ [ "a" ]) / [ "b" ] ≡ [ "a" ]
_ = refl

_ : ("b" ∷ [ "a" ]) / [ "a" ] ⊆ "b" ∷ [ "a" ]
_ = λ{ (here x) → here x;
       (there ())}

-- Free variables
FV : Term → List Id
FV (` x) = [ x ]
FV (ƛ x ⇒ e) = FV e / [ x ]
FV (e₁ · e₂) = FV e₁ ++ FV e₂
FV (lt x ⇐ e in' e') = FV e ++ (FV e' / [ x ])
FV ⟦ e ⟧ = FV e
FV (e >>= e') = FV e ++ FV e'
FV □ = []

-- Free *type* variables, types
FTVT : Type → List Id
FTVT (` α) = [ α ]
FTVT □ = []
FTVT (a ⇒ b) = FTVT a ++ FTVT b
FTVT (IO σ τ) = FTVT τ

subRegion : Substitution → List Id
subRegion SZ = []
subRegion (SS α τ s) = FTVT τ ++ subRegion s


-- Free *type* variables
FTV : TypeScheme → List Id
FTV (V α · σ) = FTV σ / [ α ]
FTV (` τ) = FTVT τ

-- Free *type* variables in a context
FTVC : Context → List Id
FTVC ∅ = []
FTVC (c , x ⦂ σ) = FTVC c ++ FTV σ

-- close : Context → Type → TypeScheme
-- close Γ τ = foldl (λ acc x → V x · acc) (` τ) (freeVars τ / FTVC Γ)

close : Context → Type → TypeScheme
close Γ τ = VV (FTVT τ / FTVC Γ) τ
-- ... | [] = ` τ
-- ... | α ∷ αs =  VV


toVV : (σ : TypeScheme) → ∃[ αs ] ( ∃[ τ ] (σ ≡ VV αs τ) )
toVV (V α · σ) with toVV σ
... | ⟨ αs , ⟨ τ , refl ⟩ ⟩ = ⟨ α ∷ αs , ⟨ τ , refl ⟩ ⟩
toVV (` τ) = ⟨ [] , ⟨ τ , refl ⟩ ⟩

toVVClose : (τ : Type) → (close ∅ τ ≡ VV (FTVT τ) τ)
toVVClose τ =
  begin
    VV (FTVT τ / FTVC ∅) τ
  ≡⟨⟩
    VV (FTVT τ / []) τ
  ≡⟨ cong (λ αs → VV αs τ) (/-empty {FTVT τ}) ⟩
    VV (FTVT τ) τ
  ∎

-- need to show that FTV (sub s σ) = FTV σ / s

-- postulate freeVarsSub : ∀ {s σ} → FTV (sub s σ) ⊆ FTV σ
-- freeVarsSub {s} {` x} = {!!} -- if σ is V then /-⊆ {FTV σ} {[ α ]}
                           -- if σis τ then ⊆-id

[]⊆ : ∀ {a} → [] ⊆ a
[]⊆ = λ ()


-- free variables in σ get used up in instantiating to σ'
-- ≥freeVars : ∀ {σ σ'} → σ ≥ σ' → FTV σ' ⊆ FTV σ
-- ≥freeVars {σ'} {σ} σ≥σ' x∈ with FTV σ
-- ≥freeVars {σ'} {σ} σ≥σ' () | []
-- ≥freeVars {σ'} {σ} σ≥σ' (there x∈) | x ∷ z = {!!}

postulate close> : ∀ {Γ x σ σ' τ}
                 → σ ≥ σ'
                 → close (Γ , x ⦂ σ) τ ≡ close (Γ , x ⦂ σ') τ
-- close> {Γ} {x} {σ} {σ'} (General f) = {!!}
--   where freeVarsLess : FTVC (Γ , x ⦂ σ') ⊆ FTVC (Γ , x ⦂ σ)
--         freeVarsLess α = {!!}

--         g : FTV σ' ⊆ FTV σ
--         g α∈σ' = {!!}
       

_ : FTVC (∅ , "x" ⦂ ` (` "a")) ≡ [ "a" ]
_ = refl

_ : FTVT (` "a" ⇒ ` "b") / FTVC (∅ , "x" ⦂ ` (` "a")) ≡ [ "b" ]
_ = refl

_ : close (∅ , "x" ⦂ ` (` "a")) (` "a" ⇒ ` "b") ≡ V "b" · (` (` "a" ⇒ ` "b"))
_ = refl

_ : close ∅ □ ≡ ` □
_ = refl

-- close∅ : ∀ {τ : Type} → close ∅ τ ≡ freeVars τ
-- close∅ {τ} =
--   begin
--     close ∅ τ
--   ≡⟨⟩
--     foldl (λ acc x → V x · acc) (` τ) (freeVars τ / FTVC ∅)
--   ≡⟨⟩
--     foldl (λ acc x → V x · acc) (` τ) (freeVars τ / [])
--   ≡⟨ cong (foldl (λ acc x → V x · acc) (` τ)) (/-empty {freeVars τ}) ⟩
--     foldl (λ acc x → V x · acc) (` τ) (freeVars τ)
--   ≡⟨⟩
--     {!!}


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

-- This is a syntax directed type system, so typing judgements return
-- *types*, not type schemes.

infix 4 _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢` : ∀ {Γ x σ τ}
     → x ⦂ σ ∈ Γ
     → σ > τ
       ---------
     → Γ ⊢ ` x ⦂ τ

  ⊢ƛ : ∀ {Γ x τ' τ e}
     → Γ , x ⦂ ` τ' ⊢ e ⦂ τ
       ------------------
     → Γ ⊢ ƛ x ⇒ e ⦂ (τ' ⇒ τ)

  ⊢· : ∀ {Γ e e' τ τ'}
     → Γ ⊢ e ⦂ τ' ⇒ τ
     → Γ ⊢ e' ⦂ τ'
       --------------
     → Γ ⊢ e · e' ⦂ τ

  ⊢lt : ∀ {Γ e e' τ τ' x}
      → Γ ⊢ e' ⦂ τ'
      → Γ , x ⦂ close Γ τ' ⊢ e ⦂ τ
        ----------------------------
      → Γ ⊢ lt x ⇐ e' in' e ⦂ τ

  ⊢⟦⟧ : ∀ {Γ e τ σ}
      → Γ ⊢ e ⦂ τ
        ----------------
      → Γ ⊢ ⟦ e ⟧ ⦂ IO σ τ
  
  ⊢>>= : ∀ {Γ e e' τ τ' σ}
       → Γ ⊢ e ⦂ (IO σ τ')
       → Γ ⊢ e' ⦂ (τ' ⇒ IO σ τ)
         -------------------
       → Γ ⊢ e >>= e' ⦂ IO σ τ

  ⊢□ : ∀ {Γ}
       
       ---------
     → Γ ⊢ □ ⦂ □

_ : ∅ ⊢ ƛ "x" ⇒ □ ⦂ ( □ ⇒ □ )
_ = ⊢ƛ ⊢□

_ : ∅ , "x" ⦂ (V "x" · (` (` "x" ⇒ ` "x"))) ⊢ (` "x" · □) ⦂ □
_ = ⊢· (⊢` Z (General (SS "x" □ SZ) refl refl)) ⊢□

-- _ : ∅ ⊢ ƛ "x" ⇒ (` "x") ⦂ ( ` "α" ⇒ ` "α" )
-- _ = ⊢ƛ (⊢` Z >refl)

postulate roundtripSub : ∀ {Γ x σ e τ}
               → (s : BJS)
               → subC (BJS.from s) (Γ , x ⦂ sub (BJS.to s) σ) ⊢ 
                      e ⦂ subT (BJS.from s) (subT (BJS.to s) τ)
               → Γ , x ⦂ σ ⊢ e ⦂ τ
