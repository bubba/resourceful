module Resourceful.Semantics.Static where

open import Resourceful.Grammar public
open import Resourceful.Substitution public
open import Resourceful.Semantics.Dynamic
open import Data.Empty using (⊥; ⊥-elim)

open import Data.List using (List; _∷_; [_]; []; foldl; filter; any; _++_; deduplicate)
open import Data.List.Membership.Setoid.Properties
import Data.List.Relation.Binary.Subset.Setoid as Subset

open import Data.List.Fresh using (List#; _∷#_)
import Data.List.Fresh as Fresh

open import Data.String using (String; _≟_; _==_)
open import Data.String.Properties using (≡-setoid)
open module SubsetString = Subset ≡-setoid

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.List.Relation.Unary.Any using (Any; here; there)

import Data.List.Membership.Setoid as Membership
open module MembershipString = Membership ≡-setoid using (_∈_; _∉_; find)

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Pred; Decidable)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _∎)
open import Agda.Builtin.Bool
open import Data.Bool using (not)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

open import Data.Product
  using (proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩; _×_ to ⟨_×_⟩)

-- Distinct heaps
infix 7 _∩_=∅ 
data _∩_=∅ : Heap → Heap → Set where
  DHZ : ∀ {ρ ρ'}
      → ρ ≢ ρ'
        -------------
      → ` ρ ∩ ` ρ' =∅
    
  DHL : ∀ {ρ ρ₁ ρ₂}
      → ρ ∩ ρ₁ =∅
      → ρ ∩ ρ₂ =∅
      → ρ₁ ∩ ρ₂ =∅
        ----------------
      → ρ ∩ (ρ₁ ∪ ρ₂) =∅

  DHR : ∀ {ρ ρ₁ ρ₂}
      → ρ ∩ ρ₁ =∅
      → ρ ∩ ρ₂ =∅
      → ρ₁ ∩ ρ₂ =∅
        ----------------
      → (ρ₁ ∪ ρ₂) ∩ ρ =∅



distinct-sym : ∀ {ρ ρ'} → ρ ∩ ρ' =∅ → ρ' ∩ ρ =∅
distinct-sym (DHZ x) = DHZ (λ z → x (sym z))
distinct-sym (DHL dist dist₁ dist₂) = DHR dist dist₁ dist₂
distinct-sym (DHR dist dist₁ dist₂) = DHL dist dist₁ dist₂

distinct-∪ˡ : ∀ {a b c}
           → a ∩ b ∪ c =∅
           → a ∩ b =∅
distinct-∪ˡ (DHL a _ _) = a
distinct-∪ˡ (DHR a b c) = let z = distinct-∪ˡ (distinct-sym b )
                              y = distinct-∪ˡ (distinct-sym a)
                         in DHR (distinct-sym y) (distinct-sym z) c

distinct-∪ʳ : ∀ {a b c}
           → a ∩ b ∪ c =∅
           → a ∩ c =∅
distinct-∪ʳ (DHL _ a _) = a
distinct-∪ʳ (DHR a b c) = DHR (distinct-sym (distinct-∪ʳ (distinct-sym a)))
                              (distinct-sym (distinct-∪ʳ (distinct-sym b)))
                              c

worldDistinct : ∀ {ρ} →  ¬ (World ∩ ρ =∅)
worldDistinct (DHL =∅ =∅₁ =∅₂) = worldDistinct =∅₁

_ : ` Net ∩ ` File =∅
_ = DHZ (λ ())

_ : (` Net ∪ ` Printer) ∩ (` Database ∪ ` File) =∅
_ = DHL (DHR (DHZ (λ ())) (DHZ (λ ())) (DHZ (λ ())))
      (DHR (DHZ (λ ())) (DHZ (λ ())) (DHZ (λ ()))) (DHZ (λ ()))


data Ok : Heap → Set where
  OkZ : ∀ {r}
        --------
      → Ok (` r)
  OkS : ∀ {a b}
       → Ok a
       → Ok b
       → a ∩ b =∅
         ----------
       → Ok (a ∪ b)
  OkWorld : --------
            Ok World

       
-- heap subtyping
infix 5 _≥:_
data _≥:_ : Heap → Heap → Set where
  ≥:World : ∀ {ρ} → ρ ≥: World
  ≥:Refl : ∀ {ρ} → ρ ≥: ρ
  ≥:∪ˡ : ∀ {ρ ρ' ρ''}
       → ρ ≥: ρ'
         ------------
       → ρ ≥: ρ' ∪ ρ''
  ≥:∪ʳ : ∀ {ρ ρ' ρ''}
       → ρ ≥: ρ'
         ------------
       → ρ ≥: ρ'' ∪ ρ'

≥:-trans : ∀ {a b c} → a ≥: b → b ≥: c → a ≥: c
≥:-trans a≥:b ≥:World = ≥:World
≥:-trans a≥:b ≥:Refl = a≥:b
≥:-trans a≥:b (≥:∪ˡ b≥:c) = ≥:∪ˡ (≥:-trans a≥:b b≥:c)
≥:-trans a≥:b (≥:∪ʳ b≥:c) = ≥:∪ʳ (≥:-trans a≥:b b≥:c)

_ : ` Net ≥: World
_ = ≥:World
_ : ` Net ≥: ` Net ∪ ` File
_ = ≥:∪ˡ ≥:Refl

∩-≥: : ∀ {ρ ρ' ρ''}
     → ρ ∩ ρ'' =∅    
     → ρ' ≥: ρ''
     → ρ ∩ ρ' =∅
∩-≥: {ρ} a ≥:World = ⊥-elim (worldDistinct {ρ} (distinct-sym a))
∩-≥: a ≥:Refl = a
∩-≥: a (≥:∪ʳ b) = let z = distinct-∪ʳ a
                       in ∩-≥: z b
∩-≥: a (≥:∪ˡ b) = let z = distinct-∪ˡ a in ∩-≥: z b

infix 5 _/_
_/_ : List Id → List Id → List Id
(x ∷ xs) / ys with any (λ a → a == x) ys
...  | true = xs / ys
...  | false = x ∷ (xs / ys)
[] / ys = []

-- xs / [] = xs
-- xs / (y ∷ ys) = (filter (λ x → ¬? (x ≟ y)) xs) / ys

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

∉-++⁺ˡ : ∀ {v xs ys} → v ∉ xs → v ∉ ys → v ∉ xs ++ ys
∉-++⁺ˡ {v} {xs} {ys} ∉xs ∉ys x∈ with ∈-++⁻ (≡-setoid) {v} xs {ys} x∈
... | inj₁ ∈xs = ∉xs ∈xs
... | inj₂ ∈ys = ∉ys ∈ys

∉-++⁻ : ∀ {v xs ys} → v ∉ xs ++ ys → ⟨ v ∉ xs × v ∉ ys ⟩
∉-++⁻ {v} {xs} {ys} ∉xs++ys = ⟨ l , r ⟩
  where
    l : v ∉ xs
    l v∈xs = ∉xs++ys (∈-++⁺ˡ ≡-setoid v∈xs)
    r : v ∉ ys
    r v∈ys = ∉xs++ys (∈-++⁺ʳ ≡-setoid xs v∈ys)

∉-/≢ : ∀ {v xs y} → v ∉ xs / (y ∷ []) → v ≢ y → v ∉ xs
∉-/≢ {v} {xs} {y} v∉xs/y v≢y v∈xs = v∉xs/y (/-∈≢ v∈xs v≢y)

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
FV (use _ e) = FV e
FV (e₁ × e₂) = FV e₁ ++ FV e₂
FV (π₁ e) = FV e
FV (π₂ e) = FV e
FV (e₁ ⋎ e₂) = FV e₁ ++ FV e₂

UList : (A : Set) → Set
UList A = List# A _≢_

-- _++U_ : ∀ {A : Set} → UList A → UList A → UList A
-- a ++U b = {!!}

-- Free *type* variables, types
-- TODO: change list with a fresh list with ≢ relation
FTVT : Type → List Id
FTVT (` α) = α ∷ []
FTVT □ = []
FTVT (a ⇒ b) = deduplicate _≟_ (FTVT a ++ FTVT b)
FTVT (IO σ τ) = FTVT τ
FTVT (a × b) = deduplicate _≟_ (FTVT a ++ FTVT b)

subRegion : Substitution → List Id
subRegion SZ = []
subRegion (SS α τ s) = FTVT τ ++ subRegion s

-- _/#_ : ∀ {a r} {A : Set a} {R : Rel A r} → List# A R → List# A R → List# A R

-- Free *type* variables
FTV : TypeScheme → List Id
FTV (V α · σ) = FTV σ / [ α ]
FTV (` τ) = FTVT τ

-- Free *type* variables in a context
FTVC : Context → List Id
FTVC ∅ = []
FTVC (c , x ⦂ σ) = FTVC c ++ FTV σ

-- UListToList : ∀ {A : Set} → UList A → List A
-- UListToList a = {!!}

close : Context → Type → TypeScheme
close Γ τ = VV (FTVT τ / FTVC Γ) τ

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


-- postulate ftv≥ : ∀ {σ σ'} → σ ≥ σ' → FTV σ' ⊆ FTV σ

-- some of the FTVs in σ get bound in σ ≥ σ'
-- same thing happens for the FTVs in Γ , x ⦂ σ and Γ , x ⦂ σ'
postulate close≥ : ∀ {Γ x σ σ' τ} → σ ≥ σ' → close(Γ , x ⦂ σ) τ ≥ close (Γ , x ⦂ σ') τ

_ : FTVC (∅ , "x" ⦂ ` (` "a")) ≡ [ "a" ]
_ = refl

_ : FTVT (` "a" ⇒ ` "b") / FTVC (∅ , "x" ⦂ ` (` "a")) ≡ [ "b" ]
_ = refl

_ : close (∅ , "x" ⦂ ` (` "a")) (` "a" ⇒ ` "b") ≡ V "b" · (` (` "a" ⇒ ` "b"))
_ = refl

_ : close ∅ □ ≡ ` □
_ = refl

close∅ : ∀ {τ : Type} → close ∅ τ ≡ VV (FTVT τ) τ
close∅ {τ} =
  begin
    close ∅ τ
  ≡⟨⟩
    VV (FTVT τ / FTVC ∅) τ
  ≡⟨⟩
    VV (FTVT τ / []) τ
  ≡⟨ cong (λ a → VV a τ) /-empty ⟩
    VV (FTVT τ) τ
  ∎

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

  ⊢× : ∀ {Γ e e' τ τ'}
     → Γ ⊢ e ⦂ τ
     → Γ ⊢ e' ⦂ τ'
       --------------------
     → Γ ⊢ e × e' ⦂ τ × τ'

  ⊢π₁ : ∀ {Γ e τ τ'}
      → Γ ⊢ e ⦂ τ × τ'
        --------------
      → Γ ⊢ π₁ e ⦂ τ

  ⊢π₂ : ∀ {Γ e τ τ'}
      → Γ ⊢ e ⦂ τ × τ'
        --------------
      → Γ ⊢ π₂ e ⦂ τ'

  ⊢□ : ∀ {Γ}
       
       ---------
     → Γ ⊢ □ ⦂ □

  -- Monadic rules

  ⊢⟦⟧ : ∀ {Γ e τ ρ}
      → Γ ⊢ e ⦂ τ
      → Ok ρ
        ----------------
      → Γ ⊢ ⟦ e ⟧ ⦂ IO ρ τ
      
  ⊢use : ∀ {Γ e τ r}
       → Γ ⊢ e ⦂ τ
         ---------------
       → Γ ⊢ use r e ⦂ IO (` r) τ
  
  ⊢>>= : ∀ {Γ e e' τ τ' ρ}
       → Γ ⊢ e ⦂ (IO ρ τ')
       → Γ ⊢ e' ⦂ (τ' ⇒ IO ρ τ)
         -------------------
       → Γ ⊢ e >>= e' ⦂ IO ρ τ

  ⊢⋎ : ∀ {Γ e₁ e₂ τ₁ τ₂ ρ₁ ρ₂}
     → Γ ⊢ e₁ ⦂ IO ρ₁ τ₁
     → Γ ⊢ e₂ ⦂ IO ρ₂ τ₂
     → Ok (ρ₁ ∪ ρ₂)
       -----------------------
     → Γ ⊢ e₁ ⋎ e₂ ⦂ IO (ρ₁ ∪ ρ₂) (τ₁ × τ₂)

  ⊢sub : ∀ {Γ e τ ρ ρ'}
         → Γ ⊢ e ⦂ IO ρ τ
         → ρ ≥: ρ'
         → Ok ρ'
           --------------
         → Γ ⊢ e ⦂ IO ρ' τ


_ : ∅ ⊢ ƛ "x" ⇒ □ ⦂ ( □ ⇒ □ )
_ = ⊢ƛ ⊢□

_ : ∅ , "x" ⦂ (V "x" · (` (` "x" ⇒ ` "x"))) ⊢ (` "x" · □) ⦂ □
_ = ⊢· (⊢` Z (Inst (SS "x" □ SZ) refl refl)) ⊢□

_ : ∅ ⊢ ƛ "x" ⇒ (` "x") ⦂ ( ` "α" ⇒ ` "α" )
_ = ⊢ƛ (⊢` Z (Inst SZ refl refl))

postulate roundtripSub : ∀ {Γ x σ e τ}
               → (s : BJS)
               → subC (BJS.from s) (Γ , x ⦂ sub (BJS.to s) σ) ⊢ 
                      e ⦂ subT (BJS.from s) (subT (BJS.to s) τ)
               → Γ , x ⦂ σ ⊢ e ⦂ τ

data Disjoint : List Id → List Id → Set where
  DisHere : ∀ {ys} → Disjoint [] ys
  DisThere : ∀ {x xs ys} → x ∉ ys → Disjoint xs ys → Disjoint (x ∷ xs) ys

disjoint-[] : ∀ {a} → Disjoint a []
disjoint-[] {[]} = DisHere
disjoint-[] {x ∷ a} = DisThere (λ ()) disjoint-[]

∉-∷ : ∀ {a b xs ys} → a ∉ xs → b ∉ a ∷ ys → a ∉ b ∷ xs
∉-∷ a∉xs b∉a∷ys (here refl) = b∉a∷ys (here refl)
∉-∷ a∉xs b∉a∷ys (there a∈b∷xs) = a∉xs a∈b∷xs

disjoint-insert : ∀ {a b x} → Disjoint a b → x ∉ a → Disjoint a (x ∷ b)
disjoint-insert DisHere x∉a = DisHere
disjoint-insert {a ∷ as} {b} {x} (DisThere x∉b dj) x∉a∷as =
  let z : Disjoint as (x ∷ b)
      z = disjoint-insert dj (λ z → x∉a∷as (there z))
      in DisThere (∉-∷ x∉b x∉a∷as) z

disjoint-sym : ∀ {a b} → Disjoint a b → Disjoint b a
disjoint-sym DisHere = disjoint-[]
disjoint-sym (DisThere x∉ d) = disjoint-insert (disjoint-sym d) x∉

disjointWeaken : ∀ {x xs ys} → Disjoint (x ∷ xs) ys → Disjoint xs ys
disjointWeaken (DisThere _ d) = d

postulate disjointSubContext : ∀ {Γ s} → Disjoint (subRegion s) (FTVC Γ) → subC s Γ ≡ Γ

postulate disjointSubTypeScheme : ∀ {αs τ s} → Disjoint (subRegion s) αs → sub s (VV αs τ) ≡ VV αs τ

postulate freshTypeVars : (αs : List Id) → ∃[ βs ] (Disjoint αs βs)
