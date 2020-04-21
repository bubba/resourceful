module Resourceful.Semantics.Dynamic where

open import Resourceful.Grammar

data Value : Term → Set where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)
  V-⟦⟧ : ∀ {e} → Value (⟦ e ⟧)
  V-□ : Value □
  V-× : ∀ {e₁ e₂}
      → Value e₁
      → Value e₂
        ---------------
      → Value (e₁ × e₂)
  V-use : ∀ {r e} → Value (use r e)

infix 2 _↝_

data _↝_ : Term → Term → Set where

  -- lambda calculus

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

  -- HM let binding
  
  β-lt : ∀ {x e e'}
         -- TODO: should (Value e')?
         ----------
       → (lt x ⇐ e' in' e) ↝ e [ x := e' ]       

  -- monads
  
  ξ->>= : ∀ {e₁ e₂ e₁'}
        → e₁ ↝ e₁'
          ----------------------
        → e₁ >>= e₂ ↝ e₁' >>= e₂

  β->>= : ∀ {v e}
          -------------------
        → ⟦ v ⟧ >>= e ↝ e · v

  β->>=-use : ∀ {r e e'}
              -----------------------
            → use r e >>= e' ↝ e' · e

  -- product types
  
  ξ-×₁ : ∀ {e₁ e₂ e₁'}
       → e₁ ↝ e₁'
         ------------
       → e₁ × e₂ ↝ e₁' × e₂
       
  ξ-×₂ : ∀ {e₁ e₂ e₂'}
       → e₂ ↝ e₂'
         ------------
       → e₁ × e₂ ↝ e₁ × e₂'

  ξ-π₁ : ∀ {e e'}
       → e ↝ e'
         ------------
       → π₁ e ↝ π₁ e'

  ξ-π₂ : ∀ {e e'}
       → e ↝ e'
         ------------
       → π₂ e ↝ π₂ e'

  β-π₁ : ∀ {e₁ e₂}
         -----------------
       → π₁ (e₁ × e₂) ↝ e₁

  β-π₂ : ∀ {e₁ e₂}
         -----------------
       → π₂ (e₁ × e₂) ↝ e₂

  -- resource stuff

  β-⋎ : ∀ {v w}
        ---------------------------------------------------------
      → v ⋎ w ↝ v >>= ƛ "v" ⇒ (w >>= (ƛ "w" ⇒ ⟦ ` "v" × ` "w" ⟧)) 
