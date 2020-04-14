module ClassicNatDed where

open import Basics
open import Form
open import CtxPerm

infix 3 _⊢c_

data _⊢c_ : Ctx → Form → Set where
  id : ∀ {Γ A} → A ∈ Γ → Γ ⊢c A
  raa : ∀ {Γ A} → Γ , (A ⊃ `⊥) ⊢c `⊥ → Γ ⊢c A
  ⊃-i : ∀ {Γ A B} → (Γ , A) ⊢c B → Γ ⊢c (A ⊃ B)
  ⊃-e : ∀ {Γ A B} → Γ ⊢c (A ⊃ B) → Γ ⊢c A → Γ ⊢c B

-- weakening for classical natural deduction

weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢c A → Γ' ⊢c A 
weakening Γ⊆Γ' (id x) = id (Γ⊆Γ' x)
weakening Γ⊆Γ' (raa p) = raa (weakening (⊆-inc Γ⊆Γ') p)
weakening Γ⊆Γ' (⊃-i p) = ⊃-i (weakening (⊆-inc Γ⊆Γ') p)
weakening Γ⊆Γ' (⊃-e p p') = ⊃-e (weakening Γ⊆Γ' p) (weakening Γ⊆Γ' p')
