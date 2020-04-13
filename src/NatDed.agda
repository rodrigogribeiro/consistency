module NatDed where

open import Basics
open import Form

infix 3 _⊢n_

data _⊢n_ : Ctx → Form → Set where
  id : ∀ {Γ A} → A ∈ Γ → Γ ⊢n A
  ⊥-e : ∀ {Γ A} → Γ ⊢n `⊥ → Γ ⊢n A
  ⊃-i : ∀ {Γ A B} → (Γ , A) ⊢n B → Γ ⊢n (A ⊃ B)
  ⊃-e : ∀ {Γ A B} → Γ ⊢n (A ⊃ B) → Γ ⊢n A → Γ ⊢n B

weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢n A → Γ' ⊢n A
weakening Γ⊆Γ' (id A∈Γ) = id (Γ⊆Γ' A∈Γ)
weakening Γ⊆Γ' (⊃-i p) = ⊃-i (weakening (⊆-inc Γ⊆Γ') p)
weakening Γ⊆Γ' (⊃-e p p') = ⊃-e (weakening Γ⊆Γ' p) (weakening Γ⊆Γ' p')
weakening Γ⊆Γ' (⊥-e p) = ⊥-e (weakening Γ⊆Γ' p)

weak-lemma : ∀ {Γ A B} → Γ ⊢n A → Γ , B ⊢n A
weak-lemma p = weakening (λ B∈Γ → there B∈Γ) p
