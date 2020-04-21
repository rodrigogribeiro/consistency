open import Basics
open import Form

module Properties where

  -- some entailment properties

  Monotonicity : (Ctx → Form → Set) → Set
  Monotonicity R = ∀ {Γ Γ' A} → Γ ⊆ Γ' → R Γ A → R Γ' A

  Reflexivity : (Ctx → Form → Set) → Set
  Reflexivity R = ∀ {Γ A} → A ∈ Γ → R Γ A

  Cut : (Ctx → Form → Set) → Set
  Cut R = ∀ Γ A B → R Γ A → R (Γ , A) B → R Γ B

  Consistency : (Ctx → Form → Set) → Set
  Consistency R = ¬ (R ∅ `⊥)

  -- some logical properties

  define-⊥ : (Ctx → Form → Set) → Set
  define-⊥ R = ∀ Γ → R Γ `⊥ ↔ (∀ A → R Γ A)

  define-⊃ : (Ctx → Form → Set) → Set
  define-⊃ R = ∀ Γ A B → R Γ (A ⊃ B) ↔ R (Γ , A) B
