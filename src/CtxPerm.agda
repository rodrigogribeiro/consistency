module CtxPerm where

open import Basics
open import Form


data _~_ : Ctx → Ctx → Set where
  Done  : ∅ ~ ∅
  Skip  : ∀ {t Γ Γ'} → Γ ~ Γ' → (Γ , t) ~ (Γ' , t)
  Swap  : ∀ {t t' Γ} → (Γ , t , t') ~ (Γ , t' , t)
  Trans : ∀ {Γ Γ₁ Γ'} → Γ ~ Γ₁ → Γ₁ ~ Γ' → Γ ~ Γ'

-- Proving that permutation is an equivalence relation.

~-refl : ∀ {Γ} -> Γ ~ Γ
~-refl {∅} = Done
~-refl {Γ , t} = Skip ~-refl

~-sym : ∀ {Γ Γ'} ->  Γ ~ Γ' ->  Γ' ~ Γ
~-sym Done = Done
~-sym (Skip prf) = Skip (~-sym prf)
~-sym Swap = Swap
~-sym (Trans prf prf₁) = Trans (~-sym prf₁) (~-sym prf)

~-trans : ∀ {Γ Γ₁ Γ'} ->  Γ ~ Γ₁ ->  Γ₁ ~ Γ' -> Γ ~ Γ'
~-trans p1 p2 = Trans p1 p2

-- permutation preserves lookup

~-∈ : ∀ {Γ Γ' A} → A ∈ Γ → Γ ~ Γ' → A ∈ Γ'
~-∈ here (Skip p') = here
~-∈ (there p) (Skip p') = there (~-∈ p p')
~-∈ here Swap = there here
~-∈ (there here) Swap = here
~-∈ (there (there p)) Swap = there (there p)
~-∈ p (Trans p' p'') with ~-∈ p p'
...| p1 = ~-∈ p1 p''

