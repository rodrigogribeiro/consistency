module CtxPerm where

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

-- another definition for permuations

~-∈-def-l : ∀ {Γ}{Γ'} → Γ ~ Γ' → ∀ {A} → A ∈ Γ → A ∈ Γ'
~-∈-def-l (Skip p) here = here
~-∈-def-l (Skip p) (there p') = there (~-∈-def-l p p')
~-∈-def-l Swap here = there here
~-∈-def-l Swap (there here) = here
~-∈-def-l Swap (there (there p')) = there (there p')
~-∈-def-l (Trans p p₁) p' with ~-∈-def-l p p'
...| p1 = ~-∈-def-l p₁ p1

-- context union produces permutations

~-∪ : ∀ Γ Γ' → (Γ ∪ Γ') ~ (Γ' ∪ Γ)
~-∪ Γ ∅ rewrite ∪-∅-l {Γ} = ~-refl
~-∪ ∅ (Γ' , A) rewrite ∪-∅-l {Γ'} = Skip ~-refl
~-∪ (Γ , B) (Γ' , A) = {!!}
