module EquivNormalNatDedCutFree where

open import Basics
open import Form
open import NormalNatDed
open import CutFree

soundness : ∀ {Γ A} → Γ ⇒* A → Γ ⊢+↑ A
soundness (init x) = change (id x)
soundness (⊥-l p) = ⊥-e (change (soundness p))
soundness (⊃-l {A = A}{B = B} p p') with soundness p | soundness p'
...| p1 | p2 = subst-↑ {Γ' = ∅} p2 (⊃-e (id here) p1)
soundness (⊃-r p) = ⊃-i (soundness p)

mutual
  completeness-↑ : ∀ {Γ C} → Γ ⊢+↑ C → Γ ⇒* C
  completeness-↑ (⊃-i p) = ⊃-r (completeness-↑ p)
  completeness-↑ (⊥-e x) = ⊥-l (completeness-↓ x (init here))
  completeness-↑ (change x) = completeness-↓ x (init here)

  completeness-↓ : ∀ {Γ C A} → Γ ⊢+↓ A → Γ , A ⇒* C →  Γ ⇒* C
  completeness-↓ (⊃-e p x) (init here) = {!!}
  completeness-↓ (⊃-e p x) (init (there x₁)) = init x₁
  completeness-↓ (⊃-e p x) (⊥-l p') = ⊥-l (completeness-↓ (⊃-e p x) p')
  completeness-↓ (⊃-e p x) (⊃-l p' p'') = {!!}
  completeness-↓ (⊃-e p x) (⊃-r p') = {!!}
  completeness-↓ (id here) p' = contraction p'
  completeness-↓ (id (there x)) p' = {!!}
  completeness-↓ (change x) (init here) = completeness-↑ x
  completeness-↓ (change x) (init (there x₁)) = init x₁
  completeness-↓ (change x) (⊥-l p') = ⊥-l (completeness-↓ (change x) p')
  completeness-↓ (change x) (⊃-l p' p'') = {!!}
  completeness-↓ (change x) (⊃-r p') = {!!}
