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
  completeness-↑ : ∀ {Γ C} → Γ ⇒* C → Γ ⊢+↑ C
  completeness-↑ (init x) = change (id x)
  completeness-↑ (⊥-l p) = ⊥-e (change (completeness-↑ p))
  completeness-↑ (⊃-l p p') = change (⊃-e (change (⊃-i (completeness-↑ p')))
                                          (change (⊃-e (id here)
                                                       (completeness-↑ p))))
  completeness-↑ (⊃-r p) = ⊃-i (completeness-↑ p)

  completeness-↓ : ∀ {Γ C} → Γ ⇒* C → Γ ⊢+↓ C
  completeness-↓ (init x) = id x
  completeness-↓ (⊥-l p) = change (⊥-e (completeness-↓ p))
  completeness-↓ (⊃-l p p') = subst-↓ {Γ' = ∅}(completeness-↓ p')
                                              (⊃-e (id here) (completeness-↑ p))
  completeness-↓ (⊃-r p) = change (⊃-i (change (completeness-↓ p)))
