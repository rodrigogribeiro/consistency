module EquivNormalNatDedCutFree where

open import Basics hiding (id)
open import Form
open import NormalNatDed
open import CutFree

soundness : ∀ {Γ A} → Γ ⇒* A → Γ ⊢+↑ A
soundness (init x) = change (id x)
soundness (⊥-l p) = ⊥-e (change (soundness p))
soundness (⊃-l {A = A}{B = B} p p') with soundness p | soundness p'
...| p1 | p2 = subst-↑ {Γ' = ∅} p2 (⊃-e (id here) p1)
soundness (⊃-r p) = ⊃-i (soundness p)


completeness-lemma-∈ : ∀ {Γ A C} → A ∈ Γ → ∀ {Γ1 Γ2} → (Γ ∪ ((Γ1 , A) ∪ Γ2)) ⇒* C → Γ ∪ (Γ1 ∪ Γ2) ⇒* C
completeness-lemma-∈ here {Γ1} {∅} p' = {!contraction-lemma p'!}
completeness-lemma-∈ (there p) {Γ1} {∅} p' = {!!}
completeness-lemma-∈ p {Γ1} {Γ2 , x} p' = {!!}


mutual
  completeness-↑ : ∀ {Γ C} → Γ ⊢+↑ C → Γ ⇒* C
  completeness-↑ (⊃-i p) = ⊃-r (completeness-↑ p)
  completeness-↑ (⊥-e x) = ⊥-l (completeness-↓ x (init here))
  completeness-↑ (change x) = completeness-↓ x (init here)

  completeness-↓ : ∀ {Γ C A} → Γ ⊢+↓ A → Γ , A ⇒* C →  Γ ⇒* C
  completeness-↓ (⊃-e p x) p' = {!!}
  completeness-↓ (id x) p' = {!!}
  completeness-↓ (change x) p' = {!!}
