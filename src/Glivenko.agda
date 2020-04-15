module Glivenko where

open import Basics
open import Form
open import NatDed renaming (weakening to weak-nd)
open import ClassicNatDed

-- auxiliar lemma present on Van Dalen logic and structure.

double-neg-sound : ∀ A → ∅ ⊢c A → ∅ ⊢c ~ (~ A)
double-neg-sound `⊥ p = ⊃-i (⊃-e (id here) (weakening (λ ()) p))
double-neg-sound (A ⊃ B) p = ⊃-i (⊃-e (id here) (weakening (λ ()) p))

double-neg-complete : ∀ A → ∅ ⊢c ~ (~ A) → ∅ ⊢c A
double-neg-complete `⊥ p = ⊃-e p (⊃-i (id here))
double-neg-complete (A ⊃ B) p = raa (⊃-e (weakening (λ ()) p) (id here))

-- proof of glivenko for classical logic

glivenko-nd : ∀ {Γ} A → Γ ⊢c A → Γ ⊢n (~ (~ A))
glivenko-nd `⊥ (id x) = ⊥-e (id x)
glivenko-nd `⊥ (raa p) = ⊃-i (⊃-e (glivenko-nd `⊥ p) (id here))
glivenko-nd `⊥ (⊃-e p p') = ⊥-e (⊃-e (glivenko-nd _ p) (glivenko-nd _ p'))
glivenko-nd (A ⊃ B) (id x) = ⊃-i (⊃-e (id here) (id (there x)))
glivenko-nd (A ⊃ B) (raa p) = ⊃-i (⊃-e (glivenko-nd `⊥ p) (⊃-i (id here)))
glivenko-nd (A ⊃ B) (⊃-i p) = {!!}
glivenko-nd (A ⊃ B) (⊃-e p p') = {!!}
