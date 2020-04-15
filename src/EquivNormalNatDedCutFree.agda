module EquivNormalNatDedCutFree where

open import Basics
open import Form
open import NormalNatDed
open import CutFree

soundness : ∀ {Γ A} → Γ ⇒* A → Γ ⊢+↑ A
soundness (init x) = change (id x)
soundness (⊥-l p) = ⊥-e (change (soundness p))
soundness (⊃-l p p') with soundness p | soundness p'
...| p1 | p2 = {!!}
soundness (⊃-r p) = ⊃-i (soundness p)
