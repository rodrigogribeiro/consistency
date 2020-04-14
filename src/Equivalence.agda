module Equivalence where

open import Basics
open import Form
open import NatDed
open import SeqCalc

⇒-sound : ∀ {Γ A} → Γ ⊢n A → Γ ⇒ A
⇒-sound (id A∈Γ) = init A∈Γ
⇒-sound (⊃-i p) = ⊃-r (⇒-sound p)
⇒-sound (⊥-e p) = ⊥-l (⇒-sound p)
⇒-sound (⊃-e {A = A}{B = B} p p') = cut (⇒-sound p) (⊃-l (⇒-sound p1) (init here))

⇒-complete : ∀ {Γ A} → Γ ⇒ A → Γ ⊢n A
⇒-complete (init A∈Γ) = id A∈Γ
⇒-complete (⊥-l p) = ⊥-e (⇒-complete p)
⇒-complete (cut p p') = ⊃-e (⊃-i (⇒-complete p'))
                            (⇒-complete p)
⇒-complete (⊃-l p p') = {!!}


{- ⊃-e (weak-lemma (⊃-i (⇒-complete p')))
                            (⊃-e (id here)
                                 (weak-lemma (⇒-complete p))) -}
⇒-complete (⊃-r p) = ⊃-i (⇒-complete p)
