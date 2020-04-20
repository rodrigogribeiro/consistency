module EquivNatDedSeqCalc where

open import Basics hiding (id)
open import Form
open import NatDed renaming (weakening to weakening-nd)
open import SeqCalc

⇒-sound : ∀ {Γ A} → Γ ⊢n A → Γ ⇒ A
⇒-sound (id A∈Γ) = init A∈Γ
⇒-sound (⊃-i p) = ⊃-r (⇒-sound p)
⇒-sound (⊥-e p) = ⊥-l (⇒-sound p)
⇒-sound (⊃-e {A = A}{B = B} p p') = cut (⇒-sound p) (⊃-l here {!weakening!} {!!})

⇒-complete : ∀ {Γ A} → Γ ⇒ A → Γ ⊢n A
⇒-complete (init A∈Γ) = id A∈Γ
⇒-complete (⊥-l p) = ⊥-e (⇒-complete p)
⇒-complete (cut p p') = ⊃-e (⊃-i (⇒-complete p'))
                            (⇒-complete p)
⇒-complete (⊃-l p p' p1) = ⊃-e (⊃-i (⇒-complete p1)) (⊃-e (id p) (⇒-complete p'))
⇒-complete (⊃-r p) = ⊃-i (⇒-complete p)
