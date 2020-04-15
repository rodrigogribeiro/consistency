module Admissibility where

open import Form
open import SeqCalc
open import CutFree

admissibility : ∀ {A Γ C} → Γ ⇒* A → Γ , A ⇒* C → Γ ⇒* C
admissibility {`⊥} p p' = ⊥-l p
admissibility {A ⊃ B} (init x) p' = {!!}
admissibility {A ⊃ B} (⊥-l p) p' = {!!}
admissibility {A ⊃ B} (⊃-l p p') p1 = {!!}
admissibility {A ⊃ B} (⊃-r p) p' = {!!}
