module Admissibility where

open import Form
open import SeqCalc
open import CutFree

admissibility : ∀ {A Γ C} → Γ ⇒* A → Γ , A ⇒* C → Γ ⇒* C
admissibility {`⊥} p p' = ⊥-l p
admissibility {A ⊃ B} (init x) (init here) = init x
admissibility {A ⊃ B} (init x) (init (there x₁)) = init x₁
admissibility {A ⊃ B} (init x) (⊥-l p') = ⊥-l (admissibility (init x) p')
admissibility {A ⊃ B} (init x) (⊃-l p' p'') = {!!}
admissibility {A ⊃ B} (init x) (⊃-r p') = {!!}
admissibility {A ⊃ B} (⊥-l p) p' = ⊥-l p
admissibility {A ⊃ B} (⊃-l p p₁) (init here) = ⊃-l p p₁
admissibility {A ⊃ B} (⊃-l p p₁) (init (there x)) = init x
admissibility {A ⊃ B} (⊃-l p p₁) (⊥-l p') = ⊥-l (admissibility (⊃-l p p₁) p')
admissibility {A ⊃ B} (⊃-l p p₁) (⊃-l p' p'') = {!!}
admissibility {A ⊃ B} (⊃-l p p₁) (⊃-r p') = ⊃-r {!!}
admissibility {A ⊃ B} (⊃-r p) (init here) = ⊃-r p
admissibility {A ⊃ B} (⊃-r p) (init (there x)) = init x
admissibility {A ⊃ B} (⊃-r p) (⊥-l p') = ⊥-l (admissibility (⊃-r p) p')
admissibility {A ⊃ B} (⊃-r p) (⊃-l p' p'') = {!!}
admissibility {A ⊃ B} (⊃-r p) (⊃-r p') = ⊃-r (admissibility {!!} {!!})
