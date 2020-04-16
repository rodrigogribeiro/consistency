module Admissibility where

open import Form
open import SeqCalc
open import CutFree


adm-lemma : ∀ {Γ A B C} → A ∈ Γ → Γ , A , B ⇒* C → Γ , B ⇒* C
adm-lemma here (init here) = init here
adm-lemma here (init (there here)) = init (there here)
adm-lemma here (init (there (there x))) = init (there x)
adm-lemma (there p) (init here) = init here
adm-lemma (there p) (init (there here)) = init (there (there p))
adm-lemma (there p) (init (there (there x))) = init (there x)
adm-lemma p (⊥-l p') = ⊥-l (adm-lemma p p')
adm-lemma here (⊃-l p' p'') = ⊃-l (adm-lemma here p') (contraction-lemma {Γ'  = ∅ , _ , _} p'')
adm-lemma (there p) (⊃-l p' p'') = ⊃-l (adm-lemma (there p) p') (adm-lemma (there (there p)) {!!})
adm-lemma here (⊃-r p') = ⊃-r (contraction-lemma {Γ'  = ∅ , _ , _} p')
adm-lemma (there p) (⊃-r p') = ⊃-r (adm-lemma (there (there p)) {!!})

admissibility : ∀ A {Γ C} → Γ ⇒* A → Γ , A ⇒* C → Γ ⇒* C
admissibility `⊥ p p' = ⊥-l p
admissibility (A ⊃ B) (init x) (init here) = init x
admissibility (A ⊃ B) (init x) (init (there x₁)) = init x₁
admissibility (A ⊃ B) (init x) (⊥-l p') = ⊥-l (admissibility (A ⊃ B) (init x) p')
admissibility (A ⊃ B) (init x) (⊃-l p' p'') = {!!}
admissibility (A ⊃ B) (init x) (⊃-r p') = ⊃-r {!!}
admissibility (A ⊃ B) (⊥-l p) p' = ⊥-l p
admissibility (A ⊃ B) (⊃-l p p₁) (init x) = {!!}
admissibility (A ⊃ B) (⊃-l p p₁) (⊥-l p') = ⊥-l (admissibility (A ⊃ B) (⊃-l p p₁) p')
admissibility (A ⊃ B) (⊃-l p p₁) (⊃-l p' p'') = {!!}
admissibility (A ⊃ B) (⊃-l p p₁) (⊃-r p') = {!!}
admissibility (A ⊃ B) (⊃-r p) (init x) = {!!}
admissibility (A ⊃ B) (⊃-r p) (⊥-l p') = ⊥-l (admissibility (A ⊃ B) (⊃-r p) p')
admissibility (A ⊃ B) (⊃-r p) (⊃-l p' p'') = {!!}
admissibility (A ⊃ B) (⊃-r p) (⊃-r p') = ⊃-r {!!}
