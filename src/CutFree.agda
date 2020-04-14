module CutFree where

open import Form
open import CtxPerm

infix 3 _⇒*_

data _⇒*_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒* A
  ⊥-l  : ∀ {Γ A} → Γ ⇒* `⊥ → Γ ⇒* A
  ⊃-l  : ∀ {Γ A B C} → Γ , A ⊃ B ⇒* A → Γ , A ⊃ B , B ⇒* C → (Γ , A ⊃ B) ⇒* C
  ⊃-r  : ∀ {Γ A B} → Γ , A ⇒* B → Γ ⇒* A ⊃ B

contraction' : ∀ {Γ Γ' A C} → (Γ , A , A) ∪ Γ' ⇒* C → (Γ , A) ∪ Γ' ⇒* C
contraction' (init here) = init here
contraction' (init (there x)) = init x
contraction' {Γ}{Γ'}(⊥-l p) = ⊥-l (contraction' {Γ}{Γ'} p)
contraction' {Γ}{Γ'}(⊃-l p p') = ⊃-l (contraction' {Γ}{Γ'} p) {!!}
contraction' (⊃-r p) = ⊃-r {!!}


contraction : ∀ {Γ A C} → Γ , A , A ⇒* C → Γ , A ⇒* C
contraction (init here) = init here
contraction (init (there x)) = init x
contraction (⊥-l p) = ⊥-l (contraction p)
contraction (⊃-l p p') = ⊃-l (contraction p) {!!}
contraction (⊃-r p) = {!!}

admissibility : ∀ {Γ C} A → Γ ⇒* A  → Γ , A ⇒* C → Γ ⇒* C
admissibility = {!!}
