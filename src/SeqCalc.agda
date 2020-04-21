open import Basics
open import Form
open import Properties

module SeqCalc where

  infix 3 _⇒_

  data _⇒_ : Ctx → Form → Set where
    init : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
    ⊥-l  : ∀ {Γ A} → Γ ⇒ `⊥ → Γ ⇒ A
    ⊃-l  : ∀ {Γ A B C} → (A ⊃ B) ∈ Γ → Γ ⇒ A → (Γ , B) ⇒ C → Γ ⇒ C
    ⊃-r  : ∀ {Γ A B} → Γ , A ⇒ B → Γ ⇒ A ⊃ B

  -----------------------------------
  -- proving entailment properties --
  -----------------------------------

  -- 1. reflexivity

  ⇒-reflexivity : Reflexivity _⇒_
  ⇒-reflexivity = init

  -- 2. monotonicity

  ⇒-monotonicity : Monotonicity _⇒_
  ⇒-monotonicity ex (init x) = init (ex _ x)
  ⇒-monotonicity ex (⊥-l p) = ⊥-l (⇒-monotonicity ex p)
  ⇒-monotonicity ex (⊃-l x p p₁) = ⊃-l (ex _ x) (⇒-monotonicity ex p)
                                                (⇒-monotonicity (⊆-inc ex) p₁)
  ⇒-monotonicity ex (⊃-r p) = ⊃-r (⇒-monotonicity (⊆-inc ex) p)


  -- 3. auxiliar lemma for proving cut property

  ⇒-cut-lemma : ∀ {Γ Γ' A C} → Γ ⇒ A → Γ' ⇒ C →  (Γ ∪ (Γ' ⊝ A)) ⇒ C
  ⇒-cut-lemma {A = `⊥} p p' = ⊥-l (⇒-monotonicity (⊆-∪-l _ _) p)
  ⇒-cut-lemma {A = A ⊃ B} (init x) (init x₁) = init (⊝-∪-r x₁ x)
  ⇒-cut-lemma {A = A ⊃ B} (init x) (⊥-l p') = ⊥-l (⇒-monotonicity (⊝-∪-r-stay x) p')
  ⇒-cut-lemma {A = A ⊃ B} (init x) (⊃-l x₁ p' p'') = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (init x) (⊃-r p') = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (⊥-l p) p' = ⊥-l (⇒-monotonicity (⊆-∪-l _ _) p)
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (init x₁) = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊥-l p') = ⊥-l (⇒-cut-lemma (⊃-l x p p₁) p')
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊃-l x₁ p' p'') = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊃-r p') = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) p' = {!!}
