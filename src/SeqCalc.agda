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

  ⇒-cut-lemma : ∀ {Γ Γ' A C} → Γ ⇒ A → Γ' ⇒ C → (Γ ∪ (Γ' ⊝ A)) ⇒ C
  ⇒-cut-lemma {A = `⊥} p p' = ⊥-l (⇒-monotonicity (⊆-∪-l _ _) p)
  ⇒-cut-lemma {A = A ⊃ B} (init x) (init x₁) = init (⊝-∪-r x₁ x)
  ⇒-cut-lemma {A = A ⊃ B} (init x) (⊥-l p') = ⊥-l (⇒-monotonicity (⊝-∪-r-stay x) p')
  ⇒-cut-lemma {A = A ⊃ B} (init {A = A ⊃ B} x) (⊃-l {A = A'}{B = B'} x₁ p' p'') with (A ⊃ B) ≟ (A' ⊃ B')
  ... | yes q rewrite q = ⊃-l (∈-∪-intro-l x)
                              (⇒-monotonicity (⊝-∪-r-stay x) p')
                              (⇒-monotonicity (⊆-inc (⊝-∪-r-stay x)) p'')
  ... | no q = ⊃-l (⊝-∪-r-stay x _ x₁)
                   (⇒-monotonicity (⊝-∪-r-stay x) p')
                   (⇒-monotonicity (⊆-inc (⊝-∪-r-stay x)) p'')
  ⇒-cut-lemma {A = A ⊃ B} (init {A = A ⊃ B} x) (⊃-r {A = A'}{B = B'} p') with (A ⊃ B) ≟ (A' ⊃ B')
  ...| yes q rewrite q = init (∈-∪-intro-l x)
  ...| no  q = ⊃-r (⇒-monotonicity (⊆-inc (⊝-∪-r-stay x)) p')
  ⇒-cut-lemma {A = A ⊃ B} (⊥-l p) p' = ⊥-l (⇒-monotonicity (⊆-∪-l _ _) p)
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l {A = A'}{B = B'} x p p₁) (init {A = C} x₁) with C ≟ (A ⊃ B)
  ...| yes q rewrite q = ?
  ...| no  q = init (∈-∪-intro-r (⊝-∈-≢ q x₁))
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊥-l p') = ⊥-l (⇒-cut-lemma (⊃-l x p p₁) p')
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊃-l x₁ p' p'') = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊃-r {A = A'}{B = B'} p') = ⊃-l (∈-∪-intro-l x) (⇒-monotonicity (⊆-∪-l _ _) p) (⊃-r (⇒-monotonicity (⊆-inc {!!}) p'))
  ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (init {A = C} x) with C ≟ (A ⊃ B)
  ...| yes q rewrite q = ⊃-r (⇒-monotonicity (⊆-inc (⊆-∪-l _ _)) p)
  ...| no  q = init (∈-∪-intro-r (⊝-∈-≢ q x))
  ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (⊥-l p') = ⊥-l (⇒-cut-lemma (⊃-r p) p')
  ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (⊃-l x p' p'') = {!!}
  ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (⊃-r {A = A'}{B = B'} p') with (A ⊃ B) ≟ (A' ⊃ B')
  ...| yes q rewrite (sym q) = ⇒-monotonicity (⊆-∪-l _ _) (⊃-r p)
  ...| no  q = ⇒-cut-lemma {!!} {!!}
