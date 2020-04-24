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


  ⊆-cut-lemma-≡ : ∀ Γ Γ' A B → A ≡ B → (Γ ∪ ((Γ' , A) ⊝ B)) ⊆ (Γ ∪ ((Γ' ⊝ B)) , A)
  ⊆-cut-lemma-≡ Γ Γ' A .A refl with A ≟ A
  ...| yes refl = λ z → there
  ...| no q = ⊥-elim (q refl)

  ⊆-cut-lemma-≢ : ∀ Γ Γ' A B → A ≢ B → (Γ ∪ ((Γ' , A) ⊝ B)) ⊆ (Γ ∪ ((Γ' ⊝ B)) , A)
  ⊆-cut-lemma-≢ Γ Γ' A B neq with A ≟ B
  ...| yes eq = ⊥-elim (neq eq)
  ...| no  q  = λ z z₁ → z₁

  {-
  (Γ ∪ ((Γ' , A1) ⊝ (A ⊃ B) | A1 ≟ (A ⊃ B))) ⊆
  (Γ ∪ (Γ' ⊝ (A ⊃ B)) , A1)
  -}


  -- 3. auxiliar lemma for proving cut property

  ⇒-cut-lemma : ∀ Γ A → Γ ⇒ A → ∀ Γ' C → Γ' ⇒ C → (Γ ∪ (Γ' ⊝ A)) ⇒ C
  ⇒-cut-lemma Γ `⊥ p Γ' C p' = ⊥-l (⇒-monotonicity (⊆-∪-l _ _) p)
  ⇒-cut-lemma Γ (A ⊃ B) (init x) Γ' C (init x₁) = init (⊝-∪-r x₁ x)
  ⇒-cut-lemma Γ (A ⊃ B) (init x) Γ' C (⊥-l p')
    = ⊥-l (⇒-cut-lemma Γ (A ⊃ B) (init x) Γ' `⊥ p')
  ⇒-cut-lemma Γ (A ⊃ B) (init x) Γ' C (⊃-l {A = A1}{B = B1} x₁ p' p'') with (A ⊃ B) ≟ (A1 ⊃ B1)
  ...| yes q rewrite q = ⊃-l (∈-∪-intro-l x)
                             (⇒-monotonicity (⊝-∪-r-stay x) p')
                             (⇒-monotonicity (⊆-inc (⊝-∪-r-stay x)) p'')
  ...| no  q = ⊃-l (⊝-∪-r-stay x _ x₁)
                   (⇒-monotonicity (⊝-∪-r-stay x) p')
                   (⇒-monotonicity (⊆-inc (⊝-∪-r-stay x)) p'') 
  ⇒-cut-lemma Γ (A ⊃ B) (init x) Γ' .(_ ⊃ _) (⊃-r {A = A1}{B = B1} p') with (A ⊃ B) ≟ (A1 ⊃ B1)
  ...| yes q rewrite q = init (∈-∪-intro-l x)
  ...| no  q = ⊃-r (⇒-monotonicity (⊆-inc (⊝-∪-r-stay x)) p')
  ⇒-cut-lemma Γ (A ⊃ B) (⊥-l p) Γ' C p' = ⊥-l (⇒-monotonicity (⊆-∪-l _ _) p)
  ⇒-cut-lemma Γ (A ⊃ B) (⊃-l x p p₁) Γ' C (init x₁) with C ≟ (A ⊃ B)
  ...| yes q rewrite q = ⊃-l (∈-∪-intro-l x)
                             (⇒-monotonicity (⊆-∪-l _ _) p)
                             (⇒-monotonicity (⊆-inc (⊆-∪-l _ _)) p₁)
  ...| no  q = init (∈-∪-intro-r (⊝-∈-≢ q x₁))
  ⇒-cut-lemma Γ (A ⊃ B) (⊃-l x p p₁) Γ' C (⊥-l p')
    = ⊥-l (⇒-cut-lemma Γ (A ⊃ B) (⊃-l x p p₁) Γ' `⊥ p')
  ⇒-cut-lemma Γ (A ⊃ B) (⊃-l x p p₁) Γ' C (⊃-l x₁ p' p'') = {!!}
  ⇒-cut-lemma Γ (A ⊃ B) (⊃-l {A = A'}{B = B'} x p p₁) Γ' .(_ ⊃ _) (⊃-r {A = A1}{B = B1} p') with A1 ≟ (A ⊃ B)
  ...| q = ⊃-r ((⇒-monotonicity (dec (⊆-cut-lemma-≡ Γ Γ' A1 (A ⊃ B))
                                     (⊆-cut-lemma-≢ Γ Γ' A1 (A ⊃ B)) q)
                                (⇒-cut-lemma Γ (A ⊃ B) ((⊃-l x p p₁)) (Γ' , A1) B1 p')))
  ⇒-cut-lemma Γ (A ⊃ B) (⊃-r p) Γ' C p' = {!!}


{-

⊃-r ((⇒-monotonicity {!!} (⇒-cut-lemma Γ (A ⊃ B) ((⊃-l x p p₁)) (Γ' , A1) B1 (subst (λ x → Γ' , x ⇒ B1) (sym q) p'))))


with A1 ≟ (A ⊃ B) | A ≟ A | B ≟ B
...| yes refl | yes refl | yes refl = ⊃-r (⇒-monotonicity {!!} (⇒-cut-lemma Γ (A ⊃ B) ((⊃-l x p p₁)) (Γ' , A1) B1 (subst (λ x → Γ' , x ⇒ B1) refl p')))
...| yes refl | no q2  | _      = {!!}
...| yes refl | _      | no q3  = {!!}
...| no q1    | yes q2 | yes q3 = {!!}
...| no q1    | no q2  | _      = {!!}
...| no q1    | _      | no q3
-}


-- ⊃-r (⇒-monotonicity {!!} (⇒-cut-lemma Γ (A ⊃ B) ((⊃-l x p p₁)) (Γ' , A1) B1 (subst (λ x → Γ' , x ⇒ B1) refl p')))

-- ⊃-r (⇒-monotonicity {!⊆-inc!} (⇒-cut-lemma Γ (A ⊃ B) ((⊃-l x p p₁)) (Γ' , A1) B1 p'))

  
  -- ⇒-cut-lemma {Γ}{Γ'}{A = A ⊃ B} (⊃-l {A = A1}{B = B1} x p p₁) (⊃-l {A = A2}{B = B2} x₁ p' p'') with (A2 ⊃ B2) ≟ (A ⊃ B)
  -- ...| yes q rewrite (fst (≡-inv q)) | (snd (≡-inv q)) 
  --   = {!!}
  -- ...| no  q = {!!}
  -- ⇒-cut-lemma {A = A ⊃ B} (⊃-l x p p₁) (⊃-r {A = A'}{B = B'} p') = {!!} 
  -- ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (init {A = C} x) with C ≟ (A ⊃ B)
  -- ...| yes q rewrite q = ⊃-r (⇒-monotonicity (⊆-inc (⊆-∪-l _ _)) p)
  -- ...| no  q = init (∈-∪-intro-r (⊝-∈-≢ q x))
  -- ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (⊥-l p') = ⊥-l (⇒-cut-lemma (⊃-r p) p')
  -- ⇒-cut-lemma {A = A ⊃ B}{C = C} (⊃-r p) (⊃-l {A = A'}{B = B'} x p' p'') = {!!}
  -- ⇒-cut-lemma {A = A ⊃ B} (⊃-r p) (⊃-r {A = A'}{B = B'} p') with (A ⊃ B) ≟ (A' ⊃ B')
  -- ...| yes q rewrite (sym q) = ⇒-monotonicity (⊆-∪-l _ _) (⊃-r p)
  -- ...| no  q = {!!} 
