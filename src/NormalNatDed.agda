module NormalNatDed where

open import Basics hiding (id)
open import Form
open import NatDed

infix 3 _⊢↑_
infix 3 _⊢↓_

mutual
  data _⊢↑_ : Ctx → Form → Set where
    ⊃-i : ∀ {Γ A B} → Γ , A ⊢↑ B → Γ ⊢↑ A ⊃ B
    ⊥-e : ∀ {Γ A} → Γ ⊢↓ `⊥ → Γ ⊢↑ A 

  data _⊢↓_ : Ctx → Form → Set where
    ⊃-e : ∀ {Γ A B} → Γ ⊢↓ A ⊃ B → Γ ⊢↑ A → Γ ⊢↓ B
    id  : ∀ {Γ A} → A ∈ Γ → Γ ⊢↓ A

-- soundness theorem

mutual
  soundness-↑ : ∀ {Γ A} → Γ ⊢↑ A → Γ ⊢n A
  soundness-↑ (⊃-i p) = ⊃-i (soundness-↑ p) 
  soundness-↑ (⊥-e p) = ⊥-e (soundness-↓ p)

  soundness-↓ : ∀ {Γ A} → Γ ⊢↓ A → Γ ⊢n A
  soundness-↓ (⊃-e p x) = ⊃-e (soundness-↓ p) (soundness-↑ x)
  soundness-↓ (id x) = id x

-- 

infix 3 _⊢+↑_
infix 3 _⊢+↓_

mutual
  data _⊢+↑_ : Ctx → Form → Set where
    ⊃-i : ∀ {Γ A B} → Γ , A ⊢+↑ B → Γ ⊢+↑ A ⊃ B
    ⊥-e : ∀ {Γ A} → Γ ⊢+↓ `⊥ → Γ ⊢+↑ A
    change : ∀ {Γ A} → Γ ⊢+↓ A → Γ ⊢+↑ A

  data _⊢+↓_ : Ctx → Form → Set where
    ⊃-e : ∀ {Γ A B} → Γ ⊢+↓ A ⊃ B → Γ ⊢+↑ A → Γ ⊢+↓ B
    id  : ∀ {Γ A} → A ∈ Γ → Γ ⊢+↓ A
    change : ∀ {Γ A} → Γ ⊢+↑ A → Γ ⊢+↓ A

-- soundness for extended deduction

mutual
  soundness-+↑ : ∀ {Γ A} → Γ ⊢+↑ A → Γ ⊢n A
  soundness-+↑ (⊃-i p) = ⊃-i (soundness-+↑ p)
  soundness-+↑ (⊥-e x) = ⊥-e (soundness-+↓ x)
  soundness-+↑ (change p) = (soundness-+↓ p)

  soundness-+↓ : ∀ {Γ A} → Γ ⊢+↓ A → Γ ⊢n A
  soundness-+↓ (⊃-e p x) = ⊃-e (soundness-+↓ p) (soundness-+↑ x)
  soundness-+↓ (id x) = id x
  soundness-+↓ (change p) = soundness-+↑ p

-- completeness

completeness : ∀ {Γ A} → Γ ⊢n A → (Γ ⊢+↑ A) × (Γ ⊢+↓ A)
completeness (id x) = change (id x) , (id x)
completeness (⊥-e p) = ⊥-e (snd (completeness p)) , change (⊥-e (snd (completeness p)))
completeness (⊃-i p) = ⊃-i (fst (completeness p)) , change (⊃-i (fst (completeness p)))
completeness (⊃-e p p') with completeness p | completeness p'
...| q | q' = change (⊃-e (snd q) (fst q')) , (⊃-e (snd q) (fst q'))

-- weakening

mutual
  weakening-↑ : ∀ {Γ Γ' C} → Γ ⊆ Γ' → Γ ⊢+↑ C → Γ' ⊢+↑ C
  weakening-↑ Γ⊆Γ' (⊃-i p) = ⊃-i (weakening-↑ (⊆-inc Γ⊆Γ') p)
  weakening-↑ Γ⊆Γ' (⊥-e p) = ⊥-e (weakening-↓ Γ⊆Γ' p)
  weakening-↑ Γ⊆Γ' (change p) = change (weakening-↓ Γ⊆Γ' p)
  
  weakening-↓ : ∀ {Γ Γ' C} → Γ ⊆ Γ' → Γ ⊢+↓ C → Γ' ⊢+↓ C
  weakening-↓ Γ⊆Γ' (⊃-e p p') = ⊃-e (weakening-↓ Γ⊆Γ' p) (weakening-↑ Γ⊆Γ' p')
  weakening-↓ Γ⊆Γ' (id p) = id (Γ⊆Γ' p)
  weakening-↓ Γ⊆Γ' (change p) = change (weakening-↑ Γ⊆Γ' p)

-- substitution

mutual
  subst-↑ : ∀ {Γ Γ' A C} → (Γ , A) ∪ Γ' ⊢+↑ C → Γ ⊢+↓ A → Γ ∪ Γ' ⊢+↑ C
  subst-↑ (⊃-i p) p' = change (⊃-e (change (⊃-i (⊃-i p))) (weakening-↑ (⊆-∪-l _ _) (change p')))
  subst-↑ (⊥-e p) p' = ⊥-e (subst-↓ p p')
  subst-↑ (change x) p' = change (subst-↓ x p')

  subst-↓ : ∀ {Γ Γ' A C} → (Γ , A) ∪ Γ' ⊢+↓ C → Γ ⊢+↓ A → Γ ∪ Γ' ⊢+↓ C
  subst-↓ (⊃-e p x) (⊃-e p' x₁) = ⊃-e (subst-↓ p (⊃-e p' x₁)) (subst-↑ x (⊃-e p' x₁))
  subst-↓ (⊃-e p x) (id x₁) = ⊃-e (subst-↓ p (id x₁)) (subst-↑ x (id x₁))
  subst-↓ (⊃-e p x) (change x₁) = ⊃-e (subst-↓ p (change x₁)) (subst-↑ x (change x₁))
  subst-↓ (id x) p' with soundness-+↓ p'
  ...| p1 = snd (completeness (subst-nd (id x) p1))
  subst-↓ (change x) p' = change (subst-↑ x p')


