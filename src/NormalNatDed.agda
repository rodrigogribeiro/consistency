module NormalNatDed where

open import Basics
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
