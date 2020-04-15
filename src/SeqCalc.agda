module SeqCalc where

open import Form
open import NormalNatDed
open import CtxPerm

infix 3 _⇒_

data _⇒_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
  ⊥-l  : ∀ {Γ A} → Γ ⇒ `⊥ → Γ ⇒ A
  cut  : ∀ {Γ A B} → Γ ⇒ A → (Γ , A) ⇒ B → Γ ⇒ B
  ⊃-l  : ∀ {Γ A B C} → Γ ⇒ A → (Γ , B) ⇒ C → (Γ , A ⊃ B) ⇒ C
  ⊃-r  : ∀ {Γ A B} → Γ , A ⇒ B → Γ ⇒ A ⊃ B


⊆-lemma : ∀ {Γ Γ' A B} → (Γ , A) ⊆ Γ' → (Γ' , A) ⇒ B → Γ' ⇒ B
⊆-lemma p (init x) = cut (init (p here)) (init x)
⊆-lemma p (⊥-l x) = ⊥-l (⊆-lemma p x)
⊆-lemma p (cut x x₁) = cut (init (p here)) (cut x x₁)
⊆-lemma p (⊃-l x x₁) = cut (init (p here)) (⊃-l x x₁)
⊆-lemma p (⊃-r x) = cut (init (p here)) (⊃-r x)

⊆-lemma2 : ∀ {Γ Γ' A} → (Γ , A) ⊆ Γ' →  Γ ⊆ Γ'
⊆-lemma2 p here = p (there here)
⊆-lemma2 p (there x) = p (there (⊆-lemma2 (λ z → z) x))

-- weakening for sequents with cut

weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⇒ A → Γ' ⇒ A
weakening Γ⊆Γ' (init x) = init (Γ⊆Γ' x)
weakening Γ⊆Γ' (⊥-l p) = ⊥-l (weakening Γ⊆Γ' p)
weakening Γ⊆Γ' (cut p p') = cut (weakening Γ⊆Γ' p) (weakening (⊆-inc Γ⊆Γ') p')
weakening Γ⊆Γ' (⊃-l p p') = ⊆-lemma Γ⊆Γ' (⊃-l (weakening (λ z → Γ⊆Γ' (there z)) p)
                                               (weakening (⊆-inc (⊆-lemma2 Γ⊆Γ')) p'))
weakening Γ⊆Γ' (⊃-r p) = ⊃-r (weakening (⊆-inc Γ⊆Γ') p)

-- soundness theorem

⊆-swap-head : ∀ {Γ A B} → (Γ , B) ⊆ (Γ , A , B)
⊆-swap-head here = here
⊆-swap-head (there p) = there (there p)

soundness : ∀ {Γ C} → Γ ⇒ C → Γ ⊢+↑ C
soundness (init x) = change (id x)
soundness (⊥-l p) = ⊥-e (change (soundness p))
soundness (cut p p') = change (⊃-e (change (⊃-i (soundness p'))) (soundness p))
soundness (⊃-l p p') = change (⊃-e (change (⊃-i (weakening-↑ ⊆-swap-head (soundness p'))))
                                   (change (⊃-e (id here) (weakening-↑ there (soundness p)))))
soundness (⊃-r p) = ⊃-i (soundness p)


-- completeness theorem

mutual
  completeness-↑ : ∀ {Γ C} → Γ ⊢+↑ C → Γ ⇒ C
  completeness-↑ (⊃-i p) = ⊃-r (completeness-↑ p)
  completeness-↑ (⊥-e p) = ⊥-l (completeness-↓ p)
  completeness-↑ (change p) = completeness-↓ p

  completeness-↓ : ∀ {Γ C} → Γ ⊢+↓ C → Γ ⇒ C
  completeness-↓ (⊃-e p p') with completeness-↓ p | completeness-↑ p'
  ...| p1 | p2 = cut p1 (⊃-l p2 (init here))
  completeness-↓ (id p) = init p
  completeness-↓ (change p) = completeness-↑ p
