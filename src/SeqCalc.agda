module SeqCalc where

open import Basics hiding (id)
open import Form
open import NormalNatDed
open import CtxPerm

infix 3 _⇒_

data _⇒_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
  ⊥-l  : ∀ {Γ A} → Γ ⇒ `⊥ → Γ ⇒ A
  cut  : ∀ {Γ A B} → Γ ⇒ A → (Γ , A) ⇒ B → Γ ⇒ B
  ⊃-l  : ∀ {Γ A B C} → (A ⊃ B) ∈ Γ → Γ ⇒ A → (Γ , B) ⇒ C → Γ ⇒ C
  ⊃-r  : ∀ {Γ A B} → Γ , A ⇒ B → Γ ⇒ A ⊃ B


---------------------------
-- structural properties --
---------------------------

-- 1. weakening

weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⇒ A → Γ' ⇒ A
weakening s (init x) = init (∈-⊆ s x)
weakening s (⊥-l p) = ⊥-l (weakening s p)
weakening s (cut p p₁) = cut (weakening s p) (weakening (keep s) p₁)
weakening s (⊃-l d p p₁) = ⊃-l (∈-⊆ s d) (weakening s p) (weakening (keep s) p₁)
weakening s (⊃-r p) = ⊃-r (weakening (keep s) p)


-- 2. monotonicity, based on set-based equality

monotonicity : ∀ {Γ Γ' C} → Γ ≈ Γ' → Γ ⇒ C → Γ' ⇒ C
monotonicity ex (init x) = init (_↔_.to (ex _) x)
monotonicity ex (⊥-l p) = ⊥-l (monotonicity ex p)
monotonicity ex (cut p p') = cut (monotonicity ex p) (monotonicity (≈-inc ex) p')
monotonicity ex (⊃-l d p p') = ⊃-l (∈-≈ ex d) (monotonicity ex p) (monotonicity (≈-inc ex) p')
monotonicity ex (⊃-r p) = ⊃-r (monotonicity (≈-inc ex) p)

-------------------------------- 
-- soundness and completeness --
--------------------------------

soundness : ∀ {Γ C} → Γ ⇒ C → Γ ⊢+↑ C
soundness (init x) = change (id x)
soundness (⊥-l p) = ⊥-e (change (soundness p))
soundness (cut p p₁) = change (⊃-e (change (⊃-i (soundness p₁))) (soundness p))
soundness (⊃-l d p p₁) = subst-↑ (soundness p₁) (⊃-e (id d) (soundness p))
soundness (⊃-r p) = ⊃-i (soundness p)


private 
  ⊆-completeness1 : ∀ {Γ B} A → (Γ , B) ⊆ (Γ , A , B)
  ⊆-completeness1 {∅} _ = keep (drop stop)
  ⊆-completeness1 {Γ , C} _ = keep (drop ⊆-refl)


mutual
  completeness-↑ : ∀ {Γ C} → Γ ⊢+↑ C → Γ ⇒ C
  completeness-↑ (⊃-i p) = ⊃-r (completeness-↑ p)
  completeness-↑ (⊥-e x) = ⊥-l (completeness-↓ x (init here))
  completeness-↑ (change x) = completeness-↓ x (init here) 

  completeness-↓ : ∀ {Γ A C} → Γ ⊢+↓ A → Γ , A ⇒ C → Γ ⇒ C
  completeness-↓ (⊃-e {A = A}{B = B} p x) p' = {!!}
  completeness-↓ (id x) p' = monotonicity (≈-sym (≈-rem x)) p'
  completeness-↓ (change x) p' = cut (completeness-↑ x) p'

-- ⊆-lemma : ∀ {Γ Γ' A B} → (Γ , A) ⊆ Γ' → (Γ' , A) ⇒ B → Γ' ⇒ B
-- ⊆-lemma p (init (inl x)) = init (p (inl x))
-- ⊆-lemma p (init (inr x)) = init x
-- ⊆-lemma p (⊥-l x) = ⊥-l (⊆-lemma p x)
-- ⊆-lemma p (cut x x₁) = cut (init (p here)) (cut x x₁)
-- ⊆-lemma p (⊃-l x x₁) = cut (init (p here)) (⊃-l x x₁)
-- ⊆-lemma p (⊃-r x) = cut (init (p here)) (⊃-r x)

-- ⊆-lemma2 : ∀ {Γ Γ' A} → (Γ , A) ⊆ Γ' →  Γ ⊆ Γ'
-- ⊆-lemma2 {Γ , B} p (inl x) = p (inr (inl x))
-- ⊆-lemma2 {Γ , B} p (inr x) = ⊆-lemma2 (λ z → p (inr z)) x

-- -- weakening for sequents with cut

-- weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⇒ A → Γ' ⇒ A
-- weakening Γ⊆Γ' (init x) = init (Γ⊆Γ' x)
-- weakening Γ⊆Γ' (⊥-l p) = ⊥-l (weakening Γ⊆Γ' p)
-- weakening Γ⊆Γ' (cut p p') = cut (weakening Γ⊆Γ' p) (weakening (⊆-inc Γ⊆Γ') p')
-- weakening Γ⊆Γ' (⊃-l p p') = ⊆-lemma Γ⊆Γ' (⊃-l (weakening (⊆-lemma2 Γ⊆Γ') p)
--                                                (weakening (⊆-inc (⊆-lemma2 Γ⊆Γ')) p'))
-- weakening Γ⊆Γ' (⊃-r p) = ⊃-r (weakening (⊆-inc Γ⊆Γ') p)

-- -- soundness theorem

-- ⊆-swap-head : ∀ {Γ A B} → (Γ , B) ⊆ (Γ , A , B)
-- ⊆-swap-head {∅} (inl refl) = here
-- ⊆-swap-head {Γ , C} (inl x) = inl x
-- ⊆-swap-head {Γ , C} (inr x) = inr (inr x)

-- soundness : ∀ {Γ C} → Γ ⇒ C → Γ ⊢+↑ C
-- soundness (init x) = change (id x)
-- soundness (⊥-l p) = ⊥-e (change (soundness p))
-- soundness (cut p p') = change (⊃-e (change (⊃-i (soundness p'))) (soundness p))
-- soundness (⊃-l p p') = change (⊃-e (change (⊃-i (weakening-↑ ⊆-swap-head (soundness p'))))
--                               (change (⊃-e (id (inl refl)) (weakening-↑ inr (soundness p)))))
-- soundness (⊃-r p) = ⊃-i (soundness p)


-- -- completeness theorem

-- mutual
--   completeness-↑ : ∀ {Γ C} → Γ ⊢+↑ C → Γ ⇒ C
--   completeness-↑ (⊃-i p) = ⊃-r (completeness-↑ p)
--   completeness-↑ (⊥-e p) = ⊥-l (completeness-↓ p)
--   completeness-↑ (change p) = completeness-↓ p

--   completeness-↓ : ∀ {Γ C} → Γ ⊢+↓ C → Γ ⇒ C
--   completeness-↓ (⊃-e p p') with completeness-↓ p | completeness-↑ p'
--   ...| p1 | p2 = {!!}
--   completeness-↓ (id p) = init p
--   completeness-↓ (change p) = completeness-↑ p
