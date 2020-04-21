module NatDed where

open import Basics    hiding (id)
open import Form 
open import CtxPerm


infix 3 _⊢n_

data _⊢n_ : Ctx → Form → Set where
  id : ∀ {Γ A} → A ∈ Γ → Γ ⊢n A
  ⊥-e : ∀ {Γ A} → Γ ⊢n `⊥ → Γ ⊢n A
  ⊃-i : ∀ {Γ A B} → (Γ , A) ⊢n B → Γ ⊢n (A ⊃ B)
  ⊃-e : ∀ {Γ A B} → Γ ⊢n (A ⊃ B) → Γ ⊢n A → Γ ⊢n B


--------------------------
-- structural properties
--------------------------


-- 1. exchange

exchange : ∀ {Γ Γ' A} → Γ ~ Γ' → Γ ⊢n A → Γ' ⊢n A
exchange p (id x) = id (~-∈ x p)
exchange p (⊥-e p') = ⊥-e (exchange p p')
exchange p (⊃-i p') = ⊃-i (exchange (Skip p) p')
exchange p (⊃-e p' p'') = ⊃-e (exchange p p') (exchange p p'')

-- 2. weakening

weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢n A → Γ' ⊢n A
weakening Γ⊆Γ' (id A∈Γ) = id (∈-⊆ Γ⊆Γ' A∈Γ)
weakening Γ⊆Γ' (⊃-i p) = ⊃-i (weakening (keep Γ⊆Γ') p)
weakening Γ⊆Γ' (⊃-e p p') = ⊃-e (weakening Γ⊆Γ' p) (weakening Γ⊆Γ' p')
weakening Γ⊆Γ' (⊥-e p) = ⊥-e (weakening Γ⊆Γ' p)

-- 3. contraction

contraction-lemma : ∀ Γ Γ1 Γ' {A C} → C ∈ ((Γ , A) ∪ (Γ1 , A) ∪ Γ') → C ∈ (Γ ∪ (Γ1 , A) ∪ Γ')
contraction-lemma Γ Γ1 ∅ p with ∈-∪-inv {Γ = Γ , _}{Γ' = Γ1 , _} p
... | inl here = here
... | inl (there x) = there (∈-∪-intro-l x)
... | inr here = here
... | inr (there x) = there (∈-∪-intro-r x)
contraction-lemma Γ Γ1 (Γ' , B) here = here
contraction-lemma Γ Γ1 (Γ' , B) (there p) = there (contraction-lemma Γ Γ1 Γ' p)

contraction : ∀ {Γ} {Γ1} {Γ'} {A C} → ((Γ , A) ∪ (Γ1 , A) ∪ Γ') ⊢n C → (Γ ∪ (Γ1 , A) ∪ Γ') ⊢n C
contraction {Γ} {Γ1} {Γ'} (id x) = id (contraction-lemma Γ Γ1 Γ' x)
contraction {Γ} {Γ1} {Γ'} (⊥-e p) = ⊥-e (contraction {Γ} {Γ1} {Γ'} p)
contraction {Γ} {Γ1} {Γ'} (⊃-i p) = ⊃-i (contraction {Γ} {Γ1} {(Γ' , _)} p)
contraction {Γ} {Γ1} {Γ'} (⊃-e p p₁) = ⊃-e (contraction {Γ} {Γ1} {Γ'} p) (contraction {Γ} {Γ1} {Γ'} p₁)

-- 4. cut

cut-nd : ∀ {Γ A B} → Γ ⊢n A → Γ , A ⊢n B → Γ ⊢n B
cut-nd (id x) p' = ⊃-e (⊃-i p') (id x)
cut-nd (⊥-e p) p' = ⊥-e p
cut-nd (⊃-i p) p' = ⊃-e (⊃-i p') (⊃-i p)
cut-nd (⊃-e p p₁) p' = ⊃-e (⊃-i p') (⊃-e p p₁)

-- 5. substitution

subst-nd : ∀ {Γ Γ' A C} → (Γ , A) ∪ Γ' ⊢n C → Γ ⊢n A → Γ ∪ Γ' ⊢n C
subst-nd {Γ}{Γ'}(id x) q with ∈-∪-inv {Γ = Γ , _} x
... | inl here = weakening (⊆-∪-l _ _) q
... | inl (there x₁) = id (∈-∪-intro-l x₁)
... | inr x₁ = id (∈-∪-intro-r x₁)
subst-nd (⊥-e p) q = ⊥-e (subst-nd p q)
subst-nd (⊃-i p) q = ⊃-i (subst-nd p q)
subst-nd (⊃-e p p₁) q = ⊃-e (subst-nd p q) (subst-nd p₁ q)
