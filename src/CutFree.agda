module CutFree where

open import Basics
open import Form
open import CtxPerm

infix 3 _⇒*_

data _⇒*_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒* A
  ⊥-l  : ∀ {Γ A} → Γ ⇒* `⊥ → Γ ⇒* A
  ⊃-l  : ∀ {Γ A B C} → Γ , A ⊃ B ⇒* A → Γ , A ⊃ B , B ⇒* C → (Γ , A ⊃ B) ⇒* C
  ⊃-r  : ∀ {Γ A B} → Γ , A ⇒* B → Γ ⇒* A ⊃ B

-- proof of weakening

weakening : ∀ {Γ Γ' C} → Γ ⊆ Γ' → Γ ⇒* C → Γ' ⇒* C
weakening s (init x) = init (s x)
weakening s (⊥-l p) = ⊥-l (weakening s p)
weakening s (⊃-l p p') = {!!}
weakening s (⊃-r p) = ⊃-r (weakening (⊆-inc s) p)


-- proof of exchange

exchange : ∀ {Γ Γ' C} → Γ ~ Γ' → Γ ⇒* C → Γ' ⇒* C
exchange ex (init x) = init (_↔_.to (ex _) x)
exchange ex (⊥-l p) = ⊥-l (exchange ex p)
exchange ex (⊃-l p p') = {!!}
exchange ex (⊃-r p) = ⊃-r (exchange (~-inc ex) p)


-- proof of contraction: this is not general enough. Damn it!!!

∈-contraction : ∀ {Γ Γ1 Γ' A C} → C ∈ ((Γ , A) ∪ (Γ1 , A) ∪ Γ') → C ∈ ((Γ , A) ∪ Γ1 ∪ Γ')
∈-contraction = {!!}

contraction-lemma : ∀ Γ Γ1 Γ' A C → ((Γ , A) ∪ (Γ1 , A) ∪ Γ') ⇒* C → ((Γ , A) ∪ Γ1 ∪ Γ') ⇒* C
contraction-lemma = {!!}

{-

contraction-lemma : ∀ {Γ Γ' A C} → ((Γ , A , A) ∪ Γ') ⇒* C → ((Γ , A) ∪ Γ') ⇒* C
contraction-lemma {Γ' = ∅} (init here) = init here
contraction-lemma {Γ' = ∅} (init (there x)) = init x
contraction-lemma {Γ' = ∅} (⊥-l p) = ⊥-l (contraction-lemma {Γ' = ∅} p)
contraction-lemma {Γ' = ∅} (⊃-l p p') with contraction-lemma {Γ' = ∅} p | contraction-lemma {Γ' = ∅ , _} p'
...| p1 | p2 = ⊃-l p1 p2
contraction-lemma {Γ' = ∅} (⊃-r p) = ⊃-r (contraction-lemma {Γ' = ∅ , _} p)
contraction-lemma {Γ' = Γ' , B} (init here) = init here
contraction-lemma {Γ' = Γ' , B} (init (there x)) = init (there (∈-contraction x))
contraction-lemma {Γ' = Γ' , B} (⊥-l p) = ⊥-l (contraction-lemma {Γ' = Γ' , B} p)
contraction-lemma {Γ' = Γ' , .(_ ⊃ _)} (⊃-l p p') = ⊃-l (contraction-lemma {Γ' = Γ' , _} p) (contraction-lemma {Γ' = Γ' , _ , _} p')
contraction-lemma {Γ' = Γ' , B} (⊃-r p) = ⊃-r (contraction-lemma {Γ' = Γ' , B , _} p)

contraction : ∀ {Γ A C} → Γ , A , A ⇒* C → Γ , A ⇒* C
contraction (init here) = init here
contraction (init (there x)) = init x
contraction (⊥-l p) = ⊥-l (contraction p)
contraction (⊃-l p p') with contraction p | contraction-lemma {Γ' = ∅ , _} p'
...| p1 | p2 = ⊃-l p1 p2
contraction (⊃-r p) with contraction-lemma {Γ' = ∅ , _} p
...| p1 = ⊃-r p1

-}
