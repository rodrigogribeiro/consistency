module CutFree where

open import Form

infix 3 _⇒*_

data _⇒*_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒* A
  ⊥-l  : ∀ {Γ A} → Γ ⇒* `⊥ → Γ ⇒* A
  ⊃-l  : ∀ {Γ A B C} → Γ , A ⊃ B ⇒* A → Γ , A ⊃ B , B ⇒* C → (Γ , A ⊃ B) ⇒* C
  ⊃-r  : ∀ {Γ A B} → Γ , A ⇒* B → Γ ⇒* A ⊃ B

∈-contraction : ∀ {Γ Γ' A C} → C ∈ ((Γ , A , A) ∪ Γ') → C ∈ ((Γ , A) ∪ Γ')
∈-contraction {Γ' = ∅} here = here
∈-contraction {Γ' = ∅} (there p) = p
∈-contraction {Γ' = Γ' , B} here = here
∈-contraction {Γ' = Γ' , B} (there p) = there (∈-contraction {Γ' = Γ'} p)

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
