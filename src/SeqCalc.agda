module SeqCalc where

open import Form

infix 3 _⇒_

data _⇒_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
  ⊥-l  : ∀ {Γ A} → Γ ⇒ `⊥ → Γ ⇒ A
  cut  : ∀ {Γ A B} → Γ ⇒ A → (Γ , A) ⇒ B → Γ ⇒ B
  ⊃-l  : ∀ {Γ A B C} → Γ ⇒ A → (Γ , B) ⇒ C → (Γ , A ⊃ B) ⇒ C
  ⊃-r  : ∀ {Γ A B} → Γ , A ⇒ B → Γ ⇒ A ⊃ B
