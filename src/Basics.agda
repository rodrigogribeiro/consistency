module Basics where

data ⊤ : Set where
  tt : ⊤ 

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

¬_ : Set → Set
¬ A = A → ⊥
