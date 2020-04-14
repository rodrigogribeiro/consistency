module Basics where

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ⊤ : Set where
  tt : ⊤ 

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[_,_] : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
[ f , g ] (inl x) = f x
[ f , g ] (inr x) = g x

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

infixr 9 _∘_

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

¬_ : Set → Set
¬ A = A → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

dec : ∀ {P A : Set} → (P → A) → (¬ P → A) → Dec P → A
dec P ¬P (yes p) = P p
dec P ¬P (no ¬p) = ¬P ¬p
