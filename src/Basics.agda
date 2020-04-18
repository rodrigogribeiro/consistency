module Basics where

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a}{A : Set a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {a}{A B : Set a}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

data ⊤ : Set where
  tt : ⊤ 

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

infixr 3 _⊎_

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


id : ∀ {l}{A : Set l} → A → A
id x = x


record _↔_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from-to : ∀ x → from (to x) ≡ x
    to-from : ∀ x → to (from x) ≡ x

-- bijections form an equivalence relation

↔-refl : ∀ {A} → A ↔ A
↔-refl 
  = record {
      to = id
    ; from = id
    ; from-to = λ x → refl
    ; to-from = λ x → refl }

↔-sym : ∀ {A B} → A ↔ B → B ↔ A
↔-sym r
   = record {
     to = _↔_.from r
   ; from = _↔_.to r
   ; from-to = _↔_.to-from r
   ; to-from = _↔_.from-to r }

↔-trans : ∀ {A B C} → A ↔ B → B ↔ C → A ↔ C
↔-trans r r'
  = record {
      to = _↔_.to r' ∘ _↔_.to r
    ; from = _↔_.from r ∘ _↔_.from r'
    ; from-to = {!!}
    ; to-from = {!!} }
