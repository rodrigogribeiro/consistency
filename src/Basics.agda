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

-- equational reasoning

infix  1 begin-≡_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  3 _≡-∎

begin-≡_ : ∀ {a}{A : Set a}{x y : A} → x ≡ y → x ≡ y
begin-≡_ x≡y  =  x≡y

_≡⟨⟩_ : ∀ {a}{A : Set a}(x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y  =  x≡y

_≡⟨_⟩_ : ∀ {a}{A : Set a}(x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

_≡-∎ : ∀ {a}{A : Set a}(x : A) → x ≡ x
x ≡-∎  =  refl


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

infix 0 _↔_

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
    ; from-to = λ x → begin-≡
                       _↔_.from r (_↔_.from r' (_↔_.to r' (_↔_.to r x))) ≡⟨ cong (_↔_.from r) (_↔_.from-to r' (_↔_.to r x)) ⟩
                       _↔_.from r (_↔_.to r x)                           ≡⟨ _↔_.from-to r x ⟩
                       x
                      ≡-∎
    ; to-from = λ x → begin-≡
                         _↔_.to r' (_↔_.to r (_↔_.from r (_↔_.from r' x))) ≡⟨ cong (_↔_.to r') (_↔_.to-from r (_↔_.from r' x)) ⟩
                         _↔_.to r' (_↔_.from r' x)                         ≡⟨ _↔_.to-from r' x ⟩
                         x
                       ≡-∎ }


-- equational reasoning combinators

infix  1 begin-↔_
infixr 2 _↔⟨_⟩_
infix  3 _↔-∎


begin-↔_ : ∀ {A B} → A ↔ B → A ↔ B
begin-↔_ A↔B = A↔B

_↔⟨_⟩_ : ∀ A {B C} → A ↔ B → B ↔ C → A ↔ C
A ↔⟨ A↔B ⟩ B↔C =  ↔-trans A↔B B↔C

_↔-∎ : ∀ A → A ↔ A
A ↔-∎ = ↔-refl 

-- several properties of bijections

private 
  lemma-⊎-left1 : ∀ {A}(x : ⊥ ⊎ A) → inr ([ (λ ()) , id ] x) ≡ x
  lemma-⊎-left1 (inr x) = refl

  lemma-⊎-right1 : ∀ {A}(x : A ⊎ ⊥) → inl ([ id , (λ ()) ] x) ≡ x
  lemma-⊎-right1 (inl x) = refl


  lemma-⊎-assoc1 : ∀ {A B C}(x : A ⊎ B ⊎ C) → 
                 [ [ inl , (λ x₁ → inr (inl x₁)) ] , (λ x₁ → inr (inr x₁)) ]
                 ([ (λ x₁ → inl (inl x₁)) , [ (λ x₁ → inl (inr x₁)) , inr ] ] x) ≡ x
  lemma-⊎-assoc1 (inl x) = refl
  lemma-⊎-assoc1 (inr (inl x)) = refl
  lemma-⊎-assoc1 (inr (inr x)) = refl
  

  lemma-⊎-assoc2 : ∀ {A B C} (x : (A ⊎ B) ⊎ C) →
                   [ (λ x₁ → inl (inl x₁)) , [ (λ x₁ → inl (inr x₁)) , inr ] ]
                   ([ [ inl , (λ x₁ → inr (inl x₁)) ] , (λ x₁ → inr (inr x₁)) ] x) ≡ x
  lemma-⊎-assoc2 (inl (inl x)) = refl
  lemma-⊎-assoc2 (inl (inr x)) = refl
  lemma-⊎-assoc2 (inr x) = refl


  lemma-⊎-cong1 : ∀ {A1 A2 B1 B2}(A1↔A2 : A1 ↔ A2)(B1↔B2 : B1 ↔ B2)(x : A1 ⊎ B1) →
                  [ (λ x₁ → inl (_↔_.from A1↔A2 x₁)) , (λ x₁ → inr (_↔_.from B1↔B2 x₁)) ]
                  ([ (λ x₁ → inl (_↔_.to A1↔A2 x₁)) , (λ x₁ → inr (_↔_.to B1↔B2 x₁)) ] x) ≡ x
  lemma-⊎-cong1 A1↔A2 B1↔B2 (inl x) = cong inl (_↔_.from-to A1↔A2 x)
  lemma-⊎-cong1 A1↔A2 B1↔B2 (inr x) = cong inr (_↔_.from-to B1↔B2 x)

  lemma-⊎-comm : ∀{A B} (x : A ⊎ B) → [ inr , inl ] ([ inr , inl ] x) ≡ x
  lemma-⊎-comm (inl x) = refl
  lemma-⊎-comm (inr x) = refl


⊎-left-identity : ∀ {A} → (⊥ ⊎ A) ↔ A
⊎-left-identity
  = record {
      to = [ (λ ()) , id ]
    ; from = inr
    ; from-to = lemma-⊎-left1
    ; to-from = λ x → refl }

⊎-right-identity : ∀ {A} → (A ⊎ ⊥) ↔ A
⊎-right-identity
  = record {
      to = [ id , (λ ()) ]
    ; from = inl
    ; from-to = lemma-⊎-right1
    ; to-from = λ x → refl }

⊎-assoc : ∀ {A B C} → (A ⊎ (B ⊎ C)) ↔ ((A ⊎ B) ⊎ C)
⊎-assoc
  = record {
      to = [ inl ∘ inl , [ inl ∘ inr , inr ] ]
    ; from = [ [ inl , inr ∘ inl ] , inr ∘ inr ]
    ; from-to = lemma-⊎-assoc1
    ; to-from = lemma-⊎-assoc2 }

⊎-comm : ∀ {A B} → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm
  = record {
      to = [ inr , inl ]
    ; from = [ inr  , inl ]
    ; from-to = lemma-⊎-comm
    ; to-from = lemma-⊎-comm }


⊎-cong : ∀ {A1 A2 B1 B2} → A1 ↔ A2 →
                           B1 ↔ B2 →
                           (A1 ⊎ B1) ↔ (A2 ⊎ B2)
⊎-cong A1↔A2 B1↔B2
  = record {
      to = [ inl ∘ _↔_.to A1↔A2  , inr ∘ _↔_.to B1↔B2 ]
    ; from = [ inl ∘ _↔_.from A1↔A2  , inr ∘ _↔_.from B1↔B2 ]
    ; from-to = lemma-⊎-cong1 A1↔A2 B1↔B2
    ; to-from = lemma-⊎-cong1 (↔-sym A1↔A2) (↔-sym B1↔B2) }
