module Form where

open import Basics

infixr 6 _⊃_

data Form : Set where
  `⊥  : Form
  _⊃_ : Form → Form → Form

-- negation abbreviation

~_ : Form → Form
~ A = A ⊃ `⊥

-- decidable equality

≡-inv : ∀ {α β α' β'} → (α ⊃ β) ≡ (α' ⊃ β') → (α ≡ α') × (β ≡ β')
≡-inv refl = refl , refl

_≟_ : ∀ (α β : Form) → Dec (α ≡ β)
`⊥ ≟ `⊥ = yes refl
`⊥ ≟ (β ⊃ β') = no (λ ())
(α ⊃ α') ≟ `⊥ = no (λ ())
(α ⊃ α') ≟ (β ⊃ β') with α ≟ β | α' ≟ β'
...| yes p | yes p' rewrite p | p' = yes refl
...| no  p | _      = no (p ∘ fst ∘ ≡-inv)  
...| yes p | no p'  = no (p' ∘ snd ∘ ≡-inv) 

-- context and membership relation

infixl 4 _,_

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Form → Ctx

infixr 6 _∪_

_∪_ : Ctx → Ctx → Ctx
Γ ∪ ∅ = Γ
Γ ∪ (Γ' , A) = (Γ ∪ Γ') , A


data _∈_ : Form → Ctx → Set where
  here  : ∀ {A Γ} → A ∈ (Γ , A)
  there : ∀ {A A' Γ} → A ∈ Γ → A ∈ (Γ , A')

∈-inv : ∀ {α β Γ} → α ∈ (Γ , β) → (α ≡ β) ⊎ (α ∈ Γ)
∈-inv here = inl refl
∈-inv (there p) = inr p

∈-∪-inv : ∀ {Γ Γ' A} → A ∈ (Γ ∪ Γ') → (A ∈ Γ) ⊎ (A ∈ Γ')
∈-∪-inv {Γ} {∅} p = inl p
∈-∪-inv {Γ} {Γ' , B} here = inr here
∈-∪-inv {Γ} {Γ' , B} (there p) with ∈-∪-inv {Γ}{Γ'} p
...| inl q = inl q
...| inr q = inr (there q)

_∈?_ : ∀ α Γ → Dec (α ∈ Γ)
α ∈? ∅ = no (λ ())
α ∈? (Γ , β) with α ≟ β
α ∈? (Γ , β) | yes p rewrite p = yes here
α ∈? (Γ , β) | no  q with α ∈? Γ
α ∈? (Γ , β) | no  q | yes p = yes (there p)
α ∈? (Γ , β) | no  q | no  p = no ([ q , p ] ∘ ∈-inv)

-- lemmas about union and membership

∈-∪-intro-l : ∀ {Γ A} → A ∈ Γ → ∀ {Γ'} → A ∈ (Γ ∪ Γ')
∈-∪-intro-l p {∅} = p
∈-∪-intro-l p {Γ' , x} = there (∈-∪-intro-l p)

∈-∪-intro-r : ∀ {Γ' A} → A ∈ Γ' → ∀ {Γ} → A ∈ (Γ ∪ Γ')
∈-∪-intro-r here = here
∈-∪-intro-r (there p) = there (∈-∪-intro-r p)

-- subset membership (order preserving embedding)

infix 20 _⊆_

data _⊆_ : Ctx → Ctx → Set where
  stop : ∅ ⊆ ∅
  drop : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊆ (Γ' , A)
  keep : ∀ {Γ Γ' A} → Γ ⊆ Γ' → (Γ , A) ⊆ (Γ' , A)


⊆-refl : ∀ {Γ} → Γ ⊆ Γ
⊆-refl {∅} = stop
⊆-refl {Γ , x} = keep ⊆-refl

⊆-trans : ∀ {Γ}{Γ1}{Γ'} → Γ ⊆ Γ1 → Γ1 ⊆ Γ' → Γ ⊆ Γ'
⊆-trans stop stop = stop
⊆-trans stop (drop p') = drop p'
⊆-trans (drop p) (drop p') = drop (⊆-trans (drop p) p')
⊆-trans (drop p) (keep p') = drop (⊆-trans p p')
⊆-trans (keep p) (drop p') = drop (⊆-trans (keep p) p')
⊆-trans (keep p) (keep p') = keep (⊆-trans p p')

∅-⊆ : ∀ {Γ} → ∅ ⊆ Γ
∅-⊆ {∅} = stop
∅-⊆ {Γ , x} = drop ∅-⊆

⊆-∪-∅-r : ∀ {Γ} → Γ ⊆ (Γ ∪ ∅)
⊆-∪-∅-r {∅} = stop
⊆-∪-∅-r {Γ , x} = keep ⊆-∪-∅-r

-- embedding membership proofs

∈-⊆ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → A ∈ Γ → A ∈ Γ'
∈-⊆ (drop p) here = there (∈-⊆ p here)
∈-⊆ (drop p) (there q) = there (∈-⊆ p (there q))
∈-⊆ (keep p) here = here
∈-⊆ (keep p) (there q) = there (∈-⊆ p q)

⊆-∪-l : ∀ Γ Γ' → (Γ ⊆ (Γ ∪ Γ'))
⊆-∪-l Γ ∅ = ⊆-refl
⊆-∪-l Γ (Γ' , x) = drop (⊆-∪-l Γ Γ')

⊆-∪-r : ∀ Γ Γ' → Γ' ⊆ (Γ ∪ Γ')
⊆-∪-r Γ ∅ = ∅-⊆
⊆-∪-r Γ (Γ' , x) = keep (⊆-∪-r Γ Γ')

-- set equality for contexts

_≈_ : Ctx → Ctx → Set
Γ ≈ Γ' = ∀ p → p ∈ Γ ↔ p ∈ Γ'

≈-refl : ∀ {Γ} → Γ ≈ Γ
≈-refl {Γ} = λ p → record { to = id ; from = id }

≈-sym : ∀ {Γ Γ'} → Γ ≈ Γ' → Γ' ≈ Γ
≈-sym r = λ p →
  record { to = _↔_.from (r p) ; from = _↔_.to (r p) }

≈-trans : ∀ {Γ Γ1 Γ'} → Γ ≈ Γ1 → Γ1 ≈ Γ' → Γ ≈ Γ'
≈-trans r r' = λ p →
  record { to =  _↔_.to (r' p) ∘ (_↔_.to (r p))
         ; from = _↔_.from (r p) ∘ _↔_.from (r' p) }

≈-inc : ∀ {Γ Γ' A} → Γ ≈ Γ' → (Γ , A) ≈ (Γ' , A)
≈-inc r p
  = record { to = to' r ; from = to' (≈-sym r) }
    where
      to' : ∀ {Γ Γ' A p} → Γ ≈ Γ'  → p ∈ (Γ , A) → p ∈ (Γ' , A)
      to' r here = here
      to' r (there q) = there (_↔_.to (r _) q)

∈-≈ : ∀ {Γ Γ' A} → Γ ≈ Γ' → A ∈ Γ → A ∈ Γ'
∈-≈ ex p = _↔_.to (ex _) p

≈-rem : ∀ {Γ A} → A ∈ Γ → Γ ≈ (Γ , A)
≈-rem {Γ} p = λ a →
  record {
    to = there
  ; from = [ (λ eq → subst (λ x → x ∈ Γ) (sym eq) p) , id ] ∘ ∈-inv }

-- removing stuff from context

_⊝_ : Ctx → Form → Ctx
∅ ⊝ A = ∅
(Γ , B) ⊝ A with B ≟ A
...| yes eq rewrite eq = Γ ⊝ A
...| no  eq = (Γ ⊝ A) , B

⊝-∪-r : ∀ {Γ Γ' A B} → B ∈ Γ' → A ∈ Γ → B ∈ (Γ ∪ (Γ' ⊝ A))
⊝-∪-r {A = A} {B = B} here p' with B ≟ A
...| yes q rewrite q = ∈-∪-intro-l p'
...| no  q = here
⊝-∪-r {A = A} {B = B} (there {A' = A'} p) p' with A' ≟ A | B ≟ A
... | yes q | yes eq' rewrite q | eq' = ∈-∪-intro-l p'
... | yes q | no x rewrite q = {!!} -- ∈-∪-intro-r {!!}
... | no q | yes x rewrite x = ∈-∪-intro-l p'
... | no q | no x = there (⊝-∪-r p p')
