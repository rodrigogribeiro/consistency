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
∈-∪-inv {Γ' = ∅} p = inl p
∈-∪-inv {Γ' = Γ' , B} here = inr here
∈-∪-inv {Γ' = Γ' , B} (there p) with ∈-∪-inv {Γ' = Γ'} p
... | inl x = inl x
... | inr x = inr (there x)


_∈?_ : ∀ α Γ → Dec (α ∈ Γ)
α ∈? ∅ = no (λ ())
α ∈? (Γ , β) with α ≟ β
α ∈? (Γ , β) | yes p rewrite p = yes here
α ∈? (Γ , β) | no  q with α ∈? Γ
α ∈? (Γ , β) | no  q | yes p = yes (there p)
α ∈? (Γ , β) | no  q | no  p = no ([ q , p ] ∘ ∈-inv)

-- lemmas about union and membership

∪-inl : ∀ {Γ A} → A ∈ Γ → ∀ Γ' → A ∈ (Γ ∪ Γ')
∪-inl p ∅ = p
∪-inl p (Γ' , B) = there (∪-inl p Γ')

-- context subset relation

_⊆_ : Ctx → Ctx → Set
Γ ⊆ Γ' = ∀ {t} → t ∈ Γ → t ∈ Γ'

-- some lemmas about subcontexts

⊆-inc : ∀ {Γ Γ' A} → Γ ⊆ Γ' → (Γ , A) ⊆ (Γ' , A)
⊆-inc Γ⊆Γ' here = here
⊆-inc Γ⊆Γ' (there A∈Γ) = there (Γ⊆Γ' A∈Γ)

⊆-∪-l : ∀ Γ Γ' → (Γ ⊆ (Γ ∪ Γ'))
⊆-∪-l Γ ∅ p = p
⊆-∪-l Γ (Γ' , A) p = there (⊆-∪-l Γ Γ' p)

⊆-∪-r : ∀ Γ Γ' → Γ' ⊆ (Γ ∪ Γ')
⊆-∪-r Γ .(_ , _) here = here
⊆-∪-r Γ .(_ , _) (there p) = there (⊆-∪-r _ _ p)
