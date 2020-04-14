module Form where

open import Basics

infixr 6 _⊃_

data Form : Set where
  `⊥  : Form
  _⊃_ : Form → Form → Form

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

infixl 4 _,_

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Form → Ctx


_∪_ : Ctx → Ctx → Ctx
∅ ∪ Γ' = Γ'
(Γ , A) ∪ Γ' = (Γ ∪ Γ') , A

data _∈_ : Form → Ctx → Set where
  here  : ∀ {A Γ} → A ∈ (Γ , A)
  there : ∀ {A A' Γ} → A ∈ Γ → A ∈ (Γ , A')

∈-inv : ∀ {α β Γ} → α ∈ (Γ , β) → (α ≡ β) ⊎ (α ∈ Γ)
∈-inv here = inl refl
∈-inv (there p) = inr p


_∈?_ : ∀ α Γ → Dec (α ∈ Γ)
α ∈? ∅ = no (λ ())
α ∈? (Γ , β) with α ≟ β
α ∈? (Γ , β) | yes p rewrite p = yes here
α ∈? (Γ , β) | no  q with α ∈? Γ
α ∈? (Γ , β) | no  q | yes p = yes (there p)
α ∈? (Γ , β) | no  q | no  p = no ([ q , p ] ∘ ∈-inv)

remDups : Ctx → Ctx
remDups ∅ = ∅
remDups (Γ , α) with α ∈? Γ
... | yes p = remDups Γ
... | no  _ = (remDups Γ) , α

_⊆_ : Ctx → Ctx → Set
Γ ⊆ Γ' = ∀ {t} → t ∈ Γ → t ∈ Γ'

⊆-inc : ∀ {Γ Γ' A} → Γ ⊆ Γ' → (Γ , A) ⊆ (Γ' , A)
⊆-inc Γ⊆Γ' here = here
⊆-inc Γ⊆Γ' (there A∈Γ) = there (Γ⊆Γ' A∈Γ)

