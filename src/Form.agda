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
∅ ∪ Γ' = Γ'
(Γ , A) ∪ Γ' = (Γ ∪ Γ') , A

Any : (Form → Set) → Ctx → Set
Any P ∅ = ⊥
Any P (Γ , A) = P A ⊎ Any P Γ

infix 6 _∈_

_∈_ : Form → Ctx → Set
α ∈ Γ = Any (λ β → α ≡ β) Γ 

pattern here = inl refl
pattern there = inr


-- some lemmas about Any

Any-∪ : ∀ (P : Form → Set)(Γ Γ' : Ctx) →
        Any P (Γ ∪ Γ') ↔ ((Any P Γ) ⊎ (Any P Γ'))
Any-∪ P ∅ Γ'
  = begin-↔
      Any P Γ'        ↔⟨ ↔-sym ⊎-left-identity ⟩
      (⊥ ⊎ Any P Γ')
    ↔-∎
Any-∪ P (Γ , A) Γ'
  = begin-↔
       (P A) ⊎ (Any P (Γ ∪ Γ'))            ↔⟨ ⊎-cong (P A ↔-∎) (Any-∪ P Γ Γ') ⟩
       (P A) ⊎ ((Any P Γ) ⊎ (Any P Γ'))    ↔⟨ ⊎-assoc ⟩
       (((P A) ⊎ (Any P Γ)) ⊎ (Any P Γ'))
    ↔-∎

-- lemmas about ∈

∈-∪-inv : ∀ {Γ Γ' A} → A ∈ (Γ ∪ Γ') → (A ∈ Γ) ⊎ (A ∈ Γ')
∈-∪-inv {∅} p = inr p
∈-∪-inv {Γ , A} (inl p) rewrite p = inl (inl refl)
∈-∪-inv {Γ , A} (inr p) with ∈-∪-inv {Γ = Γ} p
... | inl p' = inl (inr p')
... | inr p' = inr p'

∈-∪-intro-l : ∀ {Γ Γ' A} → A ∈ Γ → A ∈ (Γ ∪ Γ')
∈-∪-intro-l {Γ , B} {Γ'} {A} (inl x) = inl x
∈-∪-intro-l {Γ , B} {Γ'} {A} (inr x) = inr (∈-∪-intro-l x)

∈-∪-intro-r : ∀ {Γ Γ' A} → A ∈ Γ' → A ∈ (Γ ∪ Γ')
∈-∪-intro-r {∅} p = p
∈-∪-intro-r {Γ , B} p = inr (∈-∪-intro-r p)

∈-inv : ∀ {Γ A B} → B ∈ (Γ , A) → (B ≡ A) ⊎ B ∈ Γ
∈-inv (inl x) = inl x
∈-inv (inr x) = inr x


_∈?_ : ∀ α Γ → Dec (α ∈ Γ)
α ∈? ∅ = no id
α ∈? (Γ , A) with α ≟ A
α ∈? (Γ , A) | yes p rewrite p = yes (inl refl)
α ∈? (Γ , A) | no  p with α ∈? Γ
α ∈? (Γ , A) | no  p | yes q = yes (inr q)
α ∈? (Γ , A) | no  p | no  q = no [ p , q ]

-- subcontext relation

_⊆_ : Ctx → Ctx → Set
Γ ⊆ Γ' = ∀ {t} → t ∈ Γ → t ∈ Γ'

⊆-inc : ∀ {Γ Γ' A} → Γ ⊆ Γ' → (Γ , A) ⊆ (Γ' , A)
⊆-inc {Γ}{Γ'}{A} Γ⊆Γ' {B} p with B ≟ A
⊆-inc {Γ}{Γ'}{A} Γ⊆Γ' {B} p | yes q = inl q
⊆-inc {Γ} {Γ'} {A} Γ⊆Γ' {B} (inl x) | no q = inl x
⊆-inc {Γ} {Γ'} {A} Γ⊆Γ' {B} (inr x) | no q = inr (Γ⊆Γ' x)

⊆-∪-l : ∀ Γ Γ' → (Γ ⊆ (Γ ∪ Γ'))
⊆-∪-l ∅ Γ' = λ ()
⊆-∪-l (Γ , A) Γ' (inl x) = inl x
⊆-∪-l (Γ , A) Γ' (inr x) = inr (⊆-∪-l Γ Γ' x)

⊆-∪-r : ∀ Γ Γ' → Γ' ⊆ (Γ ∪ Γ')
⊆-∪-r ∅ Γ' = λ z → z
⊆-∪-r (Γ , A) Γ' p = inr (⊆-∪-r Γ Γ' p)



{-
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

-- monoidal properties of context permutations

∪-∅-l : ∀ {Γ} → ∅ ∪ Γ ≡ Γ
∪-∅-l {∅} = refl
∪-∅-l {(Γ , A)} rewrite ∪-∅-l {Γ} = refl

∪-∅-r : ∀ {Γ} → Γ ∪ ∅ ≡ Γ
∪-∅-r {Γ} = refl

∪-assoc : ∀ {Γ Γ1 Γ'} → ((Γ ∪ Γ1) ∪ Γ') ≡ (Γ ∪ (Γ1 ∪ Γ'))
∪-assoc {Γ} {Γ1} {∅} = refl
∪-assoc {Γ} {Γ1} {Γ' , A} rewrite ∪-assoc {Γ} {Γ1} {Γ'} = refl

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
-}
