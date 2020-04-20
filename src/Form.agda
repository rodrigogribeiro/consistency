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
≈-rem {Γ} p = λ a → record { to = there ; from = [ (λ eq → subst (λ x → x ∈ Γ) (sym eq) p) , id ] ∘ ∈-inv }


{-
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


{-
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
-}
