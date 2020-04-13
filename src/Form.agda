module Form where

open import Basics

infixr 6 _⊃_

data Form : Set where
  `⊥  : Form
  _⊃_ : Form → Form → Form

infixl 4 _,_

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Form → Ctx

data _∈_ : Form → Ctx → Set where
  here  : ∀ {A Γ} → A ∈ (Γ , A)
  there : ∀ {A A' Γ} → A ∈ Γ → A ∈ (Γ , A')

_⊆_ : Ctx → Ctx → Set
Γ ⊆ Γ' = ∀ {t} → t ∈ Γ → t ∈ Γ'

⊆-inc : ∀ {Γ Γ' A} → Γ ⊆ Γ' → (Γ , A) ⊆ (Γ' , A)
⊆-inc Γ⊆Γ' here = here
⊆-inc Γ⊆Γ' (there A∈Γ) = there (Γ⊆Γ' A∈Γ)

