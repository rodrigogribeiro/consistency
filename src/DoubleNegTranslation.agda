module DoubleNegTranslation where

open import Basics
open import Form
open import NatDed renaming (weakening to weak-nd)
open import ClassicNatDed renaming (weakening to weak-c)


-- Gödel double negation translation

ϕ[_] : Form → Form
ϕ[ `⊥ ] = `⊥
ϕ[ p ⊃ p' ] = ϕ[ p ] ⊃ ϕ[ p' ]

σ[_] : Ctx → Ctx
σ[ ∅ ] = ∅
σ[ Γ , p ] = σ[ Γ ] , ϕ[ p ]

-- For minimal propositional logic, it is the identity!

ϕ-id : ∀ A → A ≡ ϕ[ A ]
ϕ-id `⊥ = refl
ϕ-id (A ⊃ A') rewrite sym (ϕ-id A) | sym (ϕ-id A') = refl

σ-id : ∀ Γ → Γ ≡ σ[ Γ ]
σ-id ∅ = refl
σ-id (Γ , A) rewrite sym (σ-id Γ) | sym (ϕ-id A) = refl

-- correctness argument

translation-sound : ∀ {Γ A} → σ[ Γ ] ⊢n ϕ[ A ] → Γ ⊢c A
translation-sound {Γ}{A} p = {!!}

translation-complete : ∀ {Γ A} → Γ ⊢c A → σ[ Γ ] ⊢n ϕ[ A ]
translation-complete {Γ} {A} (id x) rewrite sym (σ-id Γ) | sym (ϕ-id A) = id x
translation-complete {Γ} {A} (raa p) with translation-complete p
...| p1 rewrite sym (σ-id Γ) | sym (ϕ-id A) = {!!}
translation-complete {Γ} {.(_ ⊃ _)} (⊃-i p) = {!!}
translation-complete {Γ} {A} (⊃-e p p₁) = {!!}
