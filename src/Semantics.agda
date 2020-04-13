module Semantics where

open import Basics
open import Form
open import NatDed
open import SeqCalc
open import Equivalence

⟦_⟧ : Form → Set
⟦ `⊥ ⟧ = ⊥
⟦ A ⊃ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

Env : Ctx → Set
Env ● = ⊤
Env (Γ , A) = Env Γ × ⟦ A ⟧

lookup : ∀ {Γ A} → A ∈ Γ → Env Γ → ⟦ A ⟧
lookup here (_ , A) = A
lookup (there A∈Γ) (env , _) = lookup A∈Γ env

-- semantics of natural deduction

⟦_⟧ND : ∀ {Γ A} → Γ ⊢n A → Env Γ → ⟦ A ⟧
⟦ id A∈Γ ⟧ND env = lookup A∈Γ env
⟦ ⊥-e p ⟧ND env = ⊥-elim (⟦ p ⟧ND env)
⟦ ⊃-i p ⟧ND env = λ A → ⟦ p ⟧ND (env , A)
⟦ ⊃-e p p' ⟧ND env = (⟦ p ⟧ND env) (⟦ p' ⟧ND env)

-- semantics of sequent calculus

⟦_⟧SC : ∀ {Γ A} → Γ ⇒ A → Env Γ → ⟦ A ⟧
⟦_⟧SC = ⟦_⟧ND ∘ ⇒-complete

-- consistency proofs

consistency-ND : ¬ (● ⊢n `⊥) 
consistency-ND p = ⟦ p ⟧ND tt

consistency-SC : ¬ (● ⇒ `⊥)
consistency-SC = consistency-ND ∘ ⇒-complete
