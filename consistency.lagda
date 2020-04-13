\documentclass[12pt]{article}

\usepackage{sbc-template}
\usepackage{graphicx,url}
\usepackage[utf8]{inputenc}
\usepackage[brazil]{babel}
\usepackage[latin1]{inputenc}  
\usepackage{stmaryrd}
\usepackage{amsmath}


%% Code to help Agda/LaTeX backend process symbols
\usepackage{agda}
\usepackage{newunicodechar}
\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{⊥}{$\bot$}
\newunicodechar{⇒}{$\Rightarrow$}
\newunicodechar{∈}{$\in$}
\newunicodechar{⊃}{$\supset$}
\newunicodechar{⊆}{$\subseteq$}
\newunicodechar{⊤}{$\top$}
\newunicodechar{×}{$\times$}
\newunicodechar{∘}{$\circ$}
\newunicodechar{●}{$\bullet$}
\newunicodechar{∀}{$\forall$}
\newunicodechar{→}{$\to$}
\newunicodechar{λ}{$\lambda$}
\newunicodechar{⊢}{$\vdash$}
\newunicodechar{⟦}{$\llbracket$}
\newunicodechar{⟧}{$\rrbracket$}
\newunicodechar{¬}{$\neg$}

\sloppy

\title{A Semantical Proof of Consistency \\for Minimal Implicational Logic in Agda}

\author{Felipe Sasdelli\inst{1}, Maycon Amaro\inst{1}, Rodrigo Ribeiro\inst{1}}


\address{Departamento de Computação -- Universidade Federal de Ouro Preto
  (UFOP)\\
  R. Diogo de Vasconcelos, 122. Pilar -- Ouro Preto -- MG -- Brazil
  \email{\{felipe.sasdelli,maycon.amaro\}@aluno.ufop.edu.br, rodrigo.ribeiro@ufop.edu.br}
}

\begin{document} 

\maketitle

\begin{abstract}
  Consistency is a key property of any logical system. However, consistency proofs usually
  rely on heavy proof theory notions like admissibility of cut. A more semantics based
  approach to consistency proofs is to explore the Curry-Howard correspondence between a logics
  and its correspondent $\lambda$-calculus by using the evaluation of the latter.
  In this work, we describe an Agda formalization of semantics-based consistency proof
  of minimal propositional logic.
\end{abstract}
     
\begin{resumo}
  Consistência é uma importante propriedade de qualquer sistema lógico. Porém, provas de consistência se
  valem de noções de teoria da prova como admissibilidade de corte. Uma outra abordagem para provas
  de consistência consiste em explorar a correspondência de Curry-Howard entre uma lógica 
\end{resumo}

\begin{code}[hide]
module consistency where

  module Basics where

    data ⊤ : Set where
      tt : ⊤ 
  
    data ⊥ : Set where

    ⊥-elim : ∀ {A : Set} → ⊥ → A
    ⊥-elim ()

    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        fst : A
        snd : B

    _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
    g ∘ f = λ x → g (f x)

    ¬_ : Set → Set
    ¬ A = A → ⊥
\end{code}

\begin{code}
  infixr 6 _⊃_

  data Form : Set where
    `⊥  : Form
    _⊃_ : Form → Form → Form

  infixl 4 _,_

  data Ctx : Set where
    ●   : Ctx
    _,_ : Ctx → Form → Ctx
  
  data _∈_ : Form → Ctx → Set where
    here  : ∀ {A Γ} → A ∈ (Γ , A)
    there : ∀ {A A' Γ} → A ∈ Γ → A ∈ (Γ , A')

  _⊆_ : Ctx → Ctx → Set
  Γ ⊆ Γ' = ∀ {t} → t ∈ Γ → t ∈ Γ'

  ⊆-inc : ∀ {Γ Γ' A} → Γ ⊆ Γ' → (Γ , A) ⊆ (Γ' , A)
  ⊆-inc Γ⊆Γ' here = here
  ⊆-inc Γ⊆Γ' (there A∈Γ) = there (Γ⊆Γ' A∈Γ)

  module NatDed where

    infix 3 _⊢n_

    data _⊢n_ : Ctx → Form → Set where
      id : ∀ {Γ A} → A ∈ Γ → Γ ⊢n A
      ⊥-e : ∀ {Γ A} → Γ ⊢n `⊥ → Γ ⊢n A
      ⊃-i : ∀ {Γ A B} → (Γ , A) ⊢n B → Γ ⊢n (A ⊃ B)
      ⊃-e : ∀ {Γ A B} → Γ ⊢n (A ⊃ B) → Γ ⊢n A → Γ ⊢n B

    weakening : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢n A → Γ' ⊢n A
    weakening Γ⊆Γ' (id A∈Γ) = id (Γ⊆Γ' A∈Γ)
    weakening Γ⊆Γ' (⊃-i p) = ⊃-i (weakening (⊆-inc Γ⊆Γ') p)
    weakening Γ⊆Γ' (⊃-e p p') = ⊃-e (weakening Γ⊆Γ' p) (weakening Γ⊆Γ' p')
    weakening Γ⊆Γ' (⊥-e p) = ⊥-e (weakening Γ⊆Γ' p)

    weak-lemma : ∀ {Γ A B} → Γ ⊢n A → Γ , B ⊢n A
    weak-lemma p = weakening (λ B∈Γ → there B∈Γ) p

  module SeqCalc where

    infix 3 _⇒_

    data _⇒_ : Ctx → Form → Set where
      init : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
      ⊥-l  : ∀ {Γ A} → Γ ⇒ `⊥ → Γ ⇒ A
      cut  : ∀ {Γ A B} → Γ ⇒ A → (Γ , A) ⇒ B → Γ ⇒ B
      ⊃-l  : ∀ {Γ A B C} → Γ ⇒ A → (Γ , B) ⇒ C → (Γ , A ⊃ B) ⇒ C
      ⊃-r  : ∀ {Γ A B} → Γ , A ⇒ B → Γ ⇒ A ⊃ B

  module CutFree where

    infix 3 _⇒*_

    data _⇒*_ : Ctx → Form → Set where
      init : ∀ {Γ A} → A ∈ Γ → Γ ⇒* A
      ⊥-l  : ∀ {Γ A} → Γ ⇒* `⊥ → Γ ⇒* A
      ⊃-l  : ∀ {Γ A B C} → Γ ⇒* A → (Γ , B) ⇒* C → (Γ , A ⊃ B) ⇒* C
      ⊃-r  : ∀ {Γ A B} → Γ , A ⇒* B → Γ ⇒* A ⊃ B


    contraction : ∀ {Γ A C} → Γ , A , A ⇒* C → Γ , A ⇒* C
    contraction (init here) = init here
    contraction (init (there x)) = init x
    contraction (⊥-l p) = ⊥-l (contraction p)
    contraction (⊃-l p p') = ⊃-l {!!} {!!}
    contraction (⊃-r p) = {!!}

    admissibility : ∀ {Γ C} A → Γ ⇒* A  → Γ , A ⇒* C → Γ ⇒* C
    admissibility = {!!}



  module Equivalence where
    open Basics
    open NatDed
    open SeqCalc
    open CutFree

    ⇒-sound : ∀ {Γ A} → Γ ⊢n A → Γ ⇒ A
    ⇒-sound (id A∈Γ) = init A∈Γ
    ⇒-sound (⊃-i p) = ⊃-r (⇒-sound p)
    ⇒-sound (⊥-e p) = ⊥-l (⇒-sound p)
    ⇒-sound (⊃-e p p') = cut (⇒-sound p) (⊃-l (⇒-sound p') (init here))

    ⇒-complete : ∀ {Γ A} → Γ ⇒ A → Γ ⊢n A
    ⇒-complete (init A∈Γ) = id A∈Γ
    ⇒-complete (⊥-l p) = ⊥-e (⇒-complete p)
    ⇒-complete (cut p p') = ⊃-e (⊃-i (⇒-complete p'))
                                (⇒-complete p)
    ⇒-complete (⊃-l p p') = ⊃-e (weak-lemma (⊃-i (⇒-complete p')))
                                (⊃-e (id here)
                                     (weak-lemma (⇒-complete p)))
    ⇒-complete (⊃-r p) = ⊃-i (⇒-complete p)


  module Semantics where
    open Basics
    open NatDed
    open SeqCalc
    open Equivalence

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

\end{code}



\bibliographystyle{sbc}
\bibliography{sbc-template}

\end{document}
