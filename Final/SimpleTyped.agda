open import Categories
open import Categories.Products
open import Categories.Terminal
open import Final.CCC

module Final.SimpleTyped {a}{b}{C : Cat {a}{b}}
                                        (hasProducts : Products C)
                                        (isCCC C) 
                                        where

open Cat C
open Products hasProducts
open CCC isCCC

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Product

infixr 30 _⇛_
infixr 30 _⊗_

data T : Set where
    base : T
    _⊗_ : T → T → T
    _⇛_ : T → T → T

data LamTerm : Set where
    Var : ℕ → LamTerm -- var
    _⊕_ : LamTerm → LamTerm → LamTerm -- application
    _,_ : LamTerm → LamTerm → LamTerm -- prod
    fs : LamTerm → LamTerm -- fst
    sn : LamTerm → LamTerm -- snd
    Abs : T → LamTerm → LamTerm -- abstraction

Ctx : ℕ → Set
Ctx = Vec T

data Term {n} (Γ : Ctx n) : T → Set where
  Var : ∀ {τ} (v : Fin n) → τ ≡ lookup Γ v → Term Γ τ
  _⊕_ : ∀ {σ τ} → Term Γ (σ ⇛ τ) → Term Γ σ → Term Γ τ
  _,_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ ⊗ τ)
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇛ τ)
