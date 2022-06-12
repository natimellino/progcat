module Final.SimpleTyped where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Categories
open import Categories.Products
open import Categories.Terminal
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

-- Ctx : ℕ → Set
-- Ctx = Vec T

-- data Term {n} (Γ : Ctx n) : T → Set where
--   Var : ∀ {τ} (v : Fin n) → τ ≡ lookup Γ v → Term Γ τ
--   _⊕_ : Term Γ base → Term Γ base → Term Γ base
--   lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇛ τ)

module LambdaCat (C : Cat) where
    open Cat C

    LambdaCat : Cat
    LambdaCat = record
            { Obj = T
            ; Hom = {!   !}
            ; iden = {!   !}
            ; _∙_ = {!   !}
            ; idl = {!   !}
            ; idr = {!   !}
            ; ass = {!   !}
            }