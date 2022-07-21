module Final.SimplyTyped where

infixr 7 _⇛_
infixl 7 _⊗_

-- Tipos

data Ty : Set where
  base : Ty
  _⊗_ : Ty → Ty → Ty
  _⇛_ : Ty → Ty → Ty


infix  4 _∋_
infixl 5 _,ₓ_

-- Representación para contextos

data Context : Set where
  ∅   : Context
  _,ₓ_ : Context → Ty → Context

-- Representación para variables con índices de Bruijn (representa el lookup)

data _∋_ : Context → Ty → Set where

  Z : ∀ {Γ A} → Γ ,ₓ A ∋ A

  S_ : ∀ {Γ A B} → Γ ∋ A → Γ ,ₓ B ∋ A

-- Representación para lambda términos

data Term (Γ : Context) : Ty → Set where
  Var : ∀ {τ} → Γ ∋ τ → Term Γ τ -- var
  _⊕_ : ∀ {σ τ} → Term Γ (σ ⇛ τ) → Term Γ σ → Term Γ τ -- app
  _×ₚ_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ ⊗ τ) -- pair
  p₁ :  ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ σ -- fst
  p₂ : ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ τ  -- snd
  lam : ∀ σ {τ} → Term (Γ ,ₓ σ) τ → Term Γ (σ ⇛ τ) -- abstraccion
