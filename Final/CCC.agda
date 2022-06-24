open import Categories
open import Categories.Products
open import Categories.Terminal

module Final.CCC {a}{b}{C : Cat {a}{b}}
                                    (hasProducts : Products C)
                                    (T : Cat.Obj C)
                                    (hasTerminal : Terminal C T)
                                    where

open import Library hiding (_×_ ; curry ; uncurry)

open Cat C
open Products hasProducts

record CCC : Set (a ⊔ b) where
  infix 4 _⇒_
  field
     _⇒_ : Obj → Obj → Obj
     curry : ∀{X Y Z} → Hom (X × Y) Z → Hom X (Y ⇒ Z)
     uncurry : ∀{X Y Z} → Hom X (Y ⇒ Z) → Hom (X × Y) Z
     lawcurry1 : ∀{X Y Z}{f : Hom (X × Y) Z} → uncurry (curry f) ≅ f
     lawcurry2 : ∀{X Y Z}{f : Hom X (Y ⇒ Z)} → curry (uncurry f) ≅ f
     nat-curry : ∀{X X' Y Z Z'} → {f : Hom X' X}{h : Hom Z Z'}{x : Hom (X × Y) Z}
               →  curry (h ∙ uncurry iden) ∙ curry x ∙ f ≅ curry (h ∙ x ∙ pair f iden)

  apply : ∀{Y Z} → Hom ((Y ⇒ Z) × Y) Z
  apply = uncurry iden    

  {- Ejercicio: completar la definición -}
  map⇒ : ∀{X Y Z} → Hom X Z → Hom (Y ⇒ X) (Y ⇒ Z)
  map⇒ f = curry (f ∙ apply)

  open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
  open import Data.Vec using (Vec; []; _∷_; lookup)
  open import Data.Fin using (Fin; zero; suc; toℕ)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

  infixr 30 _⇛_
  infixr 30 _⊗_

  data Ty : Set where
      base : Ty
      _⊗_ : Ty → Ty → Ty
      _⇛_ : Ty → Ty → Ty

  Ctx : ℕ → Set
  Ctx = Vec Ty

  data Term {n} (Γ : Ctx n) : Ty → Set where
    Var : ∀ {τ} (v : Fin n) → τ ≡ lookup Γ v → Term Γ τ -- lol
    _⊕_ : ∀ {σ τ} → Term Γ (σ ⇛ τ) → Term Γ σ → Term Γ τ -- app
    _×ₚ_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ ⊗ τ) -- pair
    p₁ :  ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ σ -- fst
    p₂ : ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ τ  -- snd
    lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇛ τ) -- abstraccion

  -- Interpretación para tipos como objetos CCC

  ⟦_⟧ₜ : Ty → Obj
  ⟦ base ⟧ₜ = T
  ⟦ (t ⊗ u) ⟧ₜ = ⟦ t ⟧ₜ × ⟦ u ⟧ₜ
  ⟦ (t ⇛ u) ⟧ₜ = ⟦ t ⟧ₜ ⇒ ⟦ u ⟧ₜ

  -- Interpretación para contextos como objetos CCC

  ⟦_⟧ₓ : {n : ℕ} → (Γ : Ctx n) → Obj
  ⟦ [] ⟧ₓ = T
  ⟦ (t ∷ Γ) ⟧ₓ = ⟦ Γ ⟧ₓ × ⟦ t ⟧ₜ

  find : ∀ {n : ℕ} {τ} (m : Fin n) → (Γ : Ctx n) → τ ≡ lookup Γ m → Hom ⟦ Γ ⟧ₓ ⟦ τ ⟧ₜ
  find Data.Fin.0F (x ∷ Γ) refl = π₂
  find (suc m) (x ∷ Γ) refl = (find m Γ refl) ∙ π₁

  -- Interpretacion para términos como flechas CCC

  ⟦_⊢_⟧ₗ : ∀ {n : ℕ} {τ} → (Γ : Ctx n) → Term Γ τ → Hom ⟦ Γ ⟧ₓ ⟦ τ ⟧ₜ
  ⟦ Γ ⊢ Var v x ⟧ₗ = find v Γ x
  ⟦ Γ ⊢ (t ⊕ u) ⟧ₗ = apply ∙ ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩
  ⟦ Γ ⊢ (t ×ₚ u) ⟧ₗ = ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩
  ⟦ Γ ⊢ (p₁ t) ⟧ₗ = π₁ ∙ ⟦ Γ ⊢ t ⟧ₗ 
  ⟦ Γ ⊢ (p₂ t) ⟧ₗ = π₂ ∙ ⟦ Γ ⊢ t ⟧ₗ
  ⟦ Γ ⊢ (lam σ t) ⟧ₗ = curry ⟦ (σ ∷ Γ) ⊢ t ⟧ₗ

  record ReglasLC : Set (a ⊔ b) where
    -- infix 4 _≡ₗ_
    field
      -- _≡ₗ_ : ∀ {n : ℕ} {τ₁ τ₂} → (Γ : Ctx n) → (t : Term Γ τ₁) → (u : Term Γ τ₂) → t ≡ u
      prod₁ : ∀ {n : ℕ} {τ₁ τ₂} → {Γ : Ctx n} → {t : Term Γ τ₁} → {u : Term Γ τ₂} → 
              p₁ (t ×ₚ u) ≡ t
      prod₂ : ∀ {n : ℕ} {τ₁ τ₂} → {Γ : Ctx n} → {t : Term Γ τ₁} → {u : Term Γ τ₂} → 
              p₂ (t ×ₚ u) ≡ u
      prod₃ : ∀ {n : ℕ} {τ σ} → {Γ : Ctx n} → {t : Term Γ (τ ⊗ σ)} → 
              ((p₁ t) ×ₚ (p₂ t)) ≡ t

    proof_prod₁ : ∀ {n : ℕ} {τ₁ τ₂} → {Γ : Ctx n} → {t : Term Γ τ₁} → {u : Term Γ τ₂} →
                  p₁ (t ×ₚ u) ≡ t → (⟦ Γ ⊢ p₁ (t ×ₚ u) ⟧ₗ) ≅ (⟦ Γ ⊢  t ⟧ₗ)
    proof_prod₁ {Γ = Γ} {t = t} {u = u} p = 
      proof 
        π₁ ∙ ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩ 
          ≅⟨ law1 ⟩ 
        ⟦ Γ ⊢ t ⟧ₗ ∎

    -- DUDA: funciona sin tomar el argumento

    proof_prod₂ : ∀ {n : ℕ} {τ₁ τ₂} → {Γ : Ctx n} → {t : Term Γ τ₁} → {u : Term Γ τ₂} →
                  (⟦ Γ ⊢ p₂ (t ×ₚ u) ⟧ₗ) ≅ (⟦ Γ ⊢  u ⟧ₗ)
    proof_prod₂ {Γ = Γ} {t = t} {u = u} = 
      proof 
        π₂ ∙ ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩ 
          ≅⟨ law2 ⟩ 
        ⟦ Γ ⊢ u ⟧ₗ ∎

    proof_prod₃ : ∀ {n : ℕ} {τ σ} → {Γ : Ctx n} → {t : Term Γ (τ ⊗ σ)} → 
                  ⟦ Γ ⊢ ((p₁ t) ×ₚ (p₂ t)) ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ
    proof_prod₃ {Γ = Γ} {t = t} = 
      proof 
        ⟨ π₁ ∙ ⟦ Γ ⊢ t ⟧ₗ , π₂ ∙ ⟦ Γ ⊢ t ⟧ₗ ⟩ 
          ≅⟨ sym (law3 refl refl) ⟩ 
        ⟦ Γ ⊢ t ⟧ₗ ∎
