module Final.Subst where

open import Final.SimplyTyped

extt : ∀ {Γ} {Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
       → (∀ {A B} → Γ ,ₓ B ∋ A → Δ ,ₓ B ∋ A)
extt ρ Z      =  Z
extt ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
         → (∀ {A} → Γ ∋ A → Δ ∋ A)
         → (∀ {A} → Term Γ A → Term Δ A)
rename ρ (Var x) = Var (ρ x)
rename ρ (t ⊕ t₁) = rename ρ t ⊕ rename ρ t₁
rename ρ (t ×ₚ t₁) = rename ρ t ×ₚ rename ρ t₁
rename ρ (p₁ t) = p₁ (rename ρ t)
rename ρ (p₂ t) = p₂ (rename ρ t)
rename ρ (lam σ t) = lam σ (rename (extt ρ) t)

exts : ∀ {Γ Δ}
       → (∀ {A} →       Γ ∋ A →     Term Δ A)
       → (∀ {A B} → Γ ,ₓ B ∋ A → Term (Δ ,ₓ B) A)
exts σ Z      =  Var Z
exts σ (S x)  =  rename S_ (σ x)

-- Substitución simultánea dada una función de mapeo (multiple substitution)

sub : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Term Δ A)
      → (∀ {A} → Term Γ A → Term Δ A)
sub σ (Var x) = σ x
sub σ (t ⊕ t₁) = sub σ t ⊕ sub σ t₁
sub σ (t ×ₚ t₁) = sub σ t ×ₚ sub σ t₁
sub σ (p₁ t) = p₁ (sub σ t)
sub σ (p₂ t) = p₂ (sub σ t)
sub σ (lam σ₁ t) = lam σ₁ (sub (exts σ) t)

_[_] : ∀ {Γ A B} → Term (Γ ,ₓ B) A → Term Γ B
       → Term Γ A
_[_] {Γ} {A} {B} N M = sub {(Γ ,ₓ B)} {Γ} σ {A} N
    where
    σ : ∀ {A} → Γ ,ₓ B ∋ A → Term Γ A
    σ Z      =  M
    σ (S x)  = Var x

-- Debilitación de contexto de tipado
weaken : ∀ {Γ A B} → Term Γ A 
           → Term (Γ ,ₓ B) A
weaken {Γ} t = rename ρ t
    where
    ρ : ∀ {z B} → Γ ∋ z 
        → (Γ ,ₓ B) ∋ z
    ρ s = S s

-- Formalización de las ecuaciones del lambda cálculo

infixr 7 _≡ₜ_

data _≡ₜ_ : ∀ {Γ : Context} {T : Ty} → Term Γ T → Term Γ T → Set where
    -- Reglas para Pair
    pr₁ : ∀ {Γ : Context} {A B : Ty} → {t₁ : Term Γ A} → {t₂ : Term Γ B} →
            p₁ (t₁ ×ₚ t₂) ≡ₜ t₁

    pr₂ : ∀ {Γ : Context} {A B : Ty} → {t₁ : Term Γ A} → {t₂ : Term Γ B} →
            p₂ (t₁ ×ₚ t₂) ≡ₜ t₂

    pr₃ : ∀ {Γ : Context} {A B : Ty} → {t : Term Γ (A ⊗ B)} →
            (p₁ t) ×ₚ (p₂ t) ≡ₜ t

    -- Eta y Beta

    η : ∀ {Γ : Context} {A B : Ty} → {f : Term Γ (A ⇛ B)} →
        (lam A ((weaken f) ⊕ (Var Z))) ≡ₜ f

    β : ∀ {Γ : Context} {A B : Ty} → {e : Term (Γ ,ₓ A) B} → {x : Term Γ A} →
        ((lam A e) ⊕ x) ≡ₜ (e [ x ])
