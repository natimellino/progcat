module Final.Subst where

open import Final.SimplyTyped


data _▹_ :  Context → Context → Set where
  iden▹ : ∀{Γ} → Γ ▹ Γ
  wπ▹ : ∀{Γ Γ' A} → Γ' ▹ Γ → (Γ' ,ₓ A) ▹ Γ
  w×▹ : ∀{Γ Γ' A} → Γ' ▹ Γ →  (Γ' ,ₓ A) ▹ (Γ ,ₓ A)

weakenVar : ∀{Γ Γ' A} → Γ ∋ A → Γ' ▹ Γ → Γ' ∋ A
weakenVar x iden▹ = x
weakenVar x (wπ▹ w) = S (weakenVar x w)
weakenVar Z (w×▹ w) = Z
weakenVar (S x) (w×▹ w) = S (weakenVar x w) 

weaken▹ : ∀{Γ Γ' τ} → Γ' ▹ Γ → Term Γ τ →  Term Γ' τ
weaken▹ w (Var x)   = Var (weakenVar x w)
weaken▹ w (t ⊕ t₁)  = weaken▹ w t  ⊕ weaken▹ w t₁ 
weaken▹ w (t ×ₚ t₁) = weaken▹ w t ×ₚ weaken▹ w t₁ 
weaken▹ w (p₁ t)    = p₁ (weaken▹ w t)
weaken▹ w (p₂ t)    = p₂ (weaken▹ w t)
weaken▹ w (lam σ t) = lam σ (weaken▹ (w×▹ w) t)

-- Debilitación de contexto de tipado

weaken : ∀ {Γ A B} → Term Γ A 
           → Term (Γ ,ₓ B) A
weaken {Γ} t = weaken▹ (wπ▹ iden▹) t


exts : ∀ {Γ Δ}
       → (∀ {A} →       Γ ∋ A →     Term Δ A)
       → (∀ {A B} → Γ ,ₓ B ∋ A → Term (Δ ,ₓ B) A)
exts σ Z      =  Var Z
exts σ (S x)  =  weaken (σ x)

-- Substitución simultánea dada una función de mapeo (multiple substitution)

sub : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Term Δ A)
      → (∀ {A} → Term Γ A → Term Δ A)
sub σ (Var x) = σ x
sub σ (t ⊕ t₁) = sub σ t ⊕ sub σ t₁
sub σ (t ×ₚ t₁) = sub σ t ×ₚ sub σ t₁
sub σ (p₁ t) = p₁ (sub σ t)
sub σ (p₂ t) = p₂ (sub σ t)
sub σ (lam σ₁ t) = lam σ₁ (sub (exts σ) t)

-- Definimos la substitución 'común' a partir de la substitución simultánea

_[_] : ∀ {Γ A B} → Term (Γ ,ₓ B) A → Term Γ B
       → Term Γ A
_[_] {Γ} {A} {B} N M = sub {(Γ ,ₓ B)} {Γ} σ {A} N
    where
    σ : ∀ {A} → Γ ,ₓ B ∋ A → Term Γ A
    σ Z      =  M
    σ (S x)  = Var x


{------------------------------------------------------------------------

Formalización de las ecuaciones del lambda cálculo

------------------------------------------------------------------------} 

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
 