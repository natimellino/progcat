open import Categories
open import Categories.Products
open import Categories.Terminal
open import Final.SimplyTyped
open import Final.Subst 
open import clase11.CCC

module Final.CategoricalSemantics {a}{b}{C : Cat {a}{b}}
                                  (hasProducts : Products C)
                                  (T : Cat.Obj C)
                                  (hasTerminal : Terminal C T)
                                  (isCCC : CCC hasProducts T hasTerminal)
                                  where


open import Library hiding (_×_ ; curry ; uncurry)

open Cat C
open Products hasProducts
open Terminal hasTerminal
open CCC isCCC

-- Interpretación para tipos como objetos CCC  
⟦_⟧ₜ : Ty → Obj
⟦ base ⟧ₜ = T
⟦ (t ⊗ u) ⟧ₜ = ⟦ t ⟧ₜ × ⟦ u ⟧ₜ
⟦ (t ⇛ u) ⟧ₜ = ⟦ t ⟧ₜ ⇒ ⟦ u ⟧ₜ

-- Interpretación para contextos como objetos CCC

⟦_⟧ₓ : (Γ : Context) → Obj
⟦ ∅ ⟧ₓ = T
⟦ Γ ,ₓ t ⟧ₓ = ⟦ Γ ⟧ₓ × ⟦ t ⟧ₜ

find : ∀ {τ} → (Γ : Context) → (v : Γ ∋ τ) → Hom ⟦ Γ ⟧ₓ ⟦ τ ⟧ₜ
find (Γ ,ₓ x) Z = π₂
find (Γ ,ₓ x) (S v) = (find Γ v) ∙ π₁

-- Interpretacion para términos como flechas CCC

⟦_⊢_⟧ₗ : ∀ {τ} → (Γ : Context) → Term Γ τ → Hom ⟦ Γ ⟧ₓ ⟦ τ ⟧ₜ
⟦ Γ ⊢ Var v ⟧ₗ = find Γ v
⟦ Γ ⊢ (t ⊕ u) ⟧ₗ = apply ∙ ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩
⟦ Γ ⊢ (t ×ₚ u) ⟧ₗ = ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩
⟦ Γ ⊢ (p₁ t) ⟧ₗ = π₁ ∙ ⟦ Γ ⊢ t ⟧ₗ 
⟦ Γ ⊢ (p₂ t) ⟧ₗ = π₂ ∙ ⟦ Γ ⊢ t ⟧ₗ
⟦ Γ ⊢ (lam σ t) ⟧ₗ = curry ⟦ (Γ ,ₓ σ) ⊢ t ⟧ₗ

{-
    A partir de acá demostramos que nuestra interpretación preserva las siguientes
    ecuaciones del lambda calculo formalizadas más arriba:

    1) fst(⟨a, b⟩)       = a
    2) snd(⟨a, b⟩)       = b
    3) ⟨fst(c) , snd(c)⟩ = c
    4) (λx . b) a        = b[a/x]
    5) (λx . c x)        = c (x no ocurre en c)

-}

-- TODO: this :(

open import Categories.Products.Properties hasProducts 
       using (comp-pair ; iden-pair ; iden-comp-pair ; fusion-pair ; fusion)


subs-proof : ∀ {Γ : Context} {A A' : Ty} → {t : Term (Γ ,ₓ A) A'} → {t' : Term Γ A} →
               ⟦ Γ ⊢ t [ t' ] ⟧ₗ ≅ ⟦ (Γ ,ₓ A) ⊢ t ⟧ₗ ∙ ⟨ iden {⟦ Γ ⟧ₓ} , ⟦ Γ ⊢ t' ⟧ₗ ⟩
subs-proof {Γ} {A} {A'} {Var Z} {t'} = 
    proof 
        ⟦ Γ ⊢ Var Z [ t' ] ⟧ₗ 
        ≅⟨ refl ⟩ 
        ⟦ Γ ⊢ t' ⟧ₗ
        ≅⟨ sym law2 ⟩
        π₂ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        (find (Γ ,ₓ A) Z) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        ⟦ (Γ ,ₓ A) ⊢ Var Z ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ∎
subs-proof {Γ} {A} {A'} {Var (S x)} {t'} = 
    proof 
        ⟦ Γ ⊢ Var (S x) [ t' ] ⟧ₗ 
        ≅⟨ refl ⟩ 
        ⟦ Γ ⊢ Var x ⟧ₗ
        ≅⟨ refl ⟩
        find Γ x
        ≅⟨ sym idr ⟩
        (find Γ x) ∙ iden
        ≅⟨ cong (λ y →  (find Γ x) ∙ y) (sym law1) ⟩
        find Γ x ∙ (π₁ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩)
        ≅⟨ sym ass ⟩
        (find Γ x ∙ π₁) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        (find (Γ ,ₓ A) (S x)) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        ⟦ (Γ ,ₓ A) ⊢ Var (S x) ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ 
        ∎
subs-proof {Γ} {A} {A'} {t ⊕ t₁} {t'} = 
    proof 
        ⟦ Γ ⊢ (t ⊕ t₁) [ t' ] ⟧ₗ 
        ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) refl ⟩ 
        ⟦ Γ ⊢ (t [ t' ]) ⊕ (t₁ [ t' ]) ⟧ₗ
        ≅⟨ refl ⟩
        apply ∙ ⟨ ⟦ Γ ⊢ (t [ t' ]) ⟧ₗ , ⟦ Γ ⊢ (t₁ [ t' ]) ⟧ₗ ⟩
        ≅⟨ Library.cong₂ (λ x y → apply ∙ ⟨ x , y ⟩) (subs-proof {t = t}) (subs-proof {t = t₁}) ⟩
        apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ ⟩
        ≅⟨ cong (λ x → apply ∙ x) (sym fusion)⟩
        apply ∙ (⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ⟩ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩)
        ≅⟨ sym ass ⟩
        (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ⟩) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        ⟦ (Γ ,ₓ A) ⊢ t ⊕ t₁ ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ∎
subs-proof {Γ} {A} {.(_ ⊗ _)} {t ×ₚ t₁} {t'} = 
    proof 
        ⟦ Γ ⊢ (t ×ₚ t₁) [ t' ] ⟧ₗ 
        ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) refl ⟩ 
        ⟦ Γ ⊢ (t [ t' ]) ×ₚ (t₁ [ t' ]) ⟧ₗ
        ≅⟨ refl ⟩
        ⟨ ⟦ Γ ⊢ t [ t' ] ⟧ₗ , ⟦ Γ ⊢ t₁ [ t' ] ⟧ₗ ⟩
        ≅⟨ Library.cong₂ (λ x y → ⟨ x , y ⟩) (subs-proof {t = t}) (subs-proof {t = t₁}) ⟩
        ⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ ⟩
        ≅⟨ sym fusion ⟩
        ⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ⟩ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        ⟦ Γ ,ₓ A ⊢ t ×ₚ t₁ ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ 
        ∎
subs-proof {Γ} {A} {A'} {p₁ t} {t'} = 
    proof 
        ⟦ Γ ⊢ p₁ t [ t' ] ⟧ₗ 
        ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) refl ⟩ 
        ⟦ Γ ⊢ p₁ (t [ t' ]) ⟧ₗ
        ≅⟨ refl ⟩
        π₁ ∙ ⟦ Γ ⊢ t [ t' ] ⟧ₗ
        ≅⟨ cong (λ x → π₁ ∙ x) (subs-proof {t = t}) ⟩
        π₁ ∙ (⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ _ ⟧ₗ ⟩)
        ≅⟨ sym ass ⟩
        (π₁ ∙ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        ⟦ Γ ,ₓ A ⊢ p₁ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ 
        ∎
subs-proof {Γ} {A} {A'} {p₂ t} {t'} =
    proof 
        ⟦ Γ ⊢ (p₂ t) [ t' ] ⟧ₗ
        ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) refl ⟩ 
        ⟦ Γ ⊢ p₂ (t [ t' ]) ⟧ₗ
        ≅⟨ refl ⟩
        π₂ ∙ ⟦ Γ ⊢ t [ t' ] ⟧ₗ
        ≅⟨ cong (λ x → π₂ ∙ x) (subs-proof {t = t}) ⟩
        π₂ ∙ (⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ _ ⟧ₗ ⟩)
        ≅⟨ sym ass ⟩
        (π₂ ∙ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
        ≅⟨ refl ⟩
        ⟦ Γ ,ₓ A ⊢ p₂ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ 
        ∎
subs-proof {Γ} {A} {.(σ ⇛ _)} {lam σ t} {t'} = {!   !}

-- open import Properties

β-proof : ∀ {Γ : Context} {A B : Ty} → {e : Term (Γ ,ₓ A) B} → {x : Term Γ A} →
            ⟦ Γ ⊢ lam A e ⊕ x ⟧ₗ ≅ ⟦ Γ ⊢ e [ x ] ⟧ₗ
β-proof {Γ} {A} {B} {e} {x} = proof 
    apply ∙ ⟨ curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
    ≅⟨ cong (λ a → apply ∙ a) (Properties.curry-prop₂ hasProducts T hasTerminal isCCC) ⟩ 
    apply ∙ ((pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩) 
    ≅⟨ sym ass ⟩ 
    (apply ∙ pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
    ≅⟨ congl (Properties.curry-exp hasProducts T hasTerminal isCCC) ⟩
    ⟦ Γ ,ₓ A ⊢ e ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩
    ≅⟨ sym subs-proof ⟩ -- usar la demostracion de la igualdad de la substitucion
    ⟦ Γ ⊢ e [ x ] ⟧ₗ 
    ∎

η-lema₁ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ B} →
            ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ ≅ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁
η-lema₁ {Γ} {A} {B} {Var x} = 
    proof 
        ⟦ Γ ,ₓ A ⊢ weaken (Var x) ⟧ₗ 
        ≅⟨ refl ⟩ 
        ⟦ Γ ,ₓ A ⊢ Var (S x) ⟧ₗ
        ≅⟨ refl ⟩
        find (Γ ,ₓ A) (S x)
        ≅⟨ refl ⟩
        (find Γ x) ∙ π₁
        ≅⟨ refl ⟩
        (⟦ Γ ⊢ Var x ⟧ₗ ∙ π₁) ∎
η-lema₁ {Γ} {A} {B} {u ⊕ u₁} = 
    proof 
        ⟦ Γ ,ₓ A ⊢ weaken (u ⊕ u₁) ⟧ₗ 
        ≅⟨ refl ⟩ 
        ⟦ Γ ,ₓ A ⊢ (weaken u) ⊕ (weaken u₁) ⟧ₗ
        ≅⟨ refl ⟩
        apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ (weaken u) ⟧ₗ , ⟦ Γ ,ₓ A ⊢ (weaken u₁) ⟧ₗ ⟩
        ≅⟨ Library.cong₂ (λ x y → apply ∙ ⟨ x , y ⟩) (η-lema₁ {u = u}) (η-lema₁ {u = u₁}) ⟩
        apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , ⟦ Γ ⊢ u₁ ⟧ₗ ∙ π₁ ⟩
        ≅⟨ (cong (λ x → apply ∙ x) (sym fusion)) ⟩
        apply ∙ (⟨ ⟦ Γ ⊢ u ⟧ₗ , ⟦ Γ ⊢ u₁ ⟧ₗ ⟩ ∙ π₁)
        ≅⟨ sym ass ⟩
        (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ , ⟦ Γ ⊢ u₁ ⟧ₗ ⟩) ∙ π₁
        ≅⟨ refl ⟩
        (⟦ Γ ⊢ u ⊕ u₁ ⟧ₗ ∙ π₁) 
        ∎
η-lema₁ {Γ} {A} {B} {u ×ₚ u₁} = 
    proof 
        ⟦ Γ ,ₓ A ⊢ weaken (u ×ₚ u₁) ⟧ₗ 
        ≅⟨ refl ⟩ 
        ⟦ Γ ,ₓ A ⊢ (weaken u) ×ₚ (weaken u₁) ⟧ₗ
        ≅⟨ refl ⟩
        ⟨ ⟦ Γ ,ₓ A ⊢ (weaken u) ⟧ₗ , ⟦ Γ ,ₓ A ⊢ (weaken u₁) ⟧ₗ ⟩
        ≅⟨ Library.cong₂ (λ x y → ⟨ x , y ⟩) (η-lema₁ {u = u}) (η-lema₁ {u = u₁}) ⟩
        ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , ⟦ Γ ⊢ u₁ ⟧ₗ ∙ π₁ ⟩
        ≅⟨ sym fusion ⟩
        ⟨ ⟦ Γ ⊢ u ⟧ₗ , ⟦ Γ ⊢ u₁ ⟧ₗ ⟩ ∙ π₁
        ≅⟨ refl ⟩
        ⟦ Γ ⊢ u ×ₚ u₁ ⟧ₗ ∙ π₁
    ∎ 
η-lema₁ {Γ} {A} {B} {p₁ u} = 
    proof 
        ⟦ Γ ,ₓ A ⊢ weaken (p₁ u) ⟧ₗ 
        ≅⟨ refl ⟩
        ⟦ Γ ,ₓ A ⊢ p₁ (weaken u) ⟧ₗ
        ≅⟨ refl ⟩
        π₁ ∙ ⟦ Γ ,ₓ A ⊢ (weaken u) ⟧ₗ
        ≅⟨ cong (λ x → π₁ ∙ x) (η-lema₁ {u = u}) ⟩
        π₁ ∙ (⟦ Γ ⊢ u ⟧ₗ ∙ π₁)
        ≅⟨ sym ass ⟩
        (π₁ ∙ ⟦ Γ ⊢ u ⟧ₗ) ∙ π₁
        ≅⟨ refl ⟩
        (⟦ Γ ⊢ p₁ u ⟧ₗ ∙ π₁) 
    ∎

η-lema₁ {Γ} {A} {B} {p₂ u} = 
    proof 
        ⟦ Γ ,ₓ A ⊢ weaken (p₂ u) ⟧ₗ 
        ≅⟨ refl ⟩ 
        ⟦ Γ ,ₓ A ⊢ p₂ (weaken u) ⟧ₗ
        ≅⟨ refl ⟩
        π₂ ∙ ⟦ Γ ,ₓ A ⊢ (weaken u) ⟧ₗ
        ≅⟨ cong (λ x → π₂ ∙ x) (η-lema₁ {u = u}) ⟩
        π₂ ∙ (⟦ Γ ⊢ u ⟧ₗ ∙ π₁)
        ≅⟨ sym ass ⟩
        (π₂ ∙ ⟦ Γ ⊢ u ⟧ₗ) ∙ π₁
        ≅⟨ refl ⟩
        (⟦ Γ ⊢ p₂ u ⟧ₗ ∙ π₁) 
    ∎
η-lema₁ {Γ} {A} {B} {lam σ u} = {!   !}

η-lema₂ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} →
        curry (apply ∙ (pair ⟦ Γ ⊢ u ⟧ₗ (iden {⟦ A ⟧ₜ}))) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-lema₂ {Γ = Γ} {u = u} = proof 
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ cong (λ x → curry x) (Properties.uncurry-exp hasProducts T hasTerminal isCCC) ⟩ 
    curry (uncurry ⟦ Γ ⊢ u ⟧ₗ) 
    ≅⟨ lawcurry2 ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎

η-proof : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} → 
        curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-proof {Γ} {A} {B} {u} = proof 
    curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (apply ∙ ⟨ x , π₂ ⟩)) η-lema₁ ⟩ 
    curry (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (uncurry iden ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , x ⟩)) (sym idl) ⟩
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ η-lema₂ ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎

-- Finalmente demostramos Soundness

soundness : ∀ {τ} → {Γ : Context} → {t : Term Γ τ} → {u : Term Γ τ} →
            (t ≡ₜ u) → (⟦ Γ ⊢ t ⟧ₗ) ≅ (⟦ Γ ⊢ u ⟧ₗ)
soundness pr₁ = law1
soundness pr₂ = law2
soundness pr₃ = sym (law3 refl refl)
soundness β = β-proof
soundness η = η-proof