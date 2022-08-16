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
open import Categories.Products.Properties hasProducts
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

-- Interpretación para substituciones como objetos CCC

⟦_⟧s : {Δ Γ : Context} → (Δ ⊢s Γ) → Hom ⟦ Δ ⟧ₓ ⟦ Γ ⟧ₓ
⟦_⟧s {Δ} {∅} σ = t
⟦_⟧s {Δ} {Γ ,ₓ x} σ = ⟨ ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ (σ Z) ⟧ₗ ⟩

-- Interpretación para renamings como flechas CCC
⟦_⊢_⟧ρ : ∀{Δ} → (Γ : Context) → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) → Hom  ⟦ Δ ⟧ₓ ⟦ Γ ⟧ₓ
⟦_⊢_⟧ρ ∅  ρ = t
⟦_⊢_⟧ρ {Δ} (Γ ,ₓ x) ρ = ⟨ ⟦ Γ ⊢ (λ y → ρ (S y)) ⟧ρ , find Δ (ρ Z) ⟩

{-
    A partir de acá demostramos que nuestra interpretación preserva las siguientes
    ecuaciones del lambda calculo formalizadas más arriba:

    1) fst(⟨a, b⟩)       = a
    2) snd(⟨a, b⟩)       = b
    3) ⟨fst(c) , snd(c)⟩ = c
    4) (λx . b) a        = b[a/x]
    5) (λx . c x)        = c (x no ocurre en c)

-}

lrho : ∀{Γ Δ} → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) → ⟦ (λ x → Var (ρ x)) ⟧s ≅ ⟦ Γ ⊢ ρ ⟧ρ  
lrho {∅} ρ = refl
lrho {Γ ,ₓ x} ρ = cong₂ ⟨_,_⟩ ((lrho (λ y → ρ (S y)))) refl

lemarho : ∀{Δ B} →  (Γ : Context) → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) → 
          ⟦ Γ ⊢ (λ x → S_ {B = B} (ρ x)) ⟧ρ ≅ ⟦ Γ ⊢ ρ ⟧ρ ∙ π₁ {⟦ Δ ⟧ₓ} {⟦ B ⟧ₜ}
lemarho ∅ ρ = law
lemarho {Δ} (Γ ,ₓ x) ρ = proof
                ⟦ Γ ,ₓ x ⊢ (λ x₁ → S ρ x₁) ⟧ρ
              ≅⟨ refl ⟩
                ⟨ ⟦ Γ ⊢ (λ y → S ρ (S y)) ⟧ρ , find Δ (ρ Z) ∙ π₁ ⟩
              ≅⟨ cong₂ ⟨_,_⟩ (lemarho Γ ((λ y → ρ (S y)))) refl ⟩
                ⟨ ⟦ Γ ⊢ (λ {A} z → ρ (S z)) ⟧ρ ∙ π₁ , find Δ (ρ Z) ∙ π₁ ⟩
              ≅⟨ sym fusion ⟩
                (⟨ ⟦ Γ ⊢ (λ {A} z → ρ (S z)) ⟧ρ , find Δ (ρ Z) ⟩) ∙ π₁
              ≅⟨ refl ⟩
                ⟦ Γ ,ₓ x ⊢ ρ ⟧ρ ∙ π₁
              ∎

idrho : ∀{Γ} → ⟦ Γ ⊢ id ⟧ρ ≅ iden { ⟦ Γ ⟧ₓ}
idrho {∅} = law
idrho {Γ ,ₓ x} = proof 
           ⟦ Γ ,ₓ x ⊢ id ⟧ρ
          ≅⟨ refl ⟩
            ⟨ ⟦ Γ ⊢ S_ ⟧ρ , π₂ ⟩
          ≅⟨ cong₂ ⟨_,_⟩ (lemarho Γ id) refl ⟩
            ⟨ ⟦ Γ ⊢ id ⟧ρ ∙ π₁ , π₂ ⟩
          ≅⟨ cong₂ ⟨_,_⟩ (congl (idrho {Γ})) refl ⟩
             ⟨ iden ∙ π₁ , π₂ ⟩
          ≅⟨ cong₂ ⟨_,_⟩ idl refl ⟩   
            ⟨ π₁ , π₂ ⟩
          ≅⟨ sym (law3 idr idr) ⟩
            iden {⟦ Γ ,ₓ x ⟧ₓ}
          ∎

{---------}

lemaSubstVar : (Γ : Context) → (⟦_⟧s {Γ} {Γ} (λ x → Var x))  ≅ iden { ⟦ Γ ⟧ₓ}
lemaSubstVar Γ = trans (lrho {Γ} {Γ} id) (idrho {Γ})

varWeakLema : ∀ {Γ Δ : Context} {A X : Ty} {x : Γ ∋ A } → (σ : Δ ⊢s (Γ ,ₓ X)) →
        ⟦ Γ ⊢ Var x ⟧ₗ ∙ ⟦ weakσ σ ⟧s ≅  ⟦ Δ ⊢ σ (S x) ⟧ₗ
varWeakLema {.(_ ,ₓ A)} {Δ} {A} {X} {Z} σ = law2
varWeakLema {.(_ ,ₓ _)} {Δ} {A} {X} {S x} σ = trans ass (trans (congr law1) (trans (varWeakLema (weakσ σ)) refl))

{-
lemarho : ∀{Δ B} →  (Γ : Context) → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) → 
          ⟦ Γ ⊢ (λ x → S_ {B = B} (ρ x)) ⟧ρ ≅ ⟦ Γ ⊢ ρ ⟧ρ ∙ π₁ {⟦ Δ ⟧ₓ} {⟦ B ⟧ₜ}
-}

weakSubsLema : ∀ {Γ Δ : Context} {σ : Δ ⊢s Γ} →  
               ⟦ weakσ (exts σ) ⟧s ≅ ⟦ σ ⟧s ∙ π₁
weakSubsLema {Γ} {Δ} {σ} = {!   !}

-- weakenVarLemma : ∀{Γ Γ' A} → (x : Γ ∋ A) →  (ρ : ∀ {B} → Γ ∋ B → Δ ∋ B) 
--                → find Γ' (weaken x) ≅ find Γ x ∙ ⟦ ρ ⟧ρ
-- weakenVarLemma = ?

curry-prop₁ : ∀{X X' Y Z} → {g : Hom X' X}{f : Hom (X × Y) Z} →
              curry f ∙ g ≅ curry (f ∙ pair g iden)
curry-prop₁ {g = g} {f} = proof 
                              curry f ∙ g
                            ≅⟨ sym idl ⟩
                              iden ∙ curry f ∙ g
                            ≅⟨ congl (sym lawcurry2) ⟩
                              curry (uncurry iden) ∙  curry f ∙ g
                            ≅⟨ cong (λ x → curry x ∙ curry f ∙ g) (sym idl) ⟩
                              curry (iden ∙ uncurry iden) ∙  curry f ∙ g
                            ≅⟨ nat-curry ⟩
                              curry (iden ∙ f ∙ pair g iden)
                            ≅⟨ cong (λ x → curry x) idl ⟩
                              curry (f ∙ pair g iden) 
                            ∎

{-------------------------------------------------------------------------------}

substitutionSemantics : ∀ {Γ Δ : Context} {A : Ty} → (t : Term Γ A) → (σ : Δ ⊢s Γ) →
           ⟦ Δ ⊢ sub σ t ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ σ ⟧s
substitutionSemantics {Γ ,ₓ x₁} (Var Z) σ = sym law2
substitutionSemantics {Γ ,ₓ x₁} {Δ} (Var (S x)) σ = 
  proof 
    ⟦ Δ ⊢ sub σ (Var (S x)) ⟧ₗ 
    ≅⟨ refl ⟩ 
    ⟦ Δ ⊢ σ (S x) ⟧ₗ
    ≅⟨ sym (varWeakLema σ) ⟩ -- {Γ} {Δ} {x₁} {x} 
    ⟦ Γ ⊢ (Var x) ⟧ₗ ∙ ⟦ weakσ σ ⟧s
    ≅⟨ refl ⟩
    (find Γ x) ∙ ⟦ weakσ σ ⟧s
    ≅⟨ congr (sym law1) ⟩
    (find Γ x) ∙ (π₁ ∙ ⟨ ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ (σ Z) ⟧ₗ ⟩) 
    ≅⟨ sym ass ⟩
    (find Γ x ∙ π₁) ∙ ⟨ ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ σ Z ⟧ₗ ⟩
    ≅⟨ refl ⟩
    find (Γ ,ₓ x₁) (S x) ∙ ⟨ ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ σ Z ⟧ₗ ⟩
    ≅⟨ refl ⟩
    find (Γ ,ₓ x₁) (S x) ∙ ⟦ σ ⟧s
    ≅⟨ refl ⟩
    ⟦ Γ ,ₓ x₁ ⊢ (Var (S x)) ⟧ₗ ∙ ⟦ σ ⟧s
    ∎
substitutionSemantics {Γ} {Δ} (t₁ ⊕ t₂) σ = 
  proof 
  ⟦ Δ ⊢ sub σ (t₁ ⊕ t₂) ⟧ₗ
  ≅⟨ refl ⟩
  ⟦ Δ ⊢ (sub σ t₁) ⊕ (sub σ t₂) ⟧ₗ
  ≅⟨ refl ⟩
  apply ∙ ⟨ ⟦ Δ ⊢ (sub σ t₁) ⟧ₗ , ⟦ Δ ⊢ (sub σ t₂) ⟧ₗ ⟩
  ≅⟨ congr (cong₂ (λ x y → ⟨ x , y ⟩) (substitutionSemantics t₁ σ) (substitutionSemantics t₂ σ)) ⟩
  apply ∙ ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ σ ⟧s , ⟦ Γ ⊢ t₂ ⟧ₗ ∙ ⟦ σ ⟧s ⟩
  ≅⟨ congr (sym fusion) ⟩
  apply ∙ (⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ σ ⟧s)
  ≅⟨ sym ass ⟩
  (apply ∙ ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩) ∙ ⟦ σ ⟧s 
  ≅⟨ refl ⟩
  ⟦ Γ ⊢ t₁ ⊕ t₂ ⟧ₗ ∙ ⟦ σ ⟧s
  ∎
substitutionSemantics {Γ} {Δ} (t₁ ×ₚ t₂) σ = 
  proof 
  ⟦ Δ ⊢ sub σ (t₁ ×ₚ t₂) ⟧ₗ
  ≅⟨ refl ⟩
  ⟦ Δ ⊢ (sub σ t₁) ×ₚ (sub σ t₂) ⟧ₗ
  ≅⟨ refl ⟩
  ⟨ ⟦ Δ ⊢ (sub σ t₁) ⟧ₗ , ⟦ Δ ⊢ (sub σ t₂) ⟧ₗ ⟩
  ≅⟨ cong₂ (λ x y → ⟨ x , y ⟩) (substitutionSemantics t₁ σ) (substitutionSemantics t₂ σ) ⟩
  ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ σ ⟧s , ⟦ Γ ⊢ t₂ ⟧ₗ ∙ ⟦ σ ⟧s ⟩
  ≅⟨ sym fusion ⟩
  ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ σ ⟧s
  ≅⟨ refl ⟩
  ⟦ Γ ⊢ t₁ ×ₚ t₂ ⟧ₗ ∙ ⟦ σ ⟧s 
  ∎
substitutionSemantics {Γ} {Δ} (p₁ t₁) σ =
  proof
  ⟦ Δ ⊢ sub σ (p₁ t₁) ⟧ₗ
  ≅⟨ refl ⟩
  ⟦ Δ ⊢ p₁ (sub σ t₁) ⟧ₗ
  ≅⟨ refl ⟩
  π₁ ∙ ⟦ Δ ⊢ sub σ t₁ ⟧ₗ
  ≅⟨ congr (substitutionSemantics t₁ σ) ⟩
  π₁ ∙ (⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ σ ⟧s)
  ≅⟨ sym ass ⟩
  (π₁ ∙ ⟦ Γ ⊢ t₁ ⟧ₗ) ∙ ⟦ σ ⟧s
  ≅⟨ refl ⟩
  ⟦ Γ ⊢ p₁ t₁ ⟧ₗ ∙ ⟦ σ ⟧s 
  ∎
substitutionSemantics {Γ} {Δ} (p₂ t₁) σ = 
  proof
  ⟦ Δ ⊢ sub σ (p₂ t₁) ⟧ₗ
  ≅⟨ refl ⟩
  ⟦ Δ ⊢ p₂ (sub σ t₁) ⟧ₗ
  ≅⟨ refl ⟩
  π₂ ∙ ⟦ Δ ⊢ sub σ t₁ ⟧ₗ
  ≅⟨ congr (substitutionSemantics t₁ σ) ⟩
  π₂ ∙ (⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ σ ⟧s)
  ≅⟨ sym ass ⟩
  (π₂ ∙ ⟦ Γ ⊢ t₁ ⟧ₗ) ∙ ⟦ σ ⟧s
  ≅⟨ refl ⟩
  ⟦ Γ ⊢ p₂ t₁ ⟧ₗ ∙ ⟦ σ ⟧s 
  ∎
substitutionSemantics {Γ} {Δ} {A} (lam σ₁ t₁) σ = 
  proof 
    ⟦ Δ ⊢ sub σ (lam σ₁ t₁) ⟧ₗ
    ≅⟨ refl ⟩
    ⟦ Δ ⊢ lam σ₁ (sub (exts σ) t₁) ⟧ₗ
    ≅⟨ refl ⟩
    curry ⟦ Δ ,ₓ σ₁ ⊢ (sub (exts σ) t₁) ⟧ₗ
    ≅⟨ cong curry (substitutionSemantics {Γ ,ₓ σ₁} {Δ ,ₓ σ₁} t₁ ((exts σ))) ⟩
    curry (⟦ Γ ,ₓ σ₁ ⊢ t₁ ⟧ₗ ∙ ⟦ exts σ ⟧s)
    ≅⟨ cong curry (congr (cong₂ ⟨_,_⟩ weakSubsLema (sym idl))) ⟩
    curry (⟦ Γ ,ₓ σ₁ ⊢ t₁ ⟧ₗ ∙ pair ⟦ σ ⟧s iden)
    ≅⟨ sym curry-prop₁ ⟩
    (⟦ Γ ⊢ lam σ₁ t₁ ⟧ₗ ∙ ⟦ σ ⟧s) ∎

singleSubstitutionSemantics : ∀ {Γ : Context} {A A' : Ty} → (t : Term (Γ ,ₓ A) A') → (t' : Term Γ A) →
               ⟦ Γ ⊢ t [ t' ] ⟧ₗ ≅ ⟦ (Γ ,ₓ A) ⊢ t ⟧ₗ ∙ ⟨ iden {⟦ Γ ⟧ₓ} , ⟦ Γ ⊢ t' ⟧ₗ ⟩
singleSubstitutionSemantics {Γ} {A} {A'} t t' = 
    proof
    ⟦ Γ ⊢ t [ t' ] ⟧ₗ
    ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) aux ⟩
    ⟦ Γ ⊢ sub (single t') t ⟧ₗ
    ≅⟨ substitutionSemantics t (single t') ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟦ (single t') ⟧s
    ≅⟨ refl ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ ⟦ weakσ (single t') ⟧s , ⟦ Γ ⊢ (single t' Z) ⟧ₗ ⟩
    ≅⟨ refl ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ ⟦ weakσ (single t') ⟧s , ⟦ Γ ⊢ t' ⟧ₗ ⟩
    ≅⟨ congr (cong (λ x → ⟨ x , ⟦ Γ ⊢ t' ⟧ₗ ⟩) (lemaSubstVar Γ)) ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
    ∎
    where 
          aux :  t [ t' ] ≅ sub (single t') t
          aux = refl

{-------}

-- β-proof : ∀ {Γ : Context} {A B : Ty} → {e : Term (Γ ,ₓ A) B} → {x : Term Γ A} →
--             ⟦ Γ ⊢ lam A e ⊕ x ⟧ₗ ≅ ⟦ Γ ⊢ e [ x ] ⟧ₗ
-- β-proof {Γ} {A} {B} {e} {x} = proof 
--     apply ∙ ⟨ curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
--     ≅⟨ cong (λ a → apply ∙ a) (Properties.curry-prop₂ hasProducts T hasTerminal isCCC) ⟩ 
--     apply ∙ ((pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩) 
--     ≅⟨ sym ass ⟩ 
--     (apply ∙ pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
--     ≅⟨ congl (Properties.curry-exp hasProducts T hasTerminal isCCC) ⟩
--     ⟦ Γ ,ₓ A ⊢ e ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩
--     ≅⟨ sym subs-proof ⟩ -- usar la demostracion de la igualdad de la substitucion
--     ⟦ Γ ⊢ e [ x ] ⟧ₗ 
--     ∎

{-

(find Γ x ∙ π₁) ∙ π₁ ≅
      (find Γ x ∙ π₁) ∙ ⟨ ⟦ Γ ⊢ (λ {A = A₁} y → rho (S y)) ⟧ρ , π₂ ∙ π₁ ⟩
-}

renamingLemma : ∀ {Γ : Context} {A B : Ty} {t : Term Γ A} →
                ⟦ Γ ,ₓ B ⊢ (rename rho t) ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ Γ  ⊢ rho ⟧ρ
renamingLemma {.(_ ,ₓ Γ')} {Γ'} {A} {Var Z} = sym law2
renamingLemma {.(_ ,ₓ _)} {Γ'} {A} {Var (S x)} = {!   !}
renamingLemma {Γ} {Γ'} {A} {t₁ ⊕ t₂} = {!   !}
renamingLemma {Γ} {.(_ ⊗ _)} {A} {t₁ ×ₚ t₂} = {!   !}
renamingLemma {Γ} {Γ'} {A} {p₁ t₁} = {!   !}
renamingLemma {Γ} {Γ'} {A} {p₂ t₁} = {!   !}
renamingLemma {Γ} {.(σ ⇛ _)} {A} {lam σ t₁} = {!   !}

η-lema₁ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ B} →
            ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ ≅ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁
η-lema₁ {Γ} {A} {B} {u} = trans renamingLemma (congr idl)

η-lema₂ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} →
        curry (apply ∙ (pair ⟦ Γ ⊢ u ⟧ₗ (iden {⟦ A ⟧ₜ}))) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-lema₂ {Γ = Γ} {u = u} = proof 
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ cong (λ x → curry x) (Properties.uncurry-exp hasProducts T hasTerminal isCCC) ⟩ 
    curry (uncurry ⟦ Γ ⊢ u ⟧ₗ) 
    ≅⟨ lawcurry2 ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎

-- η-proof : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} → 
--         curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) ≅ ⟦ Γ ⊢ u ⟧ₗ
-- η-proof {Γ} {A} {B} {u} = proof 
--     curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) 
--     ≅⟨ cong (λ x → curry (apply ∙ ⟨ x , π₂ ⟩)) η-lema₁ ⟩ 
--     curry (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , π₂ ⟩) 
--     ≅⟨ cong (λ x → curry (uncurry iden ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , x ⟩)) (sym idl) ⟩
--     curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
--     ≅⟨ η-lema₂ ⟩ 
--     ⟦ Γ ⊢ u ⟧ₗ 
--     ∎

-- Finalmente demostramos Soundness

-- soundness : ∀ {τ} → {Γ : Context} → {t : Term Γ τ} → {u : Term Γ τ} →
--             (t ≡ₜ u) → (⟦ Γ ⊢ t ⟧ₗ) ≅ (⟦ Γ ⊢ u ⟧ₗ)
-- soundness pr₁ = law1
-- soundness pr₂ = law2
-- soundness pr₃ = sym (law3 refl refl)
-- soundness β = β-proof
-- soundness η = η-proof