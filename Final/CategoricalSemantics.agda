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


{- Interpretaciones como flechas y objetos CCC -}


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

{- / Interpretaciones como flechas y objetos CCC -}

{---------------------------------------------------------------------------------
    A partir de acá demostramos que nuestra interpretación preserva las siguientes
    ecuaciones del lambda calculo formalizadas más arriba:

    1) fst(⟨a, b⟩)       = a
    2) snd(⟨a, b⟩)       = b
    3) ⟨fst(c) , snd(c)⟩ = c
    4) (λx . b) a        = b[a/x]
    5) (λx . c x)        = c (x no ocurre en c)

---------------------------------------------------------------------------------}

{-

Comenzamos con las pruebas para la regla η

-}


{- Demostraciones auxiliares -}

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

lrho : ∀{Γ Δ} → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) → ⟦ (λ x → Var (ρ x)) ⟧s ≅ ⟦ Γ ⊢ ρ ⟧ρ  
lrho {∅} ρ = refl
lrho {Γ ,ₓ x} ρ = cong₂ ⟨_,_⟩ ((lrho (λ y → ρ (S y)))) refl

{-

dem de lrho:

  ⟦ (λ x → Var (ρ x)) ⟧s
  =< refl >
  ⟨ ⟦ weakσ (λ x → Var (ρ x)) ⟧s , ⟦ Δ ⊢ Var (ρ Z) ⟧ₗ ⟩
  =< por definicion de weakσ y ⟦⟧ₗ >
  ⟨ ⟦ (λ y → Var (ρ (S y))) ⟧s , find Δ (ρ Z) ⟩
  =< aplico recursivamente lrho >
  ⟨ ⟦ Γ ⊢ (λ y → Var (ρ (S y))) ⟧ρ , find Δ (ρ Z) ⟩
  =< por definicion de ⟦ _ ⟧ρ >
  ⟦ Γ ⊢ ρ ⟧ρ
-}

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

lemaρS : ∀{Γ B} → ⟦ Γ ⊢ S_ {Γ} {_} {B} ⟧ρ ≅ π₁ {⟦ Γ ⟧ₓ} {⟦ B ⟧ₜ}
lemaρS {Γ}{B} = proof 
                ⟦ Γ ⊢ S_ ⟧ρ
                ≅⟨ lemarho Γ id ⟩
                (⟦ Γ ⊢ (λ x → x) ⟧ρ ∙ π₁)
                ≅⟨ congl (idrho {Γ}) ⟩
                (iden ∙ π₁)
                ≅⟨ idl ⟩
                π₁ 
                ∎

renamingVarLemma : ∀ {Γ Δ : Context} {A : Ty} {x : Γ ∋ A} → (r : ∀ {B} → Γ ∋ B → Δ ∋ B) →
                   find Δ (r x) ≅ find Γ x ∙ ⟦ Γ ⊢ r ⟧ρ
renamingVarLemma {Γ} {Δ} {A} {Z} r = sym law2
renamingVarLemma {Γ} {Δ} {A} {S x} r = trans (trans (renamingVarLemma (λ y → r (S y))) (congr (sym law1))) (sym ass)

renamingLemma : ∀ {Γ Δ : Context}{A} → (t : Term Γ A) → (r : ∀ {B} → Γ ∋ B → Δ ∋ B) →
                ⟦ Δ ⊢ (rename r t) ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ Γ  ⊢ r ⟧ρ
renamingLemma {Γ} {Δ} {A} (Var x) r = renamingVarLemma r -- renamingVarLemma se demuestra similar a applysubstLemma
renamingLemma {Γ} {Δ} {A} (t₁ ⊕ t₂) r = 
  proof
  ⟦ Δ ⊢ rename r (t₁ ⊕ t₂) ⟧ₗ
  ≅⟨ refl ⟩
  ⟦ Δ ⊢ rename r t₁ ⊕ rename r t₂ ⟧ₗ
  ≅⟨ refl ⟩
  apply ∙ ⟨ ⟦ Δ ⊢ rename r t₁ ⟧ₗ , ⟦ Δ ⊢ rename r t₂ ⟧ₗ ⟩
  ≅⟨ congr ( proof
             ⟨ ⟦ Δ ⊢ rename r t₁ ⟧ₗ , ⟦ Δ ⊢ rename r t₂ ⟧ₗ ⟩
             ≅⟨ cong₂ ⟨_,_⟩ (renamingLemma t₁ r) (renamingLemma t₂ r) ⟩
             ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ , ⟦ Γ ⊢ t₂ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ ⟩
             ≅⟨ sym fusion ⟩
             ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ Γ ⊢ r ⟧ρ
             ∎
     )⟩
  apply ∙ (⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ Γ ⊢ r ⟧ρ)
  ≅⟨ sym ass ⟩
  (apply ∙ ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩) ∙ ⟦ Γ ⊢ r ⟧ρ
  ≅⟨ refl ⟩
  ⟦ Γ ⊢ t₁ ⊕ t₂ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ 
  ∎
renamingLemma {Γ} {Δ} {.(_ ⊗ _)} (t₁ ×ₚ t₂) r = proof
                   ⟦ Δ ⊢ rename r (t₁ ×ₚ t₂) ⟧ₗ
                 ≅⟨ cong₂ ⟨_,_⟩ (renamingLemma t₁ r) (renamingLemma t₂ r) ⟩
                   ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ , ⟦ Γ ⊢ t₂ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ ⟩
                 ≅⟨ sym fusion ⟩ 
                   ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ Γ ⊢ r ⟧ρ
                 ∎ 
renamingLemma {Γ} {Δ} {A} (p₁ t₁) r = trans (congr (renamingLemma t₁ r)) (sym ass)
renamingLemma {Γ} {Δ} {A} (p₂ t₁) r = trans (congr (renamingLemma t₁ r)) (sym ass)
renamingLemma {Γ} {Δ} {.(σ ⇛ _)} (lam σ t₁) r = proof
                              ⟦ Δ ⊢ rename r (lam σ t₁) ⟧ₗ
                            ≅⟨ refl ⟩ 
                               curry ⟦ Δ ,ₓ σ ⊢ rename (extt r) t₁ ⟧ₗ
                            ≅⟨ cong curry (proof -- ⟦ Δ ,ₓ σ ⊢ rename (extt r) t₁ ⟧ₗ ≅ ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ pair ⟦ Γ ⊢ r ⟧ρ iden
                                       ⟦ Δ ,ₓ σ ⊢ rename (extt r) t₁ ⟧ₗ
                                    ≅⟨ renamingLemma t₁ (extt r) ⟩ -- HI
                                       ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ ⟦ Γ ,ₓ σ ⊢ extt r ⟧ρ
                                    ≅⟨ refl ⟩ 
                                       ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ ⟨ ⟦ Γ ⊢ (λ x → S_ {_} {_} {σ} (r x)) ⟧ρ , π₂ ⟩
                                    ≅⟨ congr (cong₂ ⟨_,_⟩ (lemarho {Δ} Γ r) (sym idl)) ⟩ -- lemarho : ⟦ Γ ⊢ (λ x → S_ (ρ x)) ⟧ρ ≅ ⟦ Γ ⊢ ρ ⟧ρ ∙ π₁
                                       ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ ⟨ ⟦ Γ ⊢ r ⟧ρ ∙ π₁ , iden ∙ π₂ ⟩
                                    ≅⟨ refl ⟩ 
                                       ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ pair ⟦ Γ ⊢ r ⟧ρ iden
                                    ∎) ⟩
                               curry (⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ pair ⟦ Γ ⊢ r ⟧ρ iden)
                            ≅⟨ sym curry-prop₁ ⟩ 
                               curry ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ
                            ≅⟨ refl ⟩ 
                               ⟦ Γ ⊢ lam σ t₁ ⟧ₗ ∙ ⟦ Γ ⊢ r ⟧ρ
                          ∎                            

{- / Demostraciones auxiliares -}

{- Lemas auxiliares -}

η-lema₁ : ∀ {Γ : Context} {A B : Ty} → (u : Term Γ B) →
            ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ ≅ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ {_} {⟦ A ⟧ₜ}
η-lema₁ {Γ} {A} {B} u = proof
                         ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ
                       ≅⟨ renamingLemma u S_ ⟩
                         ⟦ Γ ⊢ u ⟧ₗ ∙ ⟦ Γ ⊢ S_ ⟧ρ
                       ≅⟨ congr (lemaρS {Γ}) ⟩
                         ⟦ Γ ⊢ u ⟧ₗ ∙ π₁
                      ∎
                    
η-lema₂ : ∀ {Γ : Context} {A B : Ty} → (u : Term Γ (A ⇛ B)) →
        curry (apply ∙ (pair ⟦ Γ ⊢ u ⟧ₗ (iden {⟦ A ⟧ₜ}))) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-lema₂ {Γ = Γ} u = proof 
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ cong (λ x → curry x) (Properties.uncurry-exp hasProducts T hasTerminal isCCC) ⟩ 
    curry (uncurry ⟦ Γ ⊢ u ⟧ₗ) 
    ≅⟨ lawcurry2 ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎

{- / Lemas auxiliares -}

{-
  Prueba para la regla η
-}

η-proof : ∀ {Γ : Context} {A B : Ty} → (u : Term Γ (A ⇛ B)) → 
        curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-proof {Γ} {A} {B} u = proof 
    curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (apply ∙ ⟨ x , π₂ ⟩)) (η-lema₁ u) ⟩ 
    curry (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (uncurry iden ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , x ⟩)) (sym idl) ⟩
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ η-lema₂ u ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎

{------------------------------------------------------------------------------------------------------------------------------------

Demostraciones para la regla β

-------------------------------------------------------------------------------------------------------------------------------------}


{- Demostraciones auxiliares -}


lemaSubstVar : (Γ : Context) → (⟦_⟧s {Γ} {Γ} Var)  ≅ iden { ⟦ Γ ⟧ₓ}
lemaSubstVar Γ = trans (lrho {Γ} id) (idrho {Γ})


lemaRenamingSubst :  ∀ {Δ' Γ Δ : Context} → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) →  (σ : Γ ⊢s Δ')
                  → ⟦ (λ x₁ → rename ρ (σ x₁)) ⟧s ≅ ⟦ σ ⟧s ∙ ⟦ Γ ⊢ ρ ⟧ρ
lemaRenamingSubst {∅} ρ σ = law
lemaRenamingSubst {Δ' ,ₓ x} {Γ} {Δ} ρ σ = 
  proof
  ⟦ (λ x₁ → rename ρ (σ x₁)) ⟧s
  ≅⟨ refl ⟩
  ⟨ ⟦ weakσ (λ x₁ → rename ρ (σ x₁)) ⟧s , ⟦ Δ ⊢ ((λ x₁ → rename ρ (σ x₁)) Z) ⟧ₗ ⟩ -- ⟦ weakσ (λ x₁ → rename ρ (σ x₁)) ⟧s =
                                                                                  -- = ⟦ λ x -> (λ x₁ → rename ρ (σ x₁)) (S x) ⟧s
                                                                                  -- = ⟦ λ x -> rename ρ (σ (S x)))⟧s -> ahora puedo usar HI
                                                                                  
  ≅⟨ cong₂ ⟨_,_⟩ (lemaRenamingSubst ρ (λ x → σ (S x))) (renamingLemma (σ Z) ρ) ⟩ -- ⟦ Δ ⊢ (rename r t) ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ Γ  ⊢ r ⟧ρ
  ⟨ ⟦ (λ x₁ → σ (S x₁)) ⟧s ∙ ⟦ Γ ⊢ ρ ⟧ρ , ⟦ Γ ⊢ σ Z ⟧ₗ ∙ ⟦ Γ ⊢ ρ ⟧ρ ⟩
  ≅⟨ sym fusion ⟩
  ⟦ σ ⟧s ∙ ⟦ Γ ⊢ ρ ⟧ρ 
  ∎

weakSubsLema : ∀ {Γ Δ : Context}{B} (σ : Δ ⊢s Γ) →  
               ⟦ weakσ (exts σ {B}) ⟧s ≅ ⟦ σ ⟧s ∙ π₁ {_} {⟦ B ⟧ₜ}
weakSubsLema {∅} {Δ} {B} σ = law
weakSubsLema {Γ ,ₓ x} {Δ} {B} σ = 
  proof
  ⟦ weakσ (exts σ {B}) ⟧s
  ≅⟨ refl ⟩
  (⟨ ⟦ weakσ (weakσ (exts σ)) ⟧s , ⟦ Δ ,ₓ B ⊢ weakσ (exts σ) Z ⟧ₗ ⟩)
  ≅⟨ refl ⟩
  (⟨ ⟦ (λ x₁ → rename S_ (σ (S x₁))) ⟧s , ⟦ Δ ,ₓ B ⊢ rename S_ (σ Z) ⟧ₗ ⟩)
  ≅⟨ cong₂ ⟨_,_⟩ (lemaRenamingSubst S_ (λ x → σ (S x))) (renamingLemma (σ Z) S_) ⟩ -- ⟦ Δ ⊢ (rename r t) ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ Γ  ⊢ r ⟧ρ
    ⟨ ⟦ (λ x₁ → σ (S x₁)) ⟧s ∙ ⟦ Δ ⊢ S_ ⟧ρ , ⟦ Δ ⊢ σ Z ⟧ₗ ∙ ⟦ Δ ⊢ S_ {_} {_} {B} ⟧ρ ⟩
  ≅⟨ cong₂ ⟨_,_⟩ (congr (lemaρS {Δ})) (congr (lemaρS {Δ})) ⟩ -- lemaρS : ∀{Γ} → ⟦ Γ ⊢ S_ ⟧ρ ≅ π₁
    ⟨ ⟦ weakσ σ ⟧s ∙ π₁ , ⟦ Δ ⊢ σ Z ⟧ₗ ∙ π₁ ⟩
  ≅⟨ sym fusion ⟩
    ⟦ σ ⟧s ∙ π₁
  ∎

applysubstLemma : ∀ {Γ Δ : Context} {A : Ty} → (x : Γ ∋ A ) → (σ : Δ ⊢s Γ) 
                → ⟦ Δ ⊢ σ x ⟧ₗ ≅ find Γ x ∙ ⟦ σ ⟧s
applysubstLemma Z σ = sym law2
applysubstLemma (S x) σ = trans (trans (applysubstLemma x (weakσ σ)) (congr (sym law1))) (sym ass)

{-

Notar que necesariamente Γ ≠ ∅ --> Γ = Γ* , B

Caso Z:

  find Γ Z ∙ ⟦ σ ⟧s
  =< def. find y ⟦ _ ⟧s>
  π₂ ∙ < ⟦ weakσ σ ⟧ , ⟦ Δ ⊢ (σ Z) ⟧ >
  =< law2 >
  ⟦ Δ ⊢ (σ Z) ⟧ -- que es lo que queríamos

Caso S x:
  ⟦ Δ ⊢ (σ (S x)) ⟧
  <si debilitamos σ podemos utilizar la hipotesis inductiva>
  find Γ* x ∙ ⟦ weakσ σ ⟧s
  =< sym law1 >
  find Γ* x ∙ ( π₁ ∙ < ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ (σ Z) ⟧ > )
  =< asociamos >
  (find Γ* x ∙ π₁) ∙ < ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ (σ Z) ⟧ > )
  =< definición de find y definicion de ⟦ _ ⟧s >
  find Γ (S y) ∙ ⟦ σ ⟧s

-}


{- / Demostraciones auxiliares -}


{- Lemas auxiliares -}

-- Lema para substitución simultánea

substitutionSemantics : ∀ {Γ Δ : Context} {A : Ty} → (t : Term Γ A) → (σ : Δ ⊢s Γ) →
           ⟦ Δ ⊢ sub σ t ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ σ ⟧s
substitutionSemantics {Γ} {Δ} (Var x) σ = applysubstLemma x σ
substitutionSemantics {Γ} {Δ} (t₁ ⊕ t₂) σ = trans (congr (trans (cong₂ ⟨_,_⟩ (substitutionSemantics t₁ σ) (substitutionSemantics t₂ σ)) (sym fusion))) (sym ass)
substitutionSemantics {Γ} {Δ} (t₁ ×ₚ t₂) σ = trans (cong₂ ⟨_,_⟩ (substitutionSemantics t₁ σ) (substitutionSemantics t₂ σ)) (sym fusion)
substitutionSemantics {Γ} {Δ} (p₁ t₁) σ = trans (congr (substitutionSemantics t₁ σ)) (sym ass)
substitutionSemantics {Γ} {Δ} (p₂ t₁) σ = trans (congr (substitutionSemantics t₁ σ)) (sym ass)
substitutionSemantics {Γ} {Δ} {A} (lam σ₁ t₁) σ = proof
                           ⟦ Δ ⊢ sub σ (lam σ₁ t₁) ⟧ₗ
                          ≅⟨ refl ⟩
                           ⟦ Δ ⊢ lam σ₁ (sub (exts σ) t₁) ⟧ₗ
                          ≅⟨ refl ⟩
                           curry ⟦ Δ ,ₓ σ₁ ⊢ sub (exts σ) t₁ ⟧ₗ
                          ≅⟨ cong curry (substitutionSemantics t₁ (exts σ)) ⟩ -- Extendemos el contexto de σ para poder usar la HI
                           curry (⟦ Γ ,ₓ σ₁ ⊢ t₁ ⟧ₗ ∙ ⟨ ⟦ (λ x → rename (λ x → S_ {_} {_} {σ₁} x) (σ x)) ⟧s , π₂ ⟩)
                          ≅⟨ cong curry (congr (cong₂ ⟨_,_⟩ ((weakSubsLema {Γ} {Δ} {σ₁} σ)) (sym idl))) ⟩ -- ∀ {Γ Δ : Context}{B} (σ : Δ ⊢s Γ) → ⟦ weakσ (exts σ {B}) ⟧s ≅ ⟦ σ ⟧s ∙ π₁ {_} {⟦ B ⟧ₜ}
                           curry (⟦ Γ ,ₓ σ₁ ⊢ t₁ ⟧ₗ ∙ ⟨ ⟦ σ ⟧s ∙ π₁ , iden ∙ π₂ ⟩)
                          ≅⟨ sym curry-prop₁ ⟩
                           curry ⟦ Γ ,ₓ σ₁ ⊢ t₁ ⟧ₗ ∙ ⟦ σ ⟧s
                          ∎

-- Lema para substitución simple: es un caso particular del lema para substitución simultánea

singleSubstitutionSemantics : ∀ {Γ : Context} {A A' : Ty} → (t : Term (Γ ,ₓ A) A') → (t' : Term Γ A) →
               ⟦ Γ ⊢ t [ t' ] ⟧ₗ ≅ ⟦ (Γ ,ₓ A) ⊢ t ⟧ₗ ∙ ⟨ iden {⟦ Γ ⟧ₓ} , ⟦ Γ ⊢ t' ⟧ₗ ⟩
singleSubstitutionSemantics {Γ} {A} {A'} t t' = 
    proof
    ⟦ Γ ⊢ t [ t' ] ⟧ₗ
    ≅⟨ refl ⟩
    ⟦ Γ ⊢ sub (single t') t ⟧ₗ
    ≅⟨ substitutionSemantics t (single t') ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟦ (single t') ⟧s
    ≅⟨ refl ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ ⟦ weakσ (single t') ⟧s , ⟦ Γ ⊢ (single t' Z) ⟧ₗ ⟩
    ≅⟨ refl ⟩
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ ⟦ weakσ (single t') ⟧s , ⟦ Γ ⊢ t' ⟧ₗ ⟩ -- weakσ (single t') x  termina siendo lo mismo que aplicar Var x por como estan definidas
    ≅⟨ congr (cong (λ x → ⟨ x , ⟦ Γ ⊢ t' ⟧ₗ ⟩) (lemaSubstVar Γ)) ⟩ -- (Γ : Context) → (⟦_⟧s {Γ} {Γ} Var)  ≅ iden { ⟦ Γ ⟧ₓ}
    ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
    ∎


{- / Lemas auxiliares -}

{-
  Prueba para la regla β
-}

β-proof : ∀ {Γ : Context} {A B : Ty} → (e : Term (Γ ,ₓ A) B) → (x : Term Γ A) →
            ⟦ Γ ⊢ lam A e ⊕ x ⟧ₗ ≅ ⟦ Γ ⊢ e [ x ] ⟧ₗ
β-proof {Γ} {A} {B} e x = proof 
    apply ∙ ⟨ curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
    ≅⟨ cong (λ a → apply ∙ a) (Properties.curry-prop₂ hasProducts T hasTerminal isCCC) ⟩ 
    apply ∙ ((pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩) 
    ≅⟨ sym ass ⟩ 
    (apply ∙ pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
    ≅⟨ congl (Properties.curry-exp hasProducts T hasTerminal isCCC) ⟩
    ⟦ Γ ,ₓ A ⊢ e ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩
    ≅⟨ sym (singleSubstitutionSemantics e x) ⟩
    ⟦ Γ ⊢ e [ x ] ⟧ₗ 
    ∎

{-
  Finalmente demostramos Soundness
-}

soundness : ∀ {τ} → {Γ : Context} → {t : Term Γ τ} → {u : Term Γ τ} →
            (t ≡ₜ u) → (⟦ Γ ⊢ t ⟧ₗ) ≅ (⟦ Γ ⊢ u ⟧ₗ)
soundness pr₁ = law1
soundness pr₂ = law2
soundness pr₃ = sym (law3 refl refl)
soundness (η f) = η-proof f
soundness (β e x) = β-proof e x