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
open import  Categories.Products.Properties hasProducts
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

-- Interpretación de weakenings como flechas CCC

⟦_⟧w  : ∀{Γ Γ'} → Γ' ▹ Γ → Hom ⟦ Γ' ⟧ₓ ⟦ Γ ⟧ₓ
⟦ iden▹ ⟧w = iden
⟦ wπ▹ m ⟧w = ⟦ m ⟧w ∙  π₁
⟦ w×▹ m ⟧w = pair ⟦ m ⟧w iden



weakenVarLemma : ∀{Γ Γ' A} → (x : Γ ∋ A) →  (w : Γ' ▹ Γ) 
               → find Γ' (weakenVar x w) ≅ find Γ x ∙ ⟦ w ⟧w
weakenVarLemma x iden▹ = sym idr
weakenVarLemma x (wπ▹ w) = trans (congl (weakenVarLemma x w)) ass
weakenVarLemma Z (w×▹ w) =  trans (sym idl) (sym π₂-pair)
weakenVarLemma (S x) (w×▹ w) = trans (trans (congl (weakenVarLemma x w)) ass) (trans (congr (sym π₁-pair)) (sym ass))

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

-- lema de weakening: hacer weakening y luego interpretar es lo mismo
-- que interpretar y componener con la interpretación del weakening
weakeningLemma : ∀{Γ Γ' τ} → (w : Γ' ▹ Γ) → (t : Term Γ τ) 
               → ⟦ Γ' ⊢ weaken▹ w t ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ w ⟧w 
weakeningLemma w (Var x) = weakenVarLemma x w
weakeningLemma {Γ} {Γ'} w (t₁ ⊕ t₂) = proof 
                  (apply ∙ ⟨ ⟦ Γ' ⊢ weaken▹ w t₁ ⟧ₗ , ⟦ Γ' ⊢ weaken▹ w t₂ ⟧ₗ ⟩)
               ≅⟨ congr (cong₂ ⟨_,_⟩ (weakeningLemma w t₁) (weakeningLemma w t₂)) ⟩
                 (apply ∙ ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ w ⟧w , ⟦ Γ ⊢ t₂ ⟧ₗ ∙ ⟦ w ⟧w ⟩)
               ≅⟨ congr (sym fusion) ⟩ 
                 (apply ∙ ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ w ⟧w) 
               ≅⟨ sym ass ⟩
                 ⟦ Γ ⊢ t₁ ⊕ t₂ ⟧ₗ ∙ ⟦ w ⟧w
                ∎ 
weakeningLemma {Γ} {Γ'} w (t₁ ×ₚ t₂) = proof 
                ⟨ ⟦ Γ' ⊢ weaken▹ w t₁ ⟧ₗ , ⟦ Γ' ⊢ weaken▹ w t₂ ⟧ₗ ⟩
              ≅⟨ cong₂ ⟨_,_⟩ (weakeningLemma w t₁) (weakeningLemma w t₂) ⟩
                 ⟨ ⟦ Γ ⊢ t₁ ⟧ₗ ∙ ⟦ w ⟧w , ⟦ Γ ⊢ t₂ ⟧ₗ ∙ ⟦ w ⟧w ⟩
               ≅⟨ sym fusion ⟩ 
                 (⟨ ⟦ Γ ⊢ t₁ ⟧ₗ , ⟦ Γ ⊢ t₂ ⟧ₗ ⟩ ∙ ⟦ w ⟧w)
                ∎ 
weakeningLemma w (p₁ t₁) = trans (congr (weakeningLemma w t₁)) (sym ass)
weakeningLemma w (p₂ t₁) = trans (congr (weakeningLemma w t₁)) (sym ass)
weakeningLemma {Γ} {Γ'} w (lam σ t₁) = proof 
                 curry ⟦ Γ' ,ₓ σ ⊢ weaken▹ (w×▹ w) t₁ ⟧ₗ
                ≅⟨ cong curry (weakeningLemma (w×▹ w) t₁) ⟩
                  curry (⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ pair ⟦ w ⟧w iden)
                ≅⟨ sym curry-prop₁ ⟩
                  (curry ⟦ Γ ,ₓ σ ⊢ t₁ ⟧ₗ ∙ ⟦ w ⟧w)  
                ∎

_⊢s_ : (Δ Γ : Context) → Set
_⊢s_ Δ Γ = (∀ {A} → Γ ∋ A → Term Δ A)

weakσ : ∀ {Δ Γ A} → (σ : Δ ⊢s (Γ ,ₓ A)) → Δ ⊢s Γ
weakσ σ x = σ (S x)

⟦_⟧s : {Δ Γ : Context} → (Δ ⊢s Γ) → Hom ⟦ Δ ⟧ₓ ⟦ Γ ⟧ₓ
⟦_⟧s {Δ} {∅} σ = t
⟦_⟧s {Δ} {Γ ,ₓ x} σ = ⟨ ⟦ weakσ σ ⟧s , ⟦ Δ ⊢ (σ Z) ⟧ₗ ⟩

{-
    A partir de acá demostramos que nuestra interpretación preserva las siguientes
    ecuaciones del lambda calculo formalizadas más arriba:

    1) fst(⟨a, b⟩)       = a
    2) snd(⟨a, b⟩)       = b
    3) ⟨fst(c) , snd(c)⟩ = c
    4) (λx . b) a        = b[a/x]
    5) (λx . c x)        = c (x no ocurre en c)

-}

substitutionSemantics : ∀ {Γ Δ : Context} {A : Ty} → (t : Term Γ A) → (σ : Δ ⊢s Γ) →
           ⟦ Δ ⊢ sub σ t ⟧ₗ ≅ ⟦ Γ ⊢ t ⟧ₗ ∙ ⟦ σ ⟧s
substitutionSemantics {Γ ,ₓ x₁} (Var Z) σ = sym law2
substitutionSemantics {Γ ,ₓ x₁} {Δ} (Var (S x)) σ = 
  proof 
    ⟦ Δ ⊢ sub σ (Var (S x)) ⟧ₗ 
    ≅⟨ refl ⟩ 
    ⟦ Δ ⊢ σ (S x) ⟧ₗ
    ≅⟨ {!   !} ⟩
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
substitutionSemantics {Γ} {Δ} (lam σ₁ t₁) σ = 
  proof 
    ⟦ Δ ⊢ sub σ (lam σ₁ t₁) ⟧ₗ
    ≅⟨ refl ⟩
    ⟦ Δ ⊢ lam σ₁ (sub (exts σ) t₁) ⟧ₗ
    ≅⟨ refl ⟩
    curry ⟦ Δ ,ₓ σ₁ ⊢ (sub (exts σ) t₁) ⟧ₗ
    ≅⟨ cong curry (substitutionSemantics t₁ ((exts σ))) ⟩
    curry (⟦ Γ ,ₓ σ₁ ⊢ t₁ ⟧ₗ ∙ ⟦ (exts σ) ⟧s)
    ≅⟨ {!   !} ⟩
    {!   !}
    ≅⟨ {!   !} ⟩
    {!   !} ∎

singleSubstitutionSemantics : ∀ {Γ : Context} {A A' : Ty} → {t : Term (Γ ,ₓ A) A'} → {t' : Term Γ A} →
               ⟦ Γ ⊢ t [ t' ] ⟧ₗ ≅ ⟦ (Γ ,ₓ A) ⊢ t ⟧ₗ ∙ ⟨ iden {⟦ Γ ⟧ₓ} , ⟦ Γ ⊢ t' ⟧ₗ ⟩
singleSubstitutionSemantics = {!   !}

--open import Categories.Products.Properties hasProducts 
  --     using (comp-pair ; iden-pair ; iden-comp-pair ; fusion-pair ; fusion)

-- open import Properties
{-
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
-}

η-lema₁ : ∀ {Γ : Context} {A B : Ty} → (u : Term Γ B) →
            ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ ≅ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁
η-lema₁ u = trans (weakeningLemma (wπ▹ iden▹) u) (congr idl)

η-lema₂ : ∀ {Γ : Context} {A B : Ty} → (u : Term Γ (A ⇛ B)) →
        curry (apply ∙ (pair ⟦ Γ ⊢ u ⟧ₗ (iden {⟦ A ⟧ₜ}))) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-lema₂ {Γ = Γ} u = proof 
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ cong curry (Properties.uncurry-exp hasProducts T hasTerminal isCCC) ⟩ 
    curry (uncurry ⟦ Γ ⊢ u ⟧ₗ) 
    ≅⟨ lawcurry2 ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎

η-proof : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} → 
        curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) ≅ ⟦ Γ ⊢ u ⟧ₗ
η-proof {Γ} {A} {B} {u} = proof 
    curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (apply ∙ ⟨ x , π₂ ⟩)) (η-lema₁ u) ⟩ 
    curry (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (uncurry iden ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , x ⟩)) (sym idl) ⟩
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ η-lema₂ u ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ 
    ∎
{-
-- Finalmente demostramos Soundness

soundness : ∀ {τ} → {Γ : Context} → {t : Term Γ τ} → {u : Term Γ τ} →
            (t ≡ₜ u) → (⟦ Γ ⊢ t ⟧ₗ) ≅ (⟦ Γ ⊢ u ⟧ₗ)
soundness pr₁ = law1
soundness pr₂ = law2
soundness pr₃ = sym (law3 refl refl)
soundness β = β-proof
soundness η = η-proof

-}   