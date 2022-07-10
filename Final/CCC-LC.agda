open import Categories
open import Categories.Products
open import Categories.Terminal

module Final.CCC-LC {a}{b}{C : Cat {a}{b}}
                                    (hasProducts : Products C)
                                    (T : Cat.Obj C)
                                    (hasTerminal : Terminal C T)
                                    where

open import Library hiding (_×_ ; curry ; uncurry)

open Cat C
open Products hasProducts

{-------------------------------------------------------------------------------

  CCC

-------------------------------------------------------------------------------}

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

  -- module Properties (isCCC : CCC) where
  -- open CCC isCCC
  open import Categories.Products.Properties hasProducts 
         using (comp-pair ; iden-pair ; iden-comp-pair; fusion-pair)
  
 
  {- Ejercicio: map⇒ preserva identidades. -}
  map⇒iden : ∀{X Y} → map⇒ {X} {Y} {X} (iden {X}) ≅ iden {Y ⇒ X}
  map⇒iden = proof
             map⇒ iden
             ≅⟨ refl ⟩
             curry (iden ∙ apply)
             ≅⟨ cong curry idl ⟩
             curry apply
             ≅⟨ cong curry refl ⟩
             curry (uncurry iden)
             ≅⟨ lawcurry2 ⟩
             iden
             ∎

  {- Ejercicio: Propiedad de curry con map⇒. Caso particular de nat-curry, con f = iden. -}
  curry-prop : ∀{X Y Z Z'}{f : Hom (X × Y) Z}{g : Hom Z Z'}
              →  map⇒ g ∙ curry f ≅ curry (g ∙ f)
  curry-prop {f = f} {g} = proof
                           map⇒ g ∙ curry f
                           ≅⟨ refl ⟩
                           curry (g ∙ apply) ∙ curry f
                           ≅⟨ refl ⟩
                           curry (g ∙ uncurry iden) ∙ curry f
                           ≅⟨ sym idr ⟩
                           (curry (g ∙ uncurry iden) ∙ curry f) ∙ iden
                           ≅⟨ ass ⟩
                           curry (g ∙ uncurry iden) ∙ curry f ∙ iden
                           ≅⟨ nat-curry ⟩
                           curry (g ∙ f ∙ pair iden iden)
                           ≅⟨ cong curry (congr (congr iden-pair)) ⟩
                           curry (g ∙ f ∙ iden)
                           ≅⟨ cong curry (congr idr) ⟩
                           curry (g ∙ f)
                           ∎

  {- Una definición alternativa de exponencial se puede dar en base al morfismo apply:
    Un exponencial entre A y B es un objeto B ⇒ A, y un morfismo apply : (B ⇒ A) × B → A tal que
    para cada f : C × B → A existe un único morfismo curry f : C → (B ⇒ A) tal que 
        apply ∙ pair (curry f) iden ≅ f  
    Ejercicio: probar que nuestra definición implica la de más arriba. 
    
    Cortesía de Santi
  -}
  curry-exp : ∀{X Y Z} {f : Hom (X × Y) Z} →  apply ∙ pair (curry f) iden ≅ f
  curry-exp {X} {Y} {Z} {f = f} = proof
                      apply ∙ pair (curry f) iden
                      ≅⟨ refl ⟩
                      uncurry iden ∙ pair (curry f) iden -- Tiene pinta de nat-curry falta multiplicar algo
                      ≅⟨ sym idl ⟩
                      iden ∙ uncurry iden ∙ pair (curry f) iden
                      ≅⟨ sym lawcurry1 ⟩ -- Agrego el curry para poder usar nat-curry
                      uncurry (curry (iden ∙ uncurry iden ∙ pair (curry f) iden))
                      ≅⟨ cong uncurry (sym nat-curry) ⟩ -- Paso mágico
                      uncurry (curry (iden ∙ uncurry iden) ∙ curry (uncurry iden) ∙ curry f)
                      ≅⟨ cong uncurry (congl (cong curry idl)) ⟩ -- Comienza la limpieza de iden's
                      uncurry (curry (uncurry iden) ∙ curry (uncurry iden) ∙ curry f)
                      ≅⟨ cong uncurry (congl lawcurry2) ⟩
                      uncurry (iden ∙ curry (uncurry iden) ∙ curry f)
                      ≅⟨ cong uncurry idl ⟩
                      uncurry (curry (uncurry iden) ∙ curry f)
                      ≅⟨ cong uncurry (congl lawcurry2) ⟩
                      uncurry (iden ∙ curry f)
                      ≅⟨ cong uncurry idl ⟩
                      uncurry (curry f)
                      ≅⟨ lawcurry1 ⟩
                      f
                      ∎
   
  -- TODO: this

  -- open import Categories.Products.Properties using (fusion-pair)

  aux : ∀{X Y Z} {f : Hom (Y × X) Z} {g : Hom Y X} →
        ⟨ curry f ∙ iden , iden ∙ g ⟩ ≅ ⟨ curry f , g ⟩
  aux = cong₂ (λ x y → ⟨ x , y ⟩) idr idl

  curry-prop₂ : ∀{X Y Z} {f : Hom (Y × X) Z} {g : Hom Y X} →
                ⟨ curry f , g ⟩ ≅ pair (curry f) (iden {X}) ∙ ⟨ iden {Y} , g ⟩
  curry-prop₂ {X = X} {Y = Y} {Z = Z} {f = f} {g = g} = proof 
    ⟨ curry f , g ⟩ 
    ≅⟨ sym aux ⟩ 
    ⟨ curry f ∙ iden , iden ∙ g ⟩ 
    ≅⟨ sym fusion-pair ⟩ 
    pair (curry f) iden ∙ ⟨ iden , g ⟩ ∎

  uncurry-exp : ∀ {A B C} → {f : Hom A (B ⇒ C)} →
         apply ∙ (pair f (iden {B})) ≅ uncurry f
  uncurry-exp {f = f} = proof 
    apply ∙ pair f iden 
    ≅⟨ cong (λ x → apply ∙ (pair x iden)) (sym lawcurry2) ⟩ 
    apply ∙ pair (curry (uncurry f)) iden 
    ≅⟨ curry-exp ⟩ 
    uncurry f ∎

  {-----------------------------------------------------------------------------
  
    LAMBDA CALCULO

  -----------------------------------------------------------------------------}


  open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_; _≡ᵇ_; pred; _<_; z≤n; s≤s)
  open import Data.Vec using (Vec; []; _∷_; lookup)
  open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)

  infixr 7 _⇛_
  infixl 7 _⊗_

  -- Tipos

  data Ty : Set where
      base : Ty
      _⊗_ : Ty → Ty → Ty
      _⇛_ : Ty → Ty → Ty

  -- Contextos de tipado

  Ctx : ℕ → Set
  Ctx = Vec Ty

  infix  4 _∋_
  infixl 5 _,ₓ_

  -- Representación para contextos

  data Context : Set where
    ∅   : Context
    _,ₓ_ : Context → Ty → Context

  -- Representación para variables con índices de Bruijn (representa el lookup)

  data _∋_ : Context → Ty → Set where

    Z : ∀ {Γ A}
        ---------
      → Γ ,ₓ A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ ,ₓ B ∋ A

  -- Representación para lambda términos

  data Term (Γ : Context) : Ty → Set where
    Var : ∀ {τ} → Γ ∋ τ → Term Γ τ
    _⊕_ : ∀ {σ τ} → Term Γ (σ ⇛ τ) → Term Γ σ → Term Γ τ -- app
    _×ₚ_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ ⊗ τ) -- pair
    p₁ :  ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ σ -- fst
    p₂ : ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ τ  -- snd
    lam : ∀ σ {τ} → Term (Γ ,ₓ σ) τ → Term Γ (σ ⇛ τ) -- abstraccion


  open import Data.Bool using (if_then_else_ ; Bool)
  open import Relation.Nullary using (Dec)

  {-
    Auxiliares (ver de sacar si no se usa)
  -}

  length : Context → ℕ
  length ∅        =  zero
  length (Γ ,ₓ _)  =  suc (length Γ)

  lookup' : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Ty
  lookup' {(_ ,ₓ A)} {zero}    (s≤s z≤n)  =  A
  lookup' {(Γ ,ₓ _)} {(suc n)} (s≤s p)    =  lookup' p

  count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ (lookup' p)
  count {_ ,ₓ _} {zero}    (s≤s z≤n)  =  Z
  count {Γ ,ₓ _} {(suc n)} (s≤s p)    =  S (count p)

  -- Ver si sirve, creo que se puede sacar

  #_ : ∀ {Γ}
       → (n : ℕ)
       → {n∈Γ : True (suc n ≤? length Γ)}
         --------------------------------
       → Term Γ (lookup' (toWitness n∈Γ))
  #_ n {n∈Γ}  = Var (count (toWitness n∈Γ))

  {-
    Funciones auxiliares para ayudar a definir la substitución
  -}

  extt : ∀ {Γ} {Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ---------------------------------
      → (∀ {A B} → Γ ,ₓ B ∋ A → Δ ,ₓ B ∋ A)
  extt ρ Z      =  Z
  extt ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
           → (∀ {A} → Γ ∋ A → Δ ∋ A)
             -----------------------
           → (∀ {A} → Term Γ A → Term Δ A)
  rename ρ (Var x) = Var (ρ x)
  rename ρ (t ⊕ t₁) = rename ρ t ⊕ rename ρ t₁
  rename ρ (t ×ₚ t₁) = rename ρ t ×ₚ rename ρ t₁
  rename ρ (p₁ t) = p₁ (rename ρ t)
  rename ρ (p₂ t) = p₂ (rename ρ t)
  rename ρ (lam σ t) = lam σ (rename (extt ρ) t)

  exts : ∀ {Γ Δ}
         → (∀ {A} →       Γ ∋ A →     Term Δ A)
           ---------------------------------
         → (∀ {A B} → Γ ,ₓ B ∋ A → Term (Δ ,ₓ B) A)
  exts σ Z      =  Var Z
  exts σ (S x)  =  rename S_ (σ x)

  -- Substitución simultánea dada una función de mapeo (multiple substitution)

  sub : ∀ {Γ Δ}
        → (∀ {A} → Γ ∋ A → Term Δ A)
          -------------------------
        → (∀ {A} → Term Γ A → Term Δ A)
  sub σ (Var x) = σ x
  sub σ (t ⊕ t₁) = sub σ t ⊕ sub σ t₁
  sub σ (t ×ₚ t₁) = sub σ t ×ₚ sub σ t₁
  sub σ (p₁ t) = p₁ (sub σ t)
  sub σ (p₂ t) = p₂ (sub σ t)
  sub σ (lam σ₁ t) = lam σ₁ (sub (exts σ) t)

  -- Substitución de términos (single)

  _[_] : ∀ {Γ A B}
         → Term (Γ ,ₓ B) A
         → Term Γ B
           ---------
         → Term Γ A
  _[_] {Γ} {A} {B} N M = sub {(Γ ,ₓ B)} {Γ} σ {A} N
    where
    σ : ∀ {A} → Γ ,ₓ B ∋ A → Term Γ A
    σ Z      =  M
    σ (S x)  = Var x

  weaken : ∀ {Γ A B} → Term Γ A 
           → Term (Γ ,ₓ B) A
  weaken {Γ} ⊢M = rename ρ ⊢M
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

    -- Beta y Eta

    η : ∀ {Γ : Context} {A B : Ty} → {f : Term Γ (A ⇛ B)} →
        (lam A ((weaken f) ⊕ (Var Z))) ≡ₜ f

    β : ∀ {Γ : Context} {A B : Ty} → {e : Term (Γ ,ₓ A) B} → {x : Term Γ A} →
        ((lam A e) ⊕ x) ≡ₜ (e [ x ])


  {-----------------------------------------------------------------------------
  
    CATEGORICAL SEMANTICS
  
  -----------------------------------------------------------------------------}


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

  {--
    A partir de acá demostramos que nuestra interpretación preserva las siguientes
    ecuaciones del lambda calculo formalizadas más arriba:

    1) fst(⟨a, b⟩)       = a
    2) snd(⟨a, b⟩)       = b
    3) ⟨fst(c) , snd(c)⟩ = c
    4) (λx . b) a        = b[a/x]
    5) (λx . c x)        = c (x no ocurre en c)

  -}

  -- TODO: this :(

  fusion-aux : ∀{A B C D}{f : Hom C A}{g : Hom C B}{h : Hom D C}
               → ⟨ f , g ⟩ ∙ h ≅  ⟨ f ∙  h , g ∙ h ⟩
  fusion-aux {f = f}{g}{h} = law3 (trans (sym ass) (congl law1)) (trans (sym ass) (congl law2))

  subs-proof : ∀ {Γ : Context} {A A' : Ty} → {t : Term (Γ ,ₓ A) A'} → {t' : Term Γ A} →
               ⟦ Γ ⊢ t [ t' ] ⟧ₗ ≅ ⟦ (Γ ,ₓ A) ⊢ t ⟧ₗ ∙ ⟨ iden {⟦ Γ ⟧ₓ} , ⟦ Γ ⊢ t' ⟧ₗ ⟩
  subs-proof {Γ} {A} {A'} {Var Z} {t'} = 
    proof 
      ⟦ Γ ⊢ Var Z [ t' ] ⟧ₗ 
      ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) refl ⟩ 
      ⟦ Γ ⊢ t' ⟧ₗ
      ≅⟨ sym law2 ⟩
      π₂ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
      ≅⟨ cong (λ x → x ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩) (refl) ⟩
      (find (Γ ,ₓ A) Z) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
      ≅⟨ cong (λ x → x ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩) (refl) ⟩
      ⟦ (Γ ,ₓ A) ⊢ Var Z ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
      ∎
  subs-proof {Γ} {A} {A'} {Var (S x)} {t'} = {!   !}
  subs-proof {Γ} {A} {A'} {t ⊕ t₁} {t'} = 
    proof 
      ⟦ Γ ⊢ (t ⊕ t₁) [ t' ] ⟧ₗ 
      ≅⟨ cong (λ x → ⟦ Γ ⊢ x ⟧ₗ) refl ⟩ 
      ⟦ Γ ⊢ (t [ t' ]) ⊕ (t₁ [ t' ]) ⟧ₗ
      ≅⟨ refl ⟩
      apply ∙ ⟨ ⟦ Γ ⊢ (t [ t' ]) ⟧ₗ , ⟦ Γ ⊢ (t₁ [ t' ]) ⟧ₗ ⟩ -- apply ∙ ⟨ ⟦ Γ ⊢ (t [ t' ]) ⟧ₗ , ⟦ (t₁ [ t' ]) ⟧ₗ ⟩
      ≅⟨ Library.cong₂ (λ x y → apply ∙ ⟨ x , y ⟩) (subs-proof {t = t}) (subs-proof {t = t₁}) ⟩ -- subs-proof {Γ} {A} {A'} {weaken t} {t'}
      apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩ ⟩
      ≅⟨ cong (λ x → apply ∙ x) (sym fusion-aux) ⟩
      apply ∙ (⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ⟩ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩)
      ≅⟨ sym ass ⟩
      (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ t ⟧ₗ , ⟦ Γ ,ₓ A ⊢ t₁ ⟧ₗ ⟩) ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
      ≅⟨ cong (λ x → x ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩) (refl) ⟩
      ⟦ (Γ ,ₓ A) ⊢ t ⊕ t₁ ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ t' ⟧ₗ ⟩
      ∎
  subs-proof {Γ} {A} {.(_ ⊗ _)} {t ×ₚ t₁} {t'} = {!   !}
  subs-proof {Γ} {A} {A'} {p₁ t} {t'} = {!   !}
  subs-proof {Γ} {A} {A'} {p₂ t} {t'} = {!   !}
  subs-proof {Γ} {A} {.(σ ⇛ _)} {lam σ t} {t'} = {!   !} 

  β-proof : ∀ {Γ : Context} {A B : Ty} → {e : Term (Γ ,ₓ A) B} → {x : Term Γ A} →
            ⟦ Γ ⊢ lam A e ⊕ x ⟧ₗ ≅ ⟦ Γ ⊢ e [ x ] ⟧ₗ
  β-proof {Γ} {A} {B} {e} {x} = proof 
    apply ∙ ⟨ curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
    ≅⟨ cong (λ a → apply ∙ a) curry-prop₂ ⟩ 
    apply ∙ ((pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩) 
    ≅⟨ sym ass ⟩ 
    (apply ∙ pair (curry ⟦ Γ ,ₓ A ⊢ e ⟧ₗ) iden) ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩ 
    ≅⟨ congl curry-exp ⟩
    ⟦ Γ ,ₓ A ⊢ e ⟧ₗ ∙ ⟨ iden , ⟦ Γ ⊢ x ⟧ₗ ⟩
    ≅⟨ sym subs-proof ⟩ -- usar la demostracion de la igualdad de la substitucion
    ⟦ Γ ⊢ e [ x ] ⟧ₗ 
    ∎

  -- TODO: 

  η-lema₁ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} →
            ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ ≅ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁
  η-lema₁ = {!   !}

  -- FIXME: ver despues de moverlo a la prueba principal

  η-lema₂ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} →
            curry (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , π₂ ⟩) ≅ curry (apply ∙ (pair ⟦ Γ ⊢ u ⟧ₗ (iden {⟦ A ⟧ₜ})))
  η-lema₂ {Γ = Γ} {u = u}  = cong (λ x → curry (uncurry iden ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , x ⟩)) (sym idl)

  η-lema₃ : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} →
            curry (apply ∙ (pair ⟦ Γ ⊢ u ⟧ₗ (iden {⟦ A ⟧ₜ}))) ≅ ⟦ Γ ⊢ u ⟧ₗ
  η-lema₃ {Γ = Γ} {u = u} = proof 
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ cong (λ x → curry x) uncurry-exp ⟩ 
    curry (uncurry ⟦ Γ ⊢ u ⟧ₗ) 
    ≅⟨ lawcurry2 ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ ∎

  η-proof : ∀ {Γ : Context} {A B : Ty} → {u : Term Γ (A ⇛ B)} → 
            curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) ≅ ⟦ Γ ⊢ u ⟧ₗ
  η-proof {Γ} {A} {B} {u} = proof 
    curry (apply ∙ ⟨ ⟦ Γ ,ₓ A ⊢ weaken u ⟧ₗ , π₂ ⟩) 
    ≅⟨ cong (λ x → curry (apply ∙ ⟨ x , π₂ ⟩)) η-lema₁ ⟩ 
    curry (apply ∙ ⟨ ⟦ Γ ⊢ u ⟧ₗ ∙ π₁ , π₂ ⟩) 
    ≅⟨ η-lema₂ ⟩
    curry (apply ∙ pair ⟦ Γ ⊢ u ⟧ₗ iden) 
    ≅⟨ η-lema₃ ⟩ 
    ⟦ Γ ⊢ u ⟧ₗ ∎

  -- Soundness

  soundness : ∀ {τ} → {Γ : Context} → {t : Term Γ τ} → {u : Term Γ τ} →
             (t ≡ₜ u) → (⟦ Γ ⊢ t ⟧ₗ) ≅ (⟦ Γ ⊢ u ⟧ₗ)
  soundness pr₁ = law1
  soundness pr₂ = law2
  soundness pr₃ = sym (law3 refl refl)
  soundness β = β-proof
  soundness η = η-proof
  