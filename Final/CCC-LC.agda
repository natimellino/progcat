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
         using (comp-pair ; iden-pair ; iden-comp-pair)
  
 
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

  {-----------------------------------------------------------------------------
  
    LAMBDA CALCULO

  -----------------------------------------------------------------------------}


  open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_; _≡ᵇ_; pred; _<_; z≤n; s≤s)
  open import Data.Vec using (Vec; []; _∷_; lookup)
  open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)

  infixr 30 _⇛_
  infixr 30 _⊗_

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

  data Context : Set where
    ∅   : Context
    _,ₓ_ : Context → Ty → Context

  data _∋_ : Context → Ty → Set where

    Z : ∀ {Γ A}
        ---------
      → Γ ,ₓ A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ ,ₓ B ∋ A

  -- Lambda términos

  data Term (Γ : Context) : Ty → Set where
    -- Var : ∀ {τ} (v : Fin n) → τ ≡ lookup Γ v → Term Γ τ -- lol
    Var : ∀ {τ} → Γ ∋ τ → Term Γ τ
    _⊕_ : ∀ {σ τ} → Term Γ (σ ⇛ τ) → Term Γ σ → Term Γ τ -- app
    _×ₚ_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ ⊗ τ) -- pair
    p₁ :  ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ σ -- fst
    p₂ : ∀ {σ τ} → Term Γ (σ ⊗ τ) → Term Γ τ  -- snd
    lam : ∀ σ {τ} → Term (Γ ,ₓ σ) τ → Term Γ (σ ⇛ τ) -- abstraccion


  open import Data.Bool using (if_then_else_ ; Bool)
  open import Relation.Nullary using (Dec)

  -- TODO: No sé como tiparlo

  -- Substitución de términos

  -- update : ∀ {n m : ℕ} {Γ : Ctx n} {τ : Ty} → (t : Term Γ τ) → (k : ℕ) 
  --          → (i : ℕ) → {Γ' : Ctx (n + i)} → Term Γ' τ
  -- update (Var v x) k i with k ≤? i
  -- ... | Dec.yes _ = {!   !}
  -- ... | Dec.no _ = Var {! (fromℕ (pred ((toℕ v) + i)))  !} {!   !}
  -- update (t ⊕ t₁) k i = (update t k i) ⊕ (update t₁ k i)
  -- update (t ×ₚ t₁) k i = (update t k i) ×ₚ (update t₁ k i)
  -- update (p₁ t) k i = p₁ (update t k i)
  -- update (p₂ t) k i = p₂ (update t k i)
  -- update (lam σ t) k i = lam σ (update t (suc k) i)

  length : Context → ℕ
  length ∅        =  zero
  length (Γ ,ₓ _)  =  suc (length Γ)

  lookup' : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Ty
  lookup' {(_ ,ₓ A)} {zero}    (s≤s z≤n)  =  A
  lookup' {(Γ ,ₓ _)} {(suc n)} (s≤s p)    =  lookup' p

  count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ (lookup' p)
  count {_ ,ₓ _} {zero}    (s≤s z≤n)  =  Z
  count {Γ ,ₓ _} {(suc n)} (s≤s p)    =  S (count p)

  #_ : ∀ {Γ}
       → (n : ℕ)
       → {n∈Γ : True (suc n ≤? length Γ)}
         --------------------------------
       → Term Γ (lookup' (toWitness n∈Γ))
  #_ n {n∈Γ}  = Var (count (toWitness n∈Γ))

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

  -- sub : ∀ {n k : ℕ} {τ₁ τ₂} → {Γ : Ctx n} → {Γ₁ : Ctx k} → (m : Fin n) → -- {p : τ₂ ≡ lookup Γ m} →
  --       (t : Term Γ τ₁) → (u : Term Γ τ₂) → (Term Γ₁ τ₁)
  -- -- sub m (Var m x) u = {!   !} -- if (toℕ m) ≡ᵇ (toℕ v) then t else (Var m x)
  -- sub m (Var v x) u = {!   !}
  -- sub m (t ⊕ t₁) u = (sub m t u) ⊕ (sub m t₁ u)
  -- sub m (t ×ₚ t₁) u = (sub m t u) ×ₚ (sub m t₁ u)
  -- sub m (p₁ t) u = p₁ (sub m t u)
  -- sub m (p₂ t) u = p₂ (sub m t u)
  -- sub m (lam σ t) u = {!   !} -- {! lam σ (sub (suc m) t u)  !} 

  infixr 7 _≡ₜ_

  -- Ecuaciones para lambda términos

  -- mapp : ∀ {Γ Δ A B} → (M : Term Γ A) →  Γ ,ₓ B ∋ A → Term Δ A
  -- mapp M Z      =  M
  -- mapp M (S x)  =  Var x

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

  data _≡ₜ_ : ∀ {Γ : Context} {T : Ty} → Term Γ T → Term Γ T → Set where
    pr₁ : ∀ {Γ : Context} {A B : Ty} → {t₁ : Term Γ A} → {t₂ : Term Γ B} →
          p₁ (t₁ ×ₚ t₂) ≡ₜ t₁

    pr₂ : ∀ {Γ : Context} {A B : Ty} → {t₁ : Term Γ A} → {t₂ : Term Γ B} →
          p₂ (t₁ ×ₚ t₂) ≡ₜ t₂

    pr₃ : ∀ {Γ : Context} {A B : Ty} → {t : Term Γ (A ⊗ B)} →
          (p₁ t) ×ₚ (p₂ t) ≡ₜ t

    -- η : ∀ {Γ : Context} {A B : Ty} → {f : Term Γ (A ⇛ B)} → {x : Term Γ A} →
    --     (lam A (f ⊕ x)) ≡ₜ f

    β : ∀ {Γ : Context} {A B : Ty} → {e : Term (Γ ,ₓ A) B} → {x : Term Γ A} →
        ((lam A e) ⊕ x) ≡ₜ (e [ x ])

  -- -- extt : ∀ {n m : ℕ} → (σ : Fin n → Fin m) → (v : Fin n) → Fin m
  -- -- extt σ Data.Fin.0F = {!   !}
  -- -- extt σ (suc x) = {!  suc (σ x) !}


  -- {-----------------------------------------------------------------------------
  
  --   CATEGORICAL SEMANTICS
  
  -- -----------------------------------------------------------------------------}


  -- -- Interpretación para tipos como objetos CCC

  -- ⟦_⟧ₜ : Ty → Obj
  -- ⟦ base ⟧ₜ = T
  -- ⟦ (t ⊗ u) ⟧ₜ = ⟦ t ⟧ₜ × ⟦ u ⟧ₜ
  -- ⟦ (t ⇛ u) ⟧ₜ = ⟦ t ⟧ₜ ⇒ ⟦ u ⟧ₜ

  -- -- Interpretación para contextos como objetos CCC

  -- ⟦_⟧ₓ : {n : ℕ} → (Γ : Ctx n) → Obj
  -- ⟦ [] ⟧ₓ = T
  -- ⟦ (t ∷ Γ) ⟧ₓ = ⟦ Γ ⟧ₓ × ⟦ t ⟧ₜ

  -- find : ∀ {n : ℕ} {τ} (m : Fin n) → (Γ : Ctx n) → τ ≡ lookup Γ m → Hom ⟦ Γ ⟧ₓ ⟦ τ ⟧ₜ
  -- find Data.Fin.0F (x ∷ Γ) refl = π₂
  -- find (suc m) (x ∷ Γ) refl = (find m Γ refl) ∙ π₁

  -- -- Interpretacion para términos como flechas CCC

  -- ⟦_⊢_⟧ₗ : ∀ {n : ℕ} {τ} → (Γ : Ctx n) → Term Γ τ → Hom ⟦ Γ ⟧ₓ ⟦ τ ⟧ₜ
  -- ⟦ Γ ⊢ Var v x ⟧ₗ = find v Γ x
  -- ⟦ Γ ⊢ (t ⊕ u) ⟧ₗ = apply ∙ ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩
  -- ⟦ Γ ⊢ (t ×ₚ u) ⟧ₗ = ⟨ ⟦ Γ ⊢ t ⟧ₗ , ⟦ Γ ⊢ u ⟧ₗ ⟩
  -- ⟦ Γ ⊢ (p₁ t) ⟧ₗ = π₁ ∙ ⟦ Γ ⊢ t ⟧ₗ 
  -- ⟦ Γ ⊢ (p₂ t) ⟧ₗ = π₂ ∙ ⟦ Γ ⊢ t ⟧ₗ
  -- ⟦ Γ ⊢ (lam σ t) ⟧ₗ = curry ⟦ (σ ∷ Γ) ⊢ t ⟧ₗ

  -- {--
  --   A partir de acá demostramos que nuestra interpretación preserva las siguientes
  --   ecuaciones del lambda calculo:

  --   1) fst(⟨a, b⟩)       = a
  --   2) snd(⟨a, b⟩)       = b
  --   3) ⟨fst(c) , snd(c)⟩ = c
  --   4) (λx . b) a        = b[a/x]
  --   5) (λx . c x)        = c (x no ocurre en c)

  -- -}

  -- -- Soundness

  -- proof : ∀ {n : ℕ} {τ} → {Γ : Ctx n} → {t : Term Γ τ} → {u : Term Γ τ} →
  --         (t ≡ₜ u) → (⟦ Γ ⊢ t ⟧ₗ) ≅ (⟦ Γ ⊢ u ⟧ₗ)
  -- proof pr₁ = law1
  -- proof pr₂ = law2
  -- proof pr₃ = sym (law3 refl refl)

  -- (4)

  -- TODO: no me sale :(

  -- (5)
  -- proof_eta : ∀ {n : ℕ} {τ σ} → {Γ : Ctx n} → {t : Term (σ ∷ Γ) (σ ⇛ τ)} → {x : Term (σ ∷ Γ) σ} → 
  --             ⟦ Γ ⊢ (lam σ (t ⊕ x)) ⟧ₗ ≅ ⟦ (σ ∷ Γ) ⊢ t ⟧ₗ
  -- proof_eta {σ = σ} {Γ = Γ} {t = t} {x = x} = 
  --   proof 
  --     curry ((uncurry iden) ∙ ⟨ ⟦ σ ∷ Γ ⊢ t ⟧ₗ , ⟦ σ ∷ Γ ⊢ x ⟧ₗ ⟩) 
  --   ≅⟨ sym curry-prop ⟩ 
  --     map⇒ (uncurry iden) ∙ curry ⟨ ⟦ σ ∷ Γ ⊢ t ⟧ₗ , ⟦ σ ∷ Γ ⊢ x ⟧ₗ ⟩ 
  --   ≅⟨ {!   !} ⟩ 
  --     {!   !} 
  --   ≅⟨ {!   !} ⟩ 
  --     {!   !} ∎

  {--
  ≅⟨_⟩_
  curry (uncurry iden ∙ ⟨ ⟦ σ ∷ Γ ⊢ t ⟧ₗ , ⟦ σ ∷ Γ ⊢ x ⟧ₗ ⟩) ≅ ⟦ σ ∷ Γ ⊢ t ⟧ₗ
  -}
