open import Categories
open import Categories.Products
open import Categories.Terminal
open import Final.SimpleTyped
open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)

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

-- π : ∀{X Y Z} → (Γ : Ctx n) → ℕ → () 

eval : {n : ℕ} → (Γ : Ctx n) → LamTerm → CCC
eval Γ (Var x) = {! x  !}
eval Γ (t ⊕ t₁) = {!   !}
eval Γ (Abs x t) = {!   !}