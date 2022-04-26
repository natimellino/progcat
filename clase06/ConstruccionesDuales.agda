
module clase06.ConstruccionesDuales where

open import Library
open import Categories

private 
  variable
   a b : Level
   C : Cat {a} {b}

open import clase06.Construcciones
open import Categories.Iso

open Cat
open Initial
open Iso
-------------------------------------------------
{- Probar que un objeto terminal es inicial en la categoría dual y viceversa -}

TerminalInitialDuality : {X : Obj C} → Terminal C X → Initial (C Op) X
TerminalInitialDuality (term t law₁) = init t law₁


InitialTerminalDuality : {X : Obj C} → Initial C X → Terminal (C Op) X
InitialTerminalDuality (init i₁ law₁) = term i₁ law₁

--------------------------------------------------
 


 {- Probar que dos objetos iniciales son necesariamente isomorfos *usando dualidad* -}
InitialIso : (I I' : Obj C)
            → (p : Initial C I)
            → (q : Initial C I')
            → Iso C (i p {I'})
InitialIso {C = C} I I' p q with {! TerminalIso (C Op) I I' (TerminalInitialDuality p) (TerminalInitialDuality q)  !} 
...| x = {!   !}


--------------------------------------------------------
-- Probar que los coproductos son productos en la categoría dual
ProductCoproductDuality : Products C
                        → Coproducts (C Op)
ProductCoproductDuality (prod _×_ π₁ π₂ ⟨_,_⟩ law1 law2 law3) = 
  coproduct 
    _×_ 
    π₁ 
    π₂ 
    ⟨_,_⟩ 
    law1 
    law2 
    law3

CoproductProductDuality : Coproducts C
                        → Products (C Op)
CoproductProductDuality (coproduct _+_ inl inr [_,_] law1 law2 law3) = 
  prod 
    _+_ 
    inl 
    inr 
    [_,_] 
    law1 
    law2 
    law3


--------------------------------------------------
open Coproducts

 {- Probar que los coproductos son únicos hasta un isomorfismo usando dualidad -}
CoproductIso : ∀{A B}(X Y : Coproducts C) → Iso C ([_,_] X {A} {B} (inl Y) (inr Y))
CoproductIso X Y = {!   !}


--------------------------------------------------
