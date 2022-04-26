-- {-# OPTIONS --cumulativity #-}

open import Library

module clase06.ConstruccionesSet where
 
 open import Categories.Sets
 open import clase06.Construcciones (Sets {lzero})

 {- Ejercicios
   -- Probar que Sets tiene objeto terminal, productos, inicial, y coproductos
  -}

 SetsHasProducts : Products
 SetsHasProducts = 
  prod 
    (λ x y → x × y) 
    fst 
    snd 
    (λ f g x → (f x) , (g x)) 
    refl 
    refl 
    λ {refl refl → refl}

 OneSet : Terminal ⊤
 OneSet = term (λ x → tt) refl

 -------------------------------------------------
 data _⊎_{a b : Level}(A : Set a)(B : Set b) : Set (a ⊔ b) where
     Inl : A → A ⊎ B
     Inr : B → A ⊎ B

 FunCoprod : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
 FunCoprod f g (Inl x) = f x
 FunCoprod f g (Inr x) = g x

 SetsHasCoproducts : Coproducts
 SetsHasCoproducts = 
  coproduct 
    _⊎_ 
    Inl 
    Inr 
    FunCoprod 
    refl 
    refl 
    ProofCoprod
      where ProofCoprod : {A B C : Set} {f : A → C} {g : B → C} {h : A ⊎ B → C} → (λ x → h (Inl x)) ≅ f → (λ x → h (Inr x)) ≅ g → h ≅ FunCoprod f g
            ProofCoprod refl refl = ext (λ { (Inl x) → refl
                                           ; (Inr x) → refl  } )

--------------------------------------------------
 ZeroSet : Initial ⊥
 ZeroSet = init (λ ()) (ext λ ())
--------------------------------------------------
 