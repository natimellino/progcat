
module Records where

open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Ext

-- postulamos extensionalidad
postulate ext : ∀{a b} → Ext.Extensionality a b

{- Veremos, el uso de records para definir estructuras algebraicas -}


-- MONOIDES

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1
 -}

record Monoid : Set₁  where
  infixr 7 _∙_
  -- constructor monoid
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier   {- ε = \epsilon -}
         lid     : {x : Carrier} → ε ∙ x ≡ x
         rid     : {x : Carrier} → x ∙ ε ≡ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}

{- Al escribir las ecuaciones estamos tomando una decisión sobre la noción de igualdad 
 En esta definición elegimos la igualdad proposicional
-}

open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ ; +-assoc ; *-distribʳ-+)

-- Monoide de Naturales y suma

module NatMonoid where


  NatMonoid : Monoid
  NatMonoid = record
    { Carrier = ℕ 
    ; _∙_ = _+_ 
    ; ε = 0 
    ; lid = refl 
    ; rid = λ {x} → +-identityʳ x ; 
    assoc = λ {x} {y} {z} → +-assoc x y z }

open NatMonoid


--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≡-Reasoning

open import Data.List as List hiding (length ; foldr)
open import Data.List.Properties  

module ListMonoid where

  ListMonoid : Set → Monoid
  ListMonoid A = record
    { 
      Carrier = List A ;
      _∙_     = _++_ ; 
      ε       = [] ; 
      lid     = refl ; 
      rid     = λ { x } → ++-identityʳ x ; 
      assoc   = λ {x} {y} {z} → ++-assoc x y z  
    }

--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂
-}

open Monoid using (Carrier)

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

-- (M × N)

module ProdMonoid where

  ProdMonoid : Monoid → Monoid → Monoid
  ProdMonoid M N = record
    { Carrier = Carrier₁ × Carrier₂ ; 
      _∙_ = λ x y → (fst x) ∙₁ (fst y) , (snd x) ∙₂ (snd y)  ;  
      ε = ε₁ , ε₂ ; 
      lid = cong₂ (_,_) lid₁ lid₂ ; 
      rid = cong₂ (_,_) rid₁ rid₂ ; 
      assoc = cong₂ (_,_) assoc₁ assoc₂ 
    } 
    where
    open Monoid M renaming (Carrier to Carrier₁ ; ε to ε₁ ;  _∙_ to _∙₁_ ; lid to lid₁; rid to rid₁ ; assoc to assoc₁)
    open Monoid N renaming (Carrier to Carrier₂ ; ε to ε₂ ;  _∙_ to _∙₂_ ; lid to lid₂ ; rid to rid₂; assoc to assoc₂)



--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≡ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo (M N : Monoid)(morph : Carrier M → Carrier N) : Set₁ where
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≡ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≡ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo M (Cayley M) (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext (λ x → lid)
                       ; preserves-mult = ext (λ x → assoc) }
                  where open Monoid M

--------------------------------------------------
{- Ejercicio: Probar que length es un homorfismo de monoides -}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

open ListMonoid
open NatMonoid

proof-length : {A : Set } → (xs : List A) → (ys : List A) → length (xs ++ ys) ≡ length xs + length ys
proof-length [] [] = refl
proof-length [] (y ∷ ys) = cong suc refl
proof-length (x ∷ xs) ys = cong suc (proof-length xs ys)

length-is-monoid-homo : {A : Set} → Is-Monoid-Homo (ListMonoid A) NatMonoid length
length-is-monoid-homo = record { 
  preserves-unit = refl ; 
  preserves-mult = λ {x} {y} → proof-length x y  }

--------------------------------------------------
{- Ejercicio: Probar que multiplicar por una constante es un es un homorfismo de NatMonoid -}

mult-const-proof : {c : ℕ} → Is-Monoid-Homo NatMonoid NatMonoid (_* c)
mult-const-proof {c} = record { 
  preserves-unit = refl ; 
  preserves-mult = λ {x} {y} → *-distribʳ-+ c x y } 

--------------------------------------------------
module Foldr (M : Monoid) where

 open Monoid M renaming (Carrier to MCarrier ; lid to mlid ; rid to mrid )

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}


 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e [] = e
 foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

-- _≡⟨_⟩_
 proof-foldr : (xs : List MCarrier) → (ys : List MCarrier) → foldr _∙_ ε (xs ++ ys) ≡ foldr _∙_ ε xs ∙ foldr _∙_ ε ys
 proof-foldr [] ys = sym mlid
 proof-foldr (x ∷ xs) ys = 
  begin 
    (x ∙ foldr _∙_ ε (xs ++ ys)) 
  ≡⟨ (cong (x ∙_) (proof-foldr xs ys)) ⟩ 
   (x ∙ (foldr _∙_ ε xs ∙ foldr _∙_ ε ys)) 
  ≡⟨ sym assoc ⟩
      (x ∙ foldr _∙_ ε xs) ∙ foldr _∙_ ε ys 
  ∎

 foldr-is-monoid-homo : Is-Monoid-Homo (ListMonoid MCarrier) M (foldr _∙_ ε)
 foldr-is-monoid-homo = record { 
   preserves-unit = refl ; 
   preserves-mult = λ {x} {y} → {! proof-foldr x y  !} }

--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≡ b
        law2 : ∀ a → inv (fun a) ≡ a

open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos (record) ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}

module NatIsoList where
  data ⊤ : Set where
    tt : ⊤

  proof-fun-x : ℕ → (List ⊤)
  proof-fun-x zero = []
  proof-fun-x (suc n) = tt ∷ (proof-fun-x n)

  proof-inv : (List ⊤) → ℕ
  proof-inv xs = length xs

  proof-l1 : (xs : List ⊤) → proof-fun-x (proof-inv xs) ≡ xs
  proof-l1 [] = refl
  proof-l1 (tt ∷ xs) = cong (tt ∷_) (proof-l1 xs)

  proof-l2 : (a : ℕ) → proof-inv (proof-fun-x a) ≡ a
  proof-l2 zero = refl
  proof-l2 (suc a) = cong suc (proof-l2 a) 

  proof-nat-list-iso : Iso ℕ  (List ⊤)
  proof-nat-list-iso = record { 
    fun = proof-fun-x ; 
    inv = proof-inv ; 
    law1 = proof-l1 ; 
    law2 = proof-l2 }

{- Ejercicio: introducir un constructor de tipos Maybe (o usar Data.Maybe) y probar que
Maybe ℕ es isomorfo a ℕ -}

module MaybeIsoN where
  
  data Maybe {a} (A : Set a) : Set a where
    just : A → Maybe A
    nothing : Maybe A

  proof-fun : Maybe ℕ → ℕ
  proof-fun nothing = zero
  proof-fun (just x) = suc x

  proof-inv : ℕ → Maybe ℕ
  proof-inv zero = nothing
  proof-inv (suc n) = just n

  proof-l1 : (b : ℕ) → proof-fun (proof-inv b) ≡ b
  proof-l1 zero = refl
  proof-l1 (suc b) = refl

  proof-l2 : (a : Maybe ℕ) → proof-inv (proof-fun a) ≡ a
  proof-l2 nothing = refl
  proof-l2 (just x) = refl

  proof-maybe-iso-n : Iso (Maybe ℕ) ℕ
  proof-maybe-iso-n = record { 
    fun = proof-fun ; 
    inv = proof-inv ; 
    law1 = proof-l1 ; 
    law2 = proof-l2 }

{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}

module IsoProd where
  open import Data.Product

  pfun : {A B C : Set} → (A → B × C) → (A → B) × (A → C)
  pfun f = (λ x → proj₁ (f x)) , (λ x → proj₂ (f x))

  pinv : {A B C : Set} → ((A → B) × (A → C)) → (A → B × C)
  pinv (f , g) = λ x → (f x) , (g x)

  proof-iso-prod : {A B C : Set} → Iso (A → B × C) ((A → B) × (A → C))
  proof-iso-prod = record { 
    fun = pfun ; 
    inv = pinv ; 
    law1 = λ b → refl ; 
    law2 = λ a → refl }  


{- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
Vec (A × B) n para todos A, B habitantes de Set y n natural -}

module VecIso where

  open import Data.Vec

  pfun : {n : ℕ} → {A B : Set} → ((Vec A n) × (Vec B n)) → Vec (A × B) n
  pfun ([] , []) = []
  pfun (x ∷ xs , y ∷ ys) = (x , y) ∷ (pfun (xs , ys))

  pinv : {n : ℕ} → {A B : Set} → (Vec (A × B) n) → ((Vec A n) × (Vec B n))
  pinv [] = [] , []
  pinv (x ∷ b) with pinv b
  ... | ba , bb = (((fst x) ∷ ba) , ((snd x) ∷ bb))

  pl1 : {n : ℕ} → {A B : Set}  → (b : Vec (A × B) n) → pfun (pinv b) ≡ b
  pl1 [] = refl
  pl1 (x ∷ b) = cong (λ z → x ∷ z) (pl1 b)

  pl2 : {n : ℕ} → {A B : Set}  → (a : Vec A n × Vec B n) → pinv (pfun a) ≡ a
  pl2 ([] , []) = refl
  pl2 (x ∷ xs , y ∷ ys) = cong (λ w → x ∷ (fst w) , y ∷ (snd w)) (pl2 (xs , ys))

  -- (pinv ((x , y) ∷ pfun (xs , ys)) | pinv (pfun (xs , ys))) ≡ (x ∷ xs , y ∷ ys)

  proof-vec-iso : {n : ℕ} → {A B : Set}  → Iso ((Vec A n) × (Vec B n)) (Vec (A × B) n)
  proof-vec-iso = record { 
    fun = pfun ; 
    inv = pinv ; 
    law1 = pl1 ; 
    law2 = pl2 }


--------------------------------------------------
{- Ejercicio Extra
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≡ y) × (∀ x' → f x' ≡ y → x ≡ x')) 
  
