{-# OPTIONS --cubical #-}

module Main where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Abelian
open import Cubical.Categories.Additive
open import Cubical.Categories.Isomorphism

open import MoreCat

private variable ℓO ℓM ℓ ℓ' ℓ'' : Level

module _ {Cat : AbelianCategory ℓO ℓM} where
  open AbelianCategory Cat
  open ZeroObject
  -- open ZeroMorphism

  IsExact : {A B C : ob} → (f : Hom[ A , B ]) → (g : Hom[ B , C ]) → Type _
  IsExact f g =
    let cokerF = hasCokernels f in
    let imF = hasKernels (cokerF .Cokernel.coker) in
    let kerG = hasKernels g in
    CatIso cat (imF .Kernel.k) (kerG .Kernel.k)

  IsExact→0 : {A B C : ob} {f : Hom[ A , B ]} {g : Hom[ B , C ]} → IsExact f g → f ⋆ g ≡ 0h
  IsExact→0 {A = A} {B} {C} {f} {g} exact = {!   !} where

  record ExactCouple : Type (ℓ-max ℓO ℓM) where
    constructor mkExactCouple
    field
      A C : ob
      f : Hom[ A , A ]
      g : Hom[ A , C ]
      h : Hom[ C , A ]
      exact-fg : IsExact f g
      exact-gh : IsExact g h
      exact-hf : IsExact h f
    
  module _ (X : ExactCouple) where
    open ExactCouple X

    private
      cokerF = hasCokernels f
      imF = hasKernels (cokerF .Cokernel.coker)

    module _ where -- defining A' C'
      A' : ob
      A' = imF .Kernel.k

      d : Hom[ C , C ]
      d = g ∘ h

      C' : ob
      C' = {!   !}

    module _ where -- defining f' g' h'
      f' : Hom[ A' , A' ]
      f' = {!   !}


    
