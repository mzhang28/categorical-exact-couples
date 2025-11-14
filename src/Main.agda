{-# OPTIONS --cubical #-}

module Main where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Abelian
open import Cubical.Categories.Isomorphism

private variable ℓO ℓM ℓ ℓ' ℓ'' : Level

module _ {Cat : AbelianCategory ℓO ℓM} where
  open AbelianCategory Cat

  IsExact : {A B C : ob} → (f : Hom[ A , B ]) → (g : Hom[ B , C ]) → Type _
  IsExact f g =
    let cokerF = hasCokernels f in
    let imF = hasKernels (cokerF .Cokernel.coker) in
    let kerG = hasKernels g in
    CatIso cat (imF .Kernel.k) (kerG .Kernel.k)

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

    module AC where -- defining A' C'
      A' : ob
      A' = imF .Kernel.k

      d : Hom[ C , C ]
      d = g ∘ h

      C' : ob
      C' = {!   !}



    
