{-# OPTIONS --cubical #-}

module MoreCat where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Additive
open import Cubical.Categories.Abelian
open import Cubical.Categories.Morphism
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Data.Sigma

private variable ℓO ℓM ℓ ℓ' ℓ'' : Level

module _ {Cat : Category ℓO ℓM} where
  open Category Cat

  record Coequalizer {X Y : ob} (f g : Hom[ X , Y ]) : Type (ℓ-max ℓO ℓM) where
    field
      Q : ob
      q : Hom[ Y , Q ]
      univ : {Q' : ob} (q' : Hom[ Y , Q' ]) → ∃![ u ∈ Hom[ Q , Q' ] ] u ∘ q ≡ q'

module _ {Cat : AbelianCategory ℓO ℓM} where
  open AbelianCategory Cat

  record Image {X Y : ob} (f : Hom[ X , Y ]) : Type (ℓ-max ℓO ℓM) where
    field
      Im : ob
      m : Hom[ Im , Y ]
      mMono : isMonic cat m
      e : Hom[ X , Im ]
      eProp : f ≡ e ⋆ m
      univ : (Im' : ob) (e' : Hom[ X , Im' ]) (m' : Hom[ Im' , Y ])
        (m'Mono : isMonic cat m') (e'Prop : f ≡ e' ⋆ m')
        → ∃![ v ∈ Hom[ Im , Im' ] ] m ≡ v ⋆ m'

  module _ {A B C : ob} where
    open AbGroupStr

    zAbsorbL : (f : Hom[ A , B ]) → f ⋆ 0h {y = C} ≡ 0h
    zAbsorbL f = 
      let idemp = cong (f ⋆_) (sym (homAbStr _ _ .+IdL 0h)) ∙ ⋆distl+ _ _ _ in
      GroupTheory.idFromIdempotency (AbGroup→Group (Hom[ _ , _ ] , homAbStr _ _)) _ idemp

  module _ {X Y : ob} (f : Hom[ X , Y ]) where
    kernelMono : isMonic cat (ker f)
    kernelMono {a = x} {y} p = 
      let p' = sym (⋆Assoc _ _ _) ∙ cong (_⋆ f) p ∙ ⋆Assoc _ _ _ in
      let K = hasKernels f .Kernel.k in
      let h = x ⋆ ker f in
      let
        hf≡0 : h ⋆ f ≡ 0h
        hf≡0 = ⋆Assoc _ _ _ ∙ cong (x ⋆_) (hasKernels f .Kernel.ker⋆f) ∙ zAbsorbL x
      in 
      let uniq = hasKernels f .Kernel.univ _ h hf≡0 in
      let u = uniq .fst .fst in
      let
        x≡u : x ≡ u
        x≡u = cong fst (sym (uniq .snd (x , refl)))
        y≡u = cong fst (sym (uniq .snd (y , sym p)))
      in
      x≡u ∙ sym y≡u

  module _ {X Y : ob} (f : Hom[ X , Y ]) where
    open Image

    f⋆coker≡0 : f ⋆ coker f ≡ 0h
    f⋆coker≡0 = hasCokernels f .Cokernel.f⋆coker

    hasImages : Image f
    hasImages .Im = _
    hasImages .m = ker (coker f)
    hasImages .mMono {a = x} {y} p = kernelMono (coker f) p
    hasImages .e = hasKernels (coker f) .Kernel.univ X f f⋆coker≡0 .fst .fst
    hasImages .eProp = sym (hasKernels (coker f) .Kernel.univ X f f⋆coker≡0 .fst .snd)
    hasImages .univ Im' e' m' m'Mono f≡e'm' = ({!   !} , {!   !}) , {!   !}