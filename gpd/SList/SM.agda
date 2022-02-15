{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SM where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG

open import gpd.SList.SMGStructure

module _ {i} {A : Type i} where

  module ++-β² (xs ys : SList A) where

    f : ++-β.f xs ys ∙ ++-β.f ys xs == idp
    f =
      SListElimProp.f {P = λ zs → ++-β.f zs ys ∙ ++-β.f ys zs == idp} ⦃ two-paths-level ⦄
        {!!}
        {!!}
        xs
