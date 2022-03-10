{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SM where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG

open import gpd.SList.SMGStructure

module _ {i} {A : Type i} where

  module ++-⬡ (xs ys zs : SList A) where

    f : ++-α.f xs ys zs ∙ ++-β.f xs (ys ++ zs) ∙ ++-α.f ys zs xs
      == ap (_++ zs) (++-β.f xs ys) ∙ ++-α.f ys xs zs ∙ ap (ys ++_) (++-β.f xs zs)
    f =
      SListRec2Paths.rec ⦃ trunc ⦄
        ?
        ?
        ?
        ?
        ?
        ?
        xs
