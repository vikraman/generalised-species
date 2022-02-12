{-# OPTIONS --without-K --exact-split --rewriting #-}

open import gpd.SList.SMGStructure

module gpd.SList.Properties where

  module _ {j} {N : Type j} ⦃ _ : has-level 1 N ⦄ ⦃ GN : SMGStructure N ⦄ where

    _♯ : (A → N) → SMFunctor (SList A) N
    f ♯ = ?

    SList-Universal : SMFunctor (SList A) N ≃ (A → N)
    SList-Universal = TODO
