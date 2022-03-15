{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SMGStructure where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG
open import gpd.SList.SMGStructure.Tensor
open import gpd.SList.SMGStructure.1Paths
open import gpd.SList.SMGStructure.2Paths

module _ {i} {A : Type i} where

  -- FIXME: this takes too long to typecheck
  instance
    SList-SMGStructure : SMGStructure (SList A) ⦃ trunc ⦄
    SMGStructure.I SList-SMGStructure = nil
    SMGStructure._⊗_ SList-SMGStructure = _++_
    SMGStructure.α SList-SMGStructure = ++-α.f
    SMGStructure.Λ SList-SMGStructure = ++-Λ.f
    SMGStructure.ρ SList-SMGStructure = ++-ρ.f
    SMGStructure.β SList-SMGStructure = ++-β.f
    SMGStructure.▽ SList-SMGStructure = TODO -- ++-▽.f
    SMGStructure.⬠ SList-SMGStructure = TODO -- ++-⬠.f
    SMGStructure.⬡ SList-SMGStructure = TODO -- ++-⬡.f X Y Z
    SMGStructure.β² SList-SMGStructure = TODO -- ++-β².f X Y
