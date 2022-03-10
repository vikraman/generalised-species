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
    SList-SMGStructure : SMGStructure (SList A) ⦃ ? ⦄
    SMGStructure.I SList-SMGStructure = nil
    SMGStructure._⊗_ SList-SMGStructure = _++_
    SMGStructure.α SList-SMGStructure X Y Z = ++-α.f X Y Z
    SMGStructure.Λ SList-SMGStructure X = ++-Λ.f X
    SMGStructure.ρ SList-SMGStructure X = ++-ρ.f X
    SMGStructure.β SList-SMGStructure X Y = ++-β.f X Y
    SMGStructure.▽ SList-SMGStructure X Y = ++-▽.f X Y
    SMGStructure.⬠ SList-SMGStructure W X Y Z = ++-⬠.f W X Y Z
    SMGStructure.⬡ SList-SMGStructure X Y Z = ++-⬡.f X Y Z
    SMGStructure.β² SList-SMGStructure X Y = TODO -- ++-β².f X Y
