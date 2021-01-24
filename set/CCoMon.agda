{-# OPTIONS --cubical #-}

module set.CCoMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.Prelude
open import set.hRel

record CCoMon {ℓ} (C : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    e : C ⇸ II
    Δ : C ⇸ (C ⊗ C)
    isSetC : isSet C

  CSet : hSet ℓ
  CSet = C , isSetC

open import set.MSet
open import set.Power as P

module _ {ℓ} {ASet@(A , ϕ) : hSet ℓ} where

  MSetCCoMon : CCoMon (MSet A)
  CCoMon.e MSetCCoMon xs tt = よ (MSet A , trunc) xs []
  CCoMon.Δ MSetCCoMon = TODO
  CCoMon.isSetC MSetCCoMon = TODO
