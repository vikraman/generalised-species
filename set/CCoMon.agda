{-# OPTIONS --cubical #-}

module set.CCoMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.hRel

record CCoMon {ℓ} (C : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    e : C ⇸ O
    Δ : C ⇸ (C ⊕ C)
    isSetC : isSet C

  CSet : hSet ℓ
  CSet = C , isSetC

  field
    comm-Δ : (σ {ASet = CSet} {CSet}) ⊚ Δ ≡ Δ
    -- unit-Δ : ⊕[ e , id CSet ] ⊚ Δ ≡ {!!}
    -- assoc-Δ, unitr-Δ
