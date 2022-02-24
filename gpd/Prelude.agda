{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.Prelude where

open import lib.Base public
open import lib.NType public
open import lib.NType2 public
-- open import lib.PathSeq public
open import lib.PathOver public
open import lib.PathFunctor public
open import lib.PathGroupoid public
open import lib.Equivalence public
open import lib.Equivalence2 public
open import lib.Funext public
open import lib.types.Pi public
open import lib.types.Paths public

open import gpd.Paths public

postulate
  TODO : ∀ {ℓ} {A : Type ℓ} → A
