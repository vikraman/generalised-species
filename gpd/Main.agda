{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.Main where

open import gpd.Prelude
open import gpd.FSMG
open import gpd.SList
open import gpd.UFin

-- and these are symmetric monoidal equivalences

thm1 : ∀ {i} {A : Type i} → FSMG A ≃ SList A
thm1 = TODO

thm2 : ∀ {i} {A : Type i} → SList A ≃ UFin A
thm2 = TODO
