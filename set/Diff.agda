{-# OPTIONS --cubical --exact-split #-}

module set.Diff where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Agda.Primitive

-- open import set.Power as P
open import set.hRel
open import set.MSet
open import set.MSet.Paths

variable
  ℓ : Level
  A B : Type ℓ

_♯ : (A → MSet B) → (A ⇸ MSet B)
_♯ = _# {BSet = MSet _ , trunc}

δ : MSet A ⇸ MSet (MSet A)
δ = (μ ♯) †

ε : MSet A ⇸ A
ε = (η ♯) †
