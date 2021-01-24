{-# OPTIONS --cubical --exact-split --safe #-}

module set.NSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import set.NSet
open import set.NSet.Universal

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A
    a x : A
    xs ys : NSet A
