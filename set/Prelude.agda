{-# OPTIONS --cubical #-}

module set.Prelude where

open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (funExt⁻ to happly) public

postulate
  TODO : ∀ {ℓ} {A : Type ℓ} → A
