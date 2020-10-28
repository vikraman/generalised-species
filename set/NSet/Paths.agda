{-# OPTIONS --cubical --exact-split --safe #-}

module set.NSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import set.NSet

-- private
--   variable
--     ℓ ℓ₁ ℓ₂ : Level
--     A : Type ℓ

module _ {ℓ : Level} {A : Type ℓ} where

  -- non-terminating
  -- code : NSet A → NSet A → Type ℓ
  -- code [] ys = [] ≡ ys
  -- code (x :: xs) [] = Lift ⊥
  -- code (x :: xs) (y :: ys) =
  --     ((x ≡ y) × code xs ys)
  --   ⊎ Σ (NSet A) λ zs → code xs (y :: zs) × code ys (x :: zs)
  -- code (x :: xs) (comm p q i) = {!!}
  -- code (x :: xs) (trunc ys zs p q i j) = {!!}
  -- code (comm p q i) ys = {!!}
  -- code (trunc xs zs p q i j) ys = {!!}

  -- x ∈ (y :: xs) = (x ≡ y) ⊎ Σ (NSet A) λ zs → xs ≡ x :: zs

  _∈'_ : A → NSet A → Type ℓ
  x ∈' xs = elim.f (Lift ⊥)
                   (λ y {xs} p → (x ≡ y) ⊎ p)
                   {!!}
                   {!!}
                   xs

  _∈_ : A → NSet A → Type ℓ
  x ∈ [] = Lift ⊥
  x ∈ (y :: xs) = (x ≡ y) ⊎ (x ∈ xs)
  x ∈ comm p q i = {!!}
  x ∈ trunc xs ys p q i j = {!!}
