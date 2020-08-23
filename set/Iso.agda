{-# OPTIONS --cubical --exact-split --safe #-}

module set.Iso where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import set.MSet as M
open import set.NSet as N
open import set.MSet.Universal as M
open import set.NSet.Universal as N

private
  variable
    ℓ : Level
    A : Type ℓ

M≃N : MSet A ≃ NSet A
M≃N {ℓ} {A} = isoToEquiv (iso f g f-g g-f)
  where module f-univ = M.univ N.NSetCMon (λ a → N.[ a ])
        f : MSet A → NSet A
        f = f-univ.f♯
        module g-univ = N.univ M.MSetCMon (λ a → M.[ a ])
        g : NSet A → MSet A
        g = g-univ.f♯
        f-g : (xs : NSet A) → f (g xs) ≡ xs
        f-g = {!!}
        g-f : (xs : MSet A) → g (f xs) ≡ xs
        g-f = {!!}
