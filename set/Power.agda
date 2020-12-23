{-# OPTIONS --cubical --exact-split --safe #-}

module set.Power where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Agda.Primitive

private
  variable
    ℓ : Level

open import Cubical.Functions.Logic
open import Cubical.Foundations.Powerset

PSet : hSet ℓ → hSet (ℓ-suc ℓ)
PSet (A , ϕ) = ℙ A , powersets-are-sets

η : {ASet@(A , ϕ) : hSet ℓ} → A → ℙ A
η {ASet = (A , ϕ)} x = λ y → (x ≡ y) , ϕ x y

_* : {A B : Type ℓ} → (A → ℙ B) → ℙ A → ℙ B
_* {A = A} {B} f = λ X b → ∃[ a ] f a b ⊓ X a

map : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} → (A → B) → ℙ A → ℙ B
map {BSet = BSet} f = (η {ASet = BSet} ∘ f) *

open import set.Monad

-- PSetRMonad : ∀ {ℓ} → RMonad {ℓ} ℙ
-- RMonad.map PSetRMonad = {!!}
-- RMonad.η PSetRMonad = {!!}
-- PSetRMonad RMonad.* = {!!}
-- RMonad.unitl PSetRMonad = {!!}
-- RMonad.unitr PSetRMonad = {!!}
-- RMonad.assoc PSetRMonad = {!!}
