{-# OPTIONS --cubical --exact-split --safe #-}

module set.Power where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Agda.Primitive

private
  variable
    ℓ : Level

open import Cubical.Foundations.Logic

P : hSet ℓ → hSet (ℓ-suc ℓ)
P (A , ϕ) = ℙ A , powersets-are-sets

η : {A : hSet ℓ} → A .fst → P A .fst
η {A = (A , ϕ)} x = λ y → (x ≡ y) , ϕ x y

_* : {A B : Type ℓ} → (A → ℙ B) → ℙ A → ℙ B
_* {A = A} {B} f = λ X b → ∃[ a ] f a b ⊓ X a

open import set.Monad

PRMonad : ∀ {ℓ} → RMonad {ℓ} {ℓ-suc ℓ} ℙ
RMonad.map PRMonad f = {!!}
RMonad.η PRMonad = η {A = {!!}}
PRMonad RMonad.* = {!!}
RMonad.unitl PRMonad = {!!}
RMonad.unitr PRMonad = {!!}
RMonad.assoc PRMonad = {!!}

-- η PKleisli = λ a → λ b → (a ≡ b) , {!!}
-- PKleisli * = {!!}
-- l1 PKleisli = {!!}
-- l2 PKleisli = {!!}
-- l3 PKleisli = {!!}
