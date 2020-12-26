{-# OPTIONS --cubical --exact-split #-}

module set.hRel where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Agda.Primitive

open import set.Power as P

private
  variable
    ℓ : Level

infixr 10 _⇸_

_⇸_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⇸ B = A → ℙ B

isSet⇸ : {A B : Type ℓ} → isSet (A ⇸ B)
isSet⇸ = isSetΠ (λ _ → powersets-are-sets)

id : (ASet@(A , ϕ) : hSet ℓ) → A ⇸ A
id = よ

module _ {A B C : Type ℓ} where

  infixr 10 _⊚_
  _⊚_ : B ⇸ C → A ⇸ B → A ⇸ C
  g ⊚ f = g * ∘ f

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  unitl : {f : A ⇸ B} → id BSet ⊚ f ≡ f
  unitl {f} i = よ* {ASet = BSet} i ∘ f

  unitr : {f : A ⇸ B} → f ≡ f ⊚ id ASet
  unitr {f} i = *よ {ASet = ASet} {BSet = BSet} f i

module _ {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) DSet@(D , χ) : hSet ℓ} where

  assoc : {f : A ⇸ B} {g : B ⇸ C} {h : C ⇸ D} → h ⊚ (g ⊚ f) ≡ (h ⊚ g) ⊚ f
  assoc {f} {g} {h} i = (_**_ {ASet = BSet} {BSet = CSet} {CSet = DSet} h g) (~ i) ∘ f
