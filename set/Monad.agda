{-# OPTIONS --cubical --exact-split --safe #-}

module set.Monad where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

record Monad {ℓ} (T : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    map : {A B : Type ℓ} → (A → B) → T A → T B
    η : {A : Type ℓ} → A → T A
    _* : {A B : Type ℓ} → (A → T B) → T A → T B
    unitl : {A : Type ℓ} → η * ≡ idfun (T A)
    unitr : {A B : Type ℓ} (f : A → T B) → f * ∘ η ≡ f
    assoc : {A B C : Type ℓ} (f : A → T B) (g : B → T C) → g * ∘ f * ≡ (g * ∘ f) *

  μ : {A : Type ℓ} → T (T A) → T A
  μ = idfun (T _) *

  σ : {A B : Type ℓ} → T A × B → T (A × B)
  σ = uncurry (flip λ b → (λ a → η (a , b)) *)

  τ : {A B : Type ℓ} → A × T B → T (A × B)
  τ = uncurry λ a → (λ b → η (a , b)) *

  _⊚_ : {A B C : Type ℓ} → (A → T B) → (B → T C) → A → T C
  f ⊚ g = g * ∘ f

record RMonad {ℓ₁} {ℓ₂} (T : Type ℓ₁ → Type ℓ₂) : Type (ℓ-max (ℓ-suc ℓ₁) ℓ₂) where
  field
    map : {A B : Type ℓ₁} → (A → B) → T A → T B
    η : {A : Type ℓ₁} → A → T A
    _* : {A B : Type ℓ₁} → (A → T B) → T A → T B
    unitl : {A : Type ℓ₁} → η * ≡ idfun (T A)
    unitr : {A B : Type ℓ₁} (f : A → T B) → f * ∘ η ≡ f
    assoc : {A B C : Type ℓ₁} (f : A → T B) (g : B → T C) → g * ∘ f * ≡ (g * ∘ f) *

  σ : {A B : Type ℓ₁} → T A × B → T (A × B)
  σ = uncurry (flip λ b → (λ a → η (a , b)) *)

  τ : {A B : Type ℓ₁} → A × T B → T (A × B)
  τ = uncurry λ a → (λ b → η (a , b)) *

  _⊚_ : {A B C : Type ℓ₁} → (A → T B) → (B → T C) → A → T C
  f ⊚ g = g * ∘ f

record RMonadhSet {ℓ₁} {ℓ₂} (T : Type ℓ₁ → Type ℓ₂) : Type (ℓ-max (ℓ-suc ℓ₁) ℓ₂) where
  field
    map : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ₁} → (A → B) → T A → T B
    η : {ASet@(A , ϕ) : hSet ℓ₁} → A → T A
    _* : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ₁} → (A → T B) → T A → T B
    unitl : {ASet@(A , ϕ) : hSet ℓ₁} →  _* {ASet} {ASet} (η {ASet}) ≡ idfun (T A)
    unitr : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ₁} (f : A → T B) → (_* {ASet} {BSet} f) ∘ (η {ASet}) ≡ f
    assoc : {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) : hSet ℓ₁} (f : A → T B) (g : B → T C)
          → (_* {BSet} {CSet} g) ∘ (_* {ASet} {BSet} f) ≡ _* {ASet} {CSet} ((_* {BSet} {CSet} g) ∘ f)

  σ : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ₁} → T A × B → T (A × B)
  σ {ASet = (A , ϕ)} {BSet = (B , ψ)} = uncurry (flip λ b → (_* {A , ϕ} {A × B , isSet× ϕ ψ} (λ a → η {A × B , isSet× ϕ ψ} (a , b))))

  τ : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ₁} → A × T B → T (A × B)
  τ {ASet = (A , ϕ)} {BSet = (B , ψ)} = uncurry λ a → _* {B , ψ} {A × B , isSet× ϕ ψ} (λ b → η {A × B , isSet× ϕ ψ} (a , b))

  _⊚_ : {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) : hSet ℓ₁} → (A → T B) → (B → T C) → A → T C
  _⊚_ {ASet = (A , ϕ)} {BSet = (B , ψ)} {CSet = (C , ξ)} f g = (_* {B , ψ} {C , ξ} g) ∘ f
