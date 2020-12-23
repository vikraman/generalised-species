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
