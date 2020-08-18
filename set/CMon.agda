{-# OPTIONS --cubical --safe #-}

module set.CMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

record CMon {ℓ} (M : Type ℓ) : Type ℓ where
  field
    e : M
    _⊗_ : M → M → M
    comm-⊗ : ∀ x y → x ⊗ y ≡ y ⊗ x
    assoc-⊗ : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    unit-⊗ : ∀ x → e ⊗ x ≡ x
    MSet : isSet M

record CMonHom {ℓ} {M N : Type ℓ} (CM : CMon M) (CN : CMon N) : Type ℓ where
  open CMon CM renaming (e to eM ; _⊗_ to _⊗M_)
  open CMon CN renaming (e to eN ; _⊗_ to _⊗N_)
  field
    f : M → N
    f-e : f eM ≡ eN
    f-++ : ∀ x y → f (x ⊗M y) ≡ f x ⊗N f y
    f-sing : ∀ x → f (eM ⊗M x) ≡ eN ⊗N f x
