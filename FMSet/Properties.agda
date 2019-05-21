{-# OPTIONS --cubical --safe #-}

module FMSet.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import FMSet

private
  variable
    ℓ : Level
    A : Type₀

infixr 30 _++_

_++_ : ∀ (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : ∀ (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : ∀ (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ = FMSetElimProp.f (trunc _ _)
  refl
  (λ x p → cong (_∷_ x) p)

assoc-++ : ∀ (xs ys zs : FMSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = FMSetElimProp.f (propPi (λ _ → propPi (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (_∷_ x) (p ys zs))

cons-++ : ∀ (x : A) (xs : FMSet A) → x ∷ xs ≡ xs ++ [ x ]
cons-++ x = FMSetElimProp.f (trunc _ _)
  refl
  (λ y {xs} p → comm x y xs ∙ cong (_∷_ y) p)

comm-++ : ∀ (xs ys : FMSet A) → xs ++ ys ≡ ys ++ xs
comm-++ = FMSetElimProp.f (propPi (λ _ → trunc _ _))
  (λ ys → sym (unitr-++ ys))
  (λ x {xs} p ys → cong (x ∷_) (p ys)
                 ∙ cong (_++ xs) (cons-++ x ys)
                 ∙ sym (assoc-++ ys [ x ] xs))

record IsCMon (M : Type ℓ) : Type ℓ where
  field
    e : M
    _⊗_ : M → M → M
    comm-⊗ : ∀ x y → x ⊗ y ≡ y ⊗ x
    assoc-⊗ : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    unit-⊗ : ∀ x → e ⊗ x ≡ x
    MSet : isSet M

FMSetCMon : IsCMon (FMSet A)
FMSetCMon = record
              { e = []
              ; _⊗_ = _++_
              ; comm-⊗ = comm-++
              ; assoc-⊗ = assoc-++
              ; unit-⊗ = unitl-++
              ; MSet = trunc
              }

record IsCMonHom {M N : Type ℓ} (CM : IsCMon M) (CN : IsCMon N) : Type ℓ where
  open IsCMon CM renaming (e to eM ; _⊗_ to _⊗M_)
  open IsCMon CN renaming (e to eN ; _⊗_ to _⊗N_)
  field
    f : M → N
    f-e : f eM ≡ eN
    f-++ : ∀ x y → f (x ⊗M y) ≡ f x ⊗N f y
    f-sing : ∀ x → f (eM ⊗M x) ≡ eN ⊗N f x

module FMSetUniversal {M : Type ℓ} (C : IsCMon M) (f : A → M) where

  open IsCMon C

  f♯ : FMSet A → M
  f♯ = FMSetRec.f MSet e (λ x m → f x ⊗ m)
         (λ x y m → comm-⊗ (f x) (f y ⊗ m) ∙ sym (assoc-⊗ (f y) m (f x)) ∙ cong (f y ⊗_) (comm-⊗ m (f x)))

  f♯-nil : f♯ [] ≡ e
  f♯-nil = refl

  f♯-cons : ∀ x xs → f♯ (x ∷ xs) ≡ f x ⊗ f♯ xs
  f♯-cons x xs = refl

  f♯-sing : ∀ x → f♯ [ x ] ≡ f x
  f♯-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

  f♯-++ : ∀ xs ys → f♯ (xs ++ ys) ≡ f♯ xs ⊗ f♯ ys
  f♯-++ = FMSetElimProp.f (propPi λ _ → MSet _ _)
    (λ ys → sym (unit-⊗ (f♯ ys)))
    (λ x {xs} p ys → cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f♯ xs) (f♯ ys))

  module _ (h : FMSet A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    f♯-unique : h ≡ f♯
    f♯-unique = funExt (FMSetElimProp.f (MSet _ _)
      h-nil (λ x {xs} p → (h-++ [ x ] xs) ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p))
