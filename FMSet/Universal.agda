{-# OPTIONS --cubical --safe #-}

module FMSet.Universal where

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
comm a b as bs cs p q i ++ ys =
  comm a b (as ++ ys) (bs ++ ys) (cs ++ ys)
       (cong (_++ ys) p) (cong (_++ ys) q) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : ∀ (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : ∀ (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ = FMSetElimProp.f (trunc _ _)
  refl
  (λ x p → cong (x ∷_) p)

assoc-++ : ∀ (xs ys zs : FMSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = FMSetElimProp.f (propPi (λ _ → propPi (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (_∷_ x) (p ys zs))

cons-++ : ∀ (x : A) (xs : FMSet A) → x ∷ xs ≡ xs ++ [ x ]
cons-++ x = FMSetElimProp.f (trunc _ _)
  refl
  (λ y {xs} p → swap x y xs ∙ cong (_∷_ y) p)

comm-++ : ∀ (xs ys : FMSet A) → xs ++ ys ≡ ys ++ xs
comm-++ = FMSetElimProp.f (propPi (λ _ → trunc _ _))
  (λ ys → sym (unitr-++ ys))
  (λ x {xs} p ys → cong (x ∷_) (p ys)
                 ∙ cong (_++ xs) (cons-++ x ys)
                 ∙ sym (assoc-++ ys [ x ] xs))

open import CMon

FMSetCMon : CMon (FMSet A)
FMSetCMon = record
              { e = []
              ; _⊗_ = _++_
              ; comm-⊗ = comm-++
              ; assoc-⊗ = assoc-++
              ; unit-⊗ = unitl-++
              ; MSet = trunc
              }

module FMSetUniversal {M : Type ℓ} (C : CMon M) (f : A → M) where

  open CMon.CMon C

  f♯ : FMSet A → M
  f♯ = FMSetElim.f e (λ x m → f x ⊗ m)
                   (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq
                      → cong (f a ⊗_) bp
                      ∙ assoc-⊗ (f a) (f b) bcs
                      ∙ cong (_⊗ bcs) (comm-⊗ (f a) (f b))
                      ∙ sym (assoc-⊗ (f b) (f a) bcs) ∙ cong (f b ⊗_) bq)
                   (λ _ → MSet)

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
