{-# OPTIONS --cubical --exact-split --safe #-}

module set.NSet.Universal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import set.NSet

private
  variable
    ℓ ℓ₁ : Level
    A : Type ℓ

infixr 30 _++_

_++_ : ∀ (xs ys : NSet A) → NSet A
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys
comm p q i ++ ys = comm (cong (_++ ys) p) (cong (_++ ys) q) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : (xs : NSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : (xs : NSet A) → xs ++ [] ≡ xs
unitr-++ = elimProp.f (trunc _ _)
  refl
  (λ x p → cong (x ::_) p)

assoc-++ : (xs ys zs : NSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = elimProp.f (isPropΠ (λ _ → isPropΠ (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (x ::_) (p ys zs))

swap : (x y : A) (xs : NSet A)
     → x :: y :: xs ≡ y :: x :: xs
swap x y xs = comm refl refl

cons-++ : (x : A) (xs : NSet A) → x :: xs ≡ xs ++ [ x ]
cons-++ x = elimProp.f (trunc _ _)
  refl
  (λ y {xs} p → swap x y xs ∙ cong (y ::_) p)

comm-++ : (xs ys : NSet A) → xs ++ ys ≡ ys ++ xs
comm-++ = elimProp.f (isPropΠ (λ _ → trunc _ _))
  (λ ys → sym (unitr-++ ys))
  (λ x {xs} p ys → cong (x ::_) (p ys)
                 ∙ cong (_++ xs) (cons-++ x ys)
                 ∙ sym (assoc-++ ys [ x ] xs))

open import set.CMon

NSetCMon : CMon (NSet A)
NSetCMon = record
              { e = []
              ; _⊗_ = _++_
              ; comm-⊗ = comm-++
              ; assoc-⊗ = assoc-++
              ; unit-⊗ = unitl-++
              ; isSetM = trunc
              }


module univ {M : Type ℓ₁} (C : CMon M) (f : A → M) where

  open CMon C

  f♯ : NSet A → M
  f♯ = elim.f e (λ x m → f x ⊗ m)
              (λ {a b} {as bs cs} {bas bbs bcs} {p} bp {q} bq →
                cong (f a ⊗_) bp
              ∙ assoc-⊗ (f a) (f b) bcs
              ∙ cong (_⊗ bcs) (comm-⊗ (f a) (f b))
              ∙ sym (assoc-⊗ (f b) (f a) bcs)
              ∙ cong (f b ⊗_) bq)
              (λ _ → isSetM)

  f♯-nil : f♯ [] ≡ e
  f♯-nil = refl

  f♯-cons : ∀ x xs → f♯ (x :: xs) ≡ f x ⊗ f♯ xs
  f♯-cons x xs = refl

  f♯-sing : ∀ x → f♯ [ x ] ≡ f x
  f♯-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

  f♯-++ : ∀ xs ys → f♯ (xs ++ ys) ≡ f♯ xs ⊗ f♯ ys
  f♯-++ = elimProp.f (isPropΠ λ _ → isSetM _ _)
    (λ ys → sym (unit-⊗ (f♯ ys)))
    (λ x {xs} p ys → cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f♯ xs) (f♯ ys))

  module _ (h : NSet A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    f♯-unique : h ≡ f♯
    f♯-unique = funExt (elimProp.f (isSetM _ _)
      h-nil (λ x {xs} p → (h-++ [ x ] xs) ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p))
