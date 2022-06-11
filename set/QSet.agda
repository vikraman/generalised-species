{-# OPTIONS --cubical --exact-split #-}

module set.QSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List as L
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

infix 3 _≈₀_ _≈_ _■_

data _≈₀_ {ℓ} {A : Type ℓ} : List A → List A → Type ℓ where
  nil-refl : [] ≈₀ []
  cons-cong : ∀ {a b as bs}
            → (a ≡ b) → (as ≈₀ bs)
            → (a ∷ as) ≈₀ (b ∷ bs)
  comm-rel : ∀ {a b as bs cs}
           → (p : as ≈₀ (b ∷ cs)) → (q : (a ∷ cs) ≈₀ bs)
           → (a ∷ as) ≈₀ (b ∷ bs)

_≈_ : List A → List A → Type _
xs ≈ ys = ∥ xs ≈₀ ys ∥₁

import set.Perm as R

postulate
  0→1 : {xs ys : List A} → xs ≈₀ ys → xs R.≈₁ ys
  1→0 : {xs ys : List A} → xs R.≈₁ ys → xs ≈₀ ys

≈₀-refl : (xs : List A) → xs ≈₀ xs
≈₀-refl [] = nil-refl
≈₀-refl (x ∷ xs) = cons-cong refl (≈₀-refl xs)

≈-refl : (xs : List A) → xs ≈ xs
≈-refl = ∣_∣₁ ∘ ≈₀-refl

≈₀-sym : (xs ys : List A) → xs ≈₀ ys → ys ≈₀ xs
≈₀-sym .[] .[] nil-refl = nil-refl
≈₀-sym .(_ ∷ _) .(_ ∷ _) (cons-cong p q) = cons-cong (p ⁻¹) (≈₀-sym _ _ q)
≈₀-sym .(_ ∷ _) .(_ ∷ _) (comm-rel p q) = comm-rel (≈₀-sym _ _ q) (≈₀-sym _ _ p)

≈-sym : (xs ys : List A) → xs ≈ ys → ys ≈ xs
≈-sym xs ys = P.map (≈₀-sym xs ys)

≈₀-trans : (xs ys zs : List A) → xs ≈₀ ys → ys ≈₀ zs → xs ≈₀ zs
≈₀-trans xs ys zs p q = 1→0 (R.≈₁-trans xs ys zs (0→1 p) (0→1 q))

_■_ : {xs ys zs : List A} → xs ≈₀ ys → ys ≈₀ zs → xs ≈₀ zs
_■_ = ≈₀-trans _ _ _

≈-trans : (xs ys zs : List A) → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans xs ys zs = P.map2 (≈₀-trans xs ys zs)

QSet : Type ℓ → Type ℓ
QSet A = List A / _≈_
