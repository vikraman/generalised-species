{-# OPTIONS --cubical #-}

module _ where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _∷_

data M {ℓ} (A : Type ℓ) : Type ℓ where
  []    : M A
  _∷_   : (x : A) → (xs : M A) → M A
  swap  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  hexagon : ∀ x y z xs → swap x y (z ∷ xs) ∙ ((λ i → y ∷ swap x z xs i) ∙ swap y z (x ∷ xs))
                       ≡ (λ i → x ∷ swap y z xs i) ∙ (swap x z (y ∷ xs) ∙ (λ i → z ∷ swap x y xs i))
  swap2 : ∀ x y xs → sym (swap x y xs) ≡ swap y x xs
  trunc : isGroupoid (M A)

pattern [_] x = x ∷ []

variable
  ℓ : Level
  A : Type ℓ

infixr 30 _⊗_

_⊗_ : ∀ (xs ys : M A) → M A
[] ⊗ ys = ys
(x ∷ xs) ⊗ ys = x ∷ xs ⊗ ys
swap x y xs i ⊗ ys =
  swap x y (xs ⊗ ys) i
hexagon x y z xs i j ⊗ ys =
  hexagon x y z (xs ⊗ ys) i j -- transp (λ i → A) i x != x of type A
swap2 x y xs i j ⊗ ys =
  swap2 x y (xs ⊗ ys) i j
trunc xs zs p q u v i j k ⊗ ys =
  trunc (xs ⊗ ys) (zs ⊗ ys) (cong (_⊗ ys) p)
    (cong (_⊗ ys) q) (cong (cong (_⊗ ys)) u) (cong (cong (_⊗ ys)) v) i j k
