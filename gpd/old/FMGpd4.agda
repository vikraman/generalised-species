{-# OPTIONS --cubical #-}

module gpd.FMGpd4 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _∷_

data FMGpd {ℓ} (A : Type ℓ) : Type ℓ where
  [] : FMGpd A
  _∷_ : (x : A) → (xs : FMGpd A) → FMGpd A
  swap : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  swap2 : ∀ x y xs → sym (swap x y xs) ≡ swap y x xs
  hexx : ∀ x y z xs → isProp (x ∷ y ∷ z ∷ xs ≡ z ∷ y ∷ x ∷ xs)
  trunc : isGroupoid (FMGpd A)

variable
  ℓ : Level
  A : Type ℓ

hexagon : (x y z : A) (xs : FMGpd A)
        → swap x y (z ∷ xs) ∙ (λ i → y ∷ swap x z xs i) ∙ swap y z (x ∷ xs)
        ≡ (λ i → x ∷ swap y z xs i) ∙ swap x z (y ∷ xs) ∙ (λ i → z ∷ swap x y xs i)
hexagon x y z xs = hexx x y z xs _ _

pattern [_] x = x ∷ []

_⊗_ : (xs ys : FMGpd A) → FMGpd A
[] ⊗ ys = ys
(x ∷ xs) ⊗ ys = x ∷ (xs ⊗ ys)
swap x y xs i ⊗ ys =
  swap x y (xs ⊗ ys) i
swap2 x y xs i j ⊗ ys =
  swap2 x y (xs ⊗ ys) i j
hexx x y z xs p q i j ⊗ ys =
  hexx x y z (xs ⊗ ys) (cong (_⊗ ys) p) (cong (_⊗ ys) q) i j
trunc xs zs p q u v i j k ⊗ ys =
  trunc (xs ⊗ ys) (zs ⊗ ys) (cong (_⊗ ys) p)
    (cong (_⊗ ys) q) (cong (cong (_⊗ ys)) u) (cong (cong (_⊗ ys)) v) i j k

unitl-⊗ : (xs : FMGpd A) → [] ⊗ xs ≡ xs
unitl-⊗ xs = refl

unitr-⊗ : (xs : FMGpd A) → xs ⊗ [] ≡ xs
unitr-⊗ [] = refl
unitr-⊗ (x ∷ xs) i =
  x ∷ unitr-⊗ xs i
unitr-⊗ (swap x y xs i) j =
  swap x y (unitr-⊗ xs j) i
unitr-⊗ (swap2 x y xs i j) k =
  swap2 x y (unitr-⊗ xs k) i j
unitr-⊗ (hexx x y z xs p q i j) k =
  hexx x y z (unitr-⊗ xs k) (λ i → unitr-⊗ (p i) k) (λ i → unitr-⊗ (q i) k) i j
unitr-⊗ (trunc xs zs p q u v i j k) l =
  trunc (unitr-⊗ xs l) (unitr-⊗ zs l)
    (λ i → unitr-⊗ (p i) l) (λ i → unitr-⊗ (q i) l)
      (λ i j → unitr-⊗ (u i j) l) (λ i j → unitr-⊗ (v i j) l) i j k

assoc-⊗ : (xs ys zs : FMGpd A) → xs ⊗ (ys ⊗ zs) ≡ (xs ⊗ ys) ⊗ zs
assoc-⊗ [] ys zs = refl
assoc-⊗ (x ∷ xs) ys zs i =
  x ∷ assoc-⊗ xs ys zs i
assoc-⊗ (swap x y xs i) ys zs j =
  swap x y (assoc-⊗ xs ys zs j) i
assoc-⊗ (swap2 x y xs i j) ys zs k =
  swap2 x y (assoc-⊗ xs ys zs k) i j
assoc-⊗ (hexx x y z xs p q i j) ys zs k =
  hexx x y z (assoc-⊗ xs ys zs k)
    (λ i → assoc-⊗ (p i) ys zs k) (λ i → assoc-⊗ (q i) ys zs k) i j
assoc-⊗ (trunc xs ws p q u v i j k) ys zs l =
  trunc (assoc-⊗ xs ys zs l) (assoc-⊗ ws ys zs l)
    (λ i → assoc-⊗ (p i) ys zs l) (λ i → assoc-⊗ (q i) ys zs l)
      (λ i j → assoc-⊗ (u i j) ys zs l) (λ i j → assoc-⊗ (v i j) ys zs l) i j k

cons-⊗ : (x : A) (xs : FMGpd A) → x ∷ xs ≡ xs ⊗ [ x ]
cons-⊗ x [] = refl
cons-⊗ x (y ∷ xs) = swap x y xs ∙ (λ i → y ∷ cons-⊗ x xs i)
cons-⊗ x (swap y z xs i) = {!!}
cons-⊗ x (swap2 y z xs i j) = {!!}
cons-⊗ x (hexx y z w xs p q i j) = {!!}
cons-⊗ x (trunc xs ys p q u v i j k) = {!!}
