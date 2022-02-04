{-# OPTIONS --cubical #-}

module gpd.FMGpd2.Universal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import gpd.FMGpd2

infixr 30 _⊗_

_⊗_ : ∀ (xs ys : FMGpd A) → FMGpd A
[] ⊗ ys = ys
(x ∷ xs) ⊗ ys = x ∷ xs ⊗ ys
swap x y xs i ⊗ ys =
  swap x y (xs ⊗ ys) i
hexagon x y z xs p i ⊗ ys =
  hexagon x y z (xs ⊗ ys) p i
swap2 x y xs i j ⊗ ys =
  swap2 x y (xs ⊗ ys) i j
trunc xs zs p q u v i j k ⊗ ys =
  trunc (xs ⊗ ys) (zs ⊗ ys) (cong (_⊗ ys) p)
    (cong (_⊗ ys) q) (cong (cong (_⊗ ys)) u) (cong (cong (_⊗ ys)) v) i j k

unitl-⊗ : ∀ (xs : FMGpd A) → [] ⊗ xs ≡ xs
unitl-⊗ xs = refl

unitr-⊗ : ∀ (xs : FMGpd A) → xs ⊗ [] ≡ xs
unitr-⊗ = FMGpdElimSet.f (trunc _ _)
  refl
  (λ x p → cong (x ∷_) p)
  (λ x y p i j → swap x y (p j) i)

assoc-⊗ : ∀ (xs ys zs : FMGpd A) → xs ⊗ (ys ⊗ zs) ≡ (xs ⊗ ys) ⊗ zs
assoc-⊗ = FMGpdElimSet.f (isSetPi (λ _ → isSetPi (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (x ∷_) (p ys zs))
  (λ x y p i ys zs j → swap x y (p ys zs j) i)

lemma1 : (x y z : A) (xs : FMGpd A) → y ∷ x ∷ z ∷ xs ≡ z ∷ x ∷ y ∷ xs
lemma1 x y z xs = swap y x (z ∷ xs) ∙ cong (x ∷_) (swap y z xs) ∙ swap x z (y ∷ xs)

lemma2 : (x y z : A) (xs : FMGpd A) → x ∷ y ∷ z ∷ xs ≡ y ∷ z ∷ x ∷ xs
lemma2 x y z xs = swap x y (z ∷ xs) ∙ cong (y ∷_) (swap x z xs)

lemma0 : (x y : A) (xs : FMGpd A) (p : x ∷ xs ≡ xs ⊗ [ x ]) → x ∷ y ∷ xs ≡ y ∷ (xs ⊗ [ x ])
lemma0 x y xs p i = hcomp (λ j → λ { (i = i0) → x ∷ y ∷ xs ; (i = i1) → y ∷ p j }) (swap x y xs i)

sq : (x y z : A) (xs : FMGpd A) → PathP (λ i → swap x y (z ∷ xs) i ≡ swap x z (y ∷ xs) i)
                                        (cong (x ∷_) (swap y z xs)) (lemma1 x y z xs)
sq x y z xs = {!!}

cons-⊗ : ∀ (x : A) (xs : FMGpd A) → x ∷ xs ≡ xs ⊗ [ x ]
cons-⊗ x = FMGpdElimSet.f (trunc _ _)
  refl
  (λ y {xs} p → lemma0 x y xs p)
  (λ y z {xs} p i j →
    hcomp (λ k → λ { (i = i0) → hfill (λ l → λ { (j = i0) → x ∷ y ∷ z ∷ xs
                                               ; (j = i1) → y ∷ lemma0 x z xs p l })
                                      (inS (swap x y (z ∷ xs) j)) k
                   ; (i = i1) → hfill (λ l → λ { (j = i0) → x ∷ z ∷ y ∷ xs
                                               ; (j = i1) → z ∷ lemma0 x y xs p l })
                                      (inS (swap x z (y ∷ xs) j)) k
                   ; (j = i0) → x ∷ swap y z xs i
                   ; (j = i1) → {!!}
                                -- hcomp (λ l → λ { (i = i0) → {!!}
                                --                ; (i = i1) → {!!} })
                                --       (swap y z (xs ⊗ [ x ]) i)
                                      })
          (sq x y z xs j i)
  )
