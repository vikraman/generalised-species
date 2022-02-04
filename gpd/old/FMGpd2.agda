{-# OPTIONS --cubical --allow-unsolved-metas #-}

module gpd.FMGpd2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _∷_

data FMGpd {ℓ} (A : Type ℓ) : Type ℓ where
  []    : FMGpd A
  _∷_   : (x : A) → (xs : FMGpd A) → FMGpd A
  swap  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  hexagon– : ∀ x y z xs → x ∷ y ∷ z ∷ xs ≡ z ∷ y ∷ x ∷ xs
  hexagon↑ : ∀ x y z xs → Square (λ i → y ∷ swap x z xs i) (hexagon– x y z xs)
                                 (swap y x (z ∷ xs)) (swap y z (x ∷ xs))
  hexagon↓ : ∀ x y z xs → Square (hexagon– x y z xs) (swap x z (y ∷ xs))
                                 (λ i → x ∷ swap y z xs i) (λ i → z ∷ swap y x xs i)
  swap2 : ∀ x y xs → sym (swap x y xs) ≡ swap y x xs
  trunc : isGroupoid (FMGpd A)

variable
  ℓ : Level
  A : Type ℓ

-- hexagon : (x y z : A) (xs : FMGpd A)
--         → swap x y (z ∷ xs) ∙ (λ i → y ∷ swap x z xs i) ∙ swap y z (x ∷ xs)
--         ≡ (λ i → x ∷ swap y z xs i) ∙ swap x z (y ∷ xs) ∙ (λ i → z ∷ swap x y xs i)

pattern [_] x = x ∷ []

-- module FMGpdElim {B : FMGpd A → Type ℓ}
--   ([]* : B [])
--   (_∷*_ : (x : A) {xs : FMGpd A} → (b : B xs) → B (x ∷ xs))
--   (swap* : (x y : A) {xs : FMGpd A} (b : B xs)
--          → PathP (λ i → B (swap x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
--   (swap2* : (x y : A) {xs : FMGpd A} (b : B xs)
--           → PathP (λ i → PathP (λ j → B (swap2 x y xs i j)) (y ∷* (x ∷* b)) (x ∷* (y ∷* b)))
--                   (symP (swap* x y b)) (swap* y x b))
--   (trunc* : (xs : FMGpd A) → isGroupoid (B xs)) where

--   -- f : (xs : FMGpd A) → B xs
--   -- f [] = []*
--   -- f (x ∷ xs) = x ∷* f xs
--   -- f (swap x y xs i) = swap* x y (f xs) i
--   -- f (hexagon x y z xs i j) = {!!} -- hexagon* x y z (f xs) i j
--   -- f (swap2 x y xs i j) = swap2* x y (f xs) i j
--   -- f (trunc xs zs p q u v i j k) =
--   --   isOfHLevel→isOfHLevelDep 3 trunc* (f xs) (f zs) (cong f p) (cong f q)
--   --     (cong (cong f) u) (cong (cong f) v) (trunc xs zs p q u v) i j k

-- isSet→isGroupoid : isSet A → isGroupoid A
-- isSet→isGroupoid = hLevelSuc 2 _

-- module FMGpdElimSet {B : FMGpd A → Type ℓ} (BSet : {xs : FMGpd A} → isSet (B xs))
--   ([]* : B [])
--   (_∷*_ : (x : A) {xs : FMGpd A} → (b : B xs) → B (x ∷ xs))
--   (swap* : (x y : A) {xs : FMGpd A} (b : B xs)
--          → PathP (λ i → B (swap x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b))) where

--   f : (xs : FMGpd A) → B xs
--   f [] = []*
--   f (x ∷ xs) = x ∷* f xs
--   f (swap x y xs i) = swap* x y (f xs) i
--   f (hexagon x y z xs i j) = {!!}
--   f (swap2 x y xs i j) = {!!}
--   f (trunc xs xs₁ x y x₁ y₁ i i₁ i₂) = {!!}

--   -- f = FMGpdElim.f []* _∷*_ swap*
--   --   {!!} {!!}
--   --   (λ xs → isSet→isGroupoid BSet)

-- -- module FMGpdElimProp {ℓ} {A : Type ℓ} {B : FMGpd A → Type ℓ} (BProp : {xs : FMGpd A} → isProp (B xs))
-- --   ([]* : B []) (_∷*_ : (x : A) {xs : FMGpd A} → B xs → B (x ∷ xs)) where

-- --   f : (xs : FMGpd A) → B xs
-- --   f = FMGpdElimSet.f (isProp→isSet BProp) []* _∷*_
-- --     (λ x y {xs} b → toPathP (BProp (transp (λ i → B (swap x y xs i)) i0 (x ∷* (y ∷* b))) (y ∷* (x ∷* b))))

-- -- ∀ x y z xs → swap x y (z ∷ xs) ∙ ((λ i → y ∷ swap x z xs i) ∙ swap y z (x ∷ xs))
-- --            ≡ (λ i → x ∷ swap y z xs i) ∙ swap x z (y ∷ xs) ∙ (λ i → z ∷ swap x y xs i)

-- -- swap2 : ∀ x y xs → sym (swap x y xs) ≡ swap y x xs

-- module FMGpdRec {B : Type ℓ} (BGpd : isGroupoid B)
--   ([]* : B) (_∷*_ : A → B → B)
--   (swap* : (x y : A) (b : B) → (x ∷* (y ∷* b)) ≡ (y ∷* (x ∷* b)))
--   (hexagon* : (x y z : A) (b : B) → swap* x y (z ∷* b) ∙ (λ i → y ∷* swap* x z b i) ∙ swap* y z (x ∷* b)
--                                   ≡ (λ i → x ∷* swap* y z b i) ∙ swap* x z (y ∷* b) ∙ (λ i → z ∷* swap* x y b i))
--   (swap2* : (x y : A) (b : B) → sym (swap* x y b) ≡ swap* y x b) where

--   f : FMGpd A → B
--   f [] = []*
--   f (x ∷ xs) = x ∷* f xs
--   f (swap x y xs i) = swap* x y (f xs) i
--   f (hexagon x y z xs i j) = hexagon* x y z (f xs) i j
--   f (swap2 x y xs i j) = {!!}
--   f (trunc xs xs₁ x y x₁ y₁ i i₁ i₂) = {!!}
