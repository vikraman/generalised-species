{-# OPTIONS --cubical --safe #-}

module set.old.FMSet2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _∷_

data FMSet (A : Type₀) : Type₀ where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  swap  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (FMSet A)

pattern [_] x = x ∷ []

private
  variable
    ℓ : Level
    A : Type₀

module FMSetElim {B : FMSet A → Type ℓ}
  ([]* : B [])
  (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs))
  (swap* : (x y : A) {xs : FMSet A} (b : B xs)
         → PathP (λ i → B (swap x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (trunc* : (xs : FMSet A) → isSet (B xs)) where

  f : (xs : FMSet A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (swap x y xs i) = swap* x y (f xs) i
  f (trunc xs zs p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f xs) (f zs) (cong f p) (cong f q) (trunc xs zs p q) i j

module FMSetElimProp {B : FMSet A → Type ℓ} (BProp : {xs : FMSet A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs)) where

  f : (xs : FMSet A) → B xs
  f = FMSetElim.f []* _∷*_
        (λ x y {xs} b →
          toPathP (BProp (transp (λ i → B (swap x y xs i)) i0 (x ∷* (y ∷* b))) (y ∷* (x ∷* b))))
        (λ xs → isProp→isSet BProp)

module FMSetRec {B : Type ℓ} (BSet : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (swap* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)) where

  f : FMSet A → B
  f = FMSetElim.f []* (λ x b → x ∷* b) (λ x y b → swap* x y b) (λ _ → BSet)
