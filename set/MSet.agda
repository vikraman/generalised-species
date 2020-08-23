{-# OPTIONS --cubical --exact-split --safe #-}

module set.MSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _::_

data MSet {ℓ} (A : Type ℓ) : Type ℓ where
  [] : MSet A
  _::_ : (x : A) (xs : MSet A) → MSet A
  swap : (x y : A) (xs : MSet A)
       → x :: y :: xs ≡ y :: x :: xs
  trunc : isSet (MSet A)

pattern [_] x = x :: []

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

module elim {A : Type ℓ₁} {B : MSet A → Type ℓ₂}
  ([]* : B [])
  (_::*_ : (x : A) {xs : MSet A} → B xs → B (x :: xs))
  (swap* : (x y : A) {xs : MSet A} (b : B xs)
         → PathP (λ i → B (swap x y xs i)) (x ::* (y ::* b)) (y ::* (x ::* b)))
  (trunc* : (xs : MSet A) → isSet (B xs)) where

  f : (xs : MSet A) → B xs
  f [] = []*
  f (x :: xs) = x ::* f xs
  f (swap x y xs i) = swap* x y (f xs) i
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module elimProp {A : Type ℓ₁} {B : MSet A → Type ℓ₂} (BProp : {xs : MSet A} → isProp (B xs))
  ([]* : B [])
  (_::*_ : (x : A) {xs : MSet A} → B xs → B (x :: xs)) where

  f : (xs : MSet A) → B xs
  f = elim.f []* _::*_
             (λ x y {xs} b → toPathP (BProp (transp (λ i → B (swap x y xs i)) i0 (x ::* (y ::* b))) (y ::* (x ::* b))))
             (λ _ → isProp→isSet BProp)

module rec {A : Type ℓ₁} {B : Type ℓ₂}
  ([]* : B)
  (_::*_ : A → B → B)
  (swap* : (x y : A) (b : B)
         → x ::* (y ::* b) ≡ y ::* (x ::* b))
  (trunc* : isSet B) where

  f : MSet A → B
  f = elim.f []* (λ x b → x ::* b)
             (λ x y b → swap* x y b)
             (λ _ → trunc*)

module recProp {A : Type ℓ₁} {B : Type ℓ₂} (BProp : isProp B)
  ([]* : B)
  (_::*_ : A → B → B) where

  f : MSet A → B
  f = elimProp.f BProp []* (λ x b → x ::* b)
