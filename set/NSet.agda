{-# OPTIONS --cubical --exact-split --safe #-}

module set.NSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _::_

data NSet {ℓ} (A : Type ℓ) : Type ℓ where
  [] : NSet A
  _::_ : (x : A) (xs : NSet A) → NSet A
  comm : {a b : A} {as bs cs : NSet A}
       → (p : as ≡ b :: cs)
       → (q : a :: cs ≡ bs)
       → a :: as ≡ b :: bs
  trunc : isSet (NSet A)

pattern [_] x = x :: []

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

module elim {A : Type ℓ₁} {B : NSet A → Type ℓ₂}
  ([]* : B [])
  (_::*_ : (x : A) {xs : NSet A} → B xs → B (x :: xs))
  (comm* : {a b : A} {as bs cs : NSet A} {bas : B as} {bbs : B bs} {bcs : B cs}
         → {p : as ≡ b :: cs} (bp : PathP (λ i → B (p i)) bas (b ::* bcs))
         → {q : a :: cs ≡ bs} (bq : PathP (λ i → B (q i)) (a ::* bcs) bbs)
         → PathP (λ i → B (comm p q i)) (a ::* bas) (b ::* bbs))
  (trunc* : (xs : NSet A) → isSet (B xs)) where

  f : (xs : NSet A) → B xs
  f [] = []*
  f (x :: xs) = x ::* f xs
  f (comm p q i) = comm* (cong f p) (cong f q) i
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f xs) (f ys) (cong f p) (cong f q) (trunc xs ys p q) i j

module elimProp {A : Type ℓ₁} {B : NSet A → Type ℓ₂} (BProp : {xs : NSet A} → isProp (B xs))
  ([]* : B [])
  (_::*_ : (x : A) {xs : NSet A} → B xs → B (x :: xs)) where

  f : (xs : NSet A) → B xs
  f = elim.f []* _::*_
             (λ {a b as bs cs bas bbs bcs p} bp {q} bq →
               toPathP (BProp (transp (λ i → B (comm p q i)) i0 (a ::* bas)) (b ::* bbs)))
             (λ _ → isProp→isSet BProp)

module rec {A : Type ℓ₁} {B : Type ℓ₂}
  ([]* : B)
  (_::*_ : A → B → B)
  (comm* : {a b : A} {bas bbs bcs : B}
         → (bp : bas ≡ b ::* bcs)
         → (bq : a ::* bcs ≡ bbs)
         → a ::* bas ≡ b ::* bbs)
  (trunc* : isSet B) where

  f : NSet A → B
  f = elim.f []* (λ x b → x ::* b)
             (λ bp bq i → comm* bp bq i)
             (λ _ → trunc*)

module recProp {A : Type ℓ₁} {B : Type ℓ₂} (BProp : isProp B)
  ([]* : B)
  (_::*_ : A → B → B) where

  f : NSet A → B
  f = elimProp.f BProp []* (λ x b → x ::* b)
