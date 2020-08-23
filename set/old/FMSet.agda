{-# OPTIONS --cubical --safe #-}

module set.FMSet where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _∷_

data FMSet {ℓ} (A : Type ℓ) : Type ℓ where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  comm  : ∀ a b as bs cs
        → (p : as ≡ b ∷ cs)
        → (q : a ∷ cs ≡ bs)
        → a ∷ as ≡ b ∷ bs
  trunc : isSet (FMSet A)

pattern [_] x = x ∷ []

variable
  ℓ : Level
  A : Type ℓ

swap : (x y : A) (xs : FMSet A)
     → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
swap x y xs = comm x y (y ∷ xs) (x ∷ xs) xs refl refl
-- swap y x xs = comm y x (x ∷ xs) (y ∷ xs) xs refl refl

module FMSetElim {B : FMSet A → Type ℓ}
  ([]* : B [])
  (_∷*_ : (x : A) {xs : FMSet A} → (b : B xs) → B (x ∷ xs))
  (comm* : (a b : A) {as bs cs : FMSet A} (bas : B as) (bbs : B bs) (bcs : B cs)
         → {p : as ≡ b ∷ cs} → (bp : PathP (λ i → B (p i)) bas (b ∷* bcs))
         → {q : a ∷ cs ≡ bs} → (bq : PathP (λ i → B (q i)) (a ∷* bcs) bbs)
         → PathP (λ i → B (comm a b as bs cs p q i)) (a ∷* bas) (b ∷* bbs))
  (trunc* : (xs : FMSet A) → isSet (B xs)) where

  f : (xs : FMSet A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm a b as bs cs p q i) =
    comm* a b (f as) (f bs) (f cs) (cong f p) (cong f q) i
  f (trunc xs zs p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f xs) (f zs) (cong f p) (cong f q) (trunc xs zs p q) i j

module FMSetElimProp {B : FMSet A → Type ℓ} (BProp : {xs : FMSet A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → (p : B xs) → B (x ∷ xs)) where

  f : (xs : FMSet A) → B xs
  f = FMSetElim.f []* _∷*_
        (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq →
          toPathP (BProp (transp (λ i → B (comm a b as bs cs p q i)) i0 (a ∷* bas)) (b ∷* bbs)))
        (λ xs → isProp→isSet BProp)

module FMSetRec {B : Type ℓ} (BSet : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (a b : A) (bas bbs bcs : B)
         → (bp : bas ≡ b ∷* bcs)
         → (bq : a ∷* bcs ≡ bbs)
         → a ∷* bas ≡ b ∷* bbs) where

  f : FMSet A → B
  f = FMSetElim.f []* (λ x b → x ∷* b)
        (λ a b bas bbs bcs bp bq → comm* a b bas bbs bcs bp bq)
        (λ _ → BSet)
