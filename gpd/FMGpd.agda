{-# OPTIONS --cubical --safe #-}

module gpd.FMGpd where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infixr 20 _∷_

data FMGpd {ℓ} (A : Type ℓ) : Type ℓ where
  []    : FMGpd A
  _∷_   : (x : A) → (xs : FMGpd A) → FMGpd A
  comm  : ∀ a b as bs cs
        → (p : as ≡ b ∷ cs)
        → (q : a ∷ cs ≡ bs)
        → a ∷ as ≡ b ∷ bs
  -- comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  -- comm2 : ∀ x y xs → comm x y xs ≡ sym (comm y x xs)
  trunc : isGroupoid (FMGpd A)

pattern [_] x = x ∷ []

variable
  ℓ : Level
  A : Type ℓ

swap : (x y : A) (xs : FMGpd A)
     → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
swap x y xs = comm x y (y ∷ xs) (x ∷ xs) xs refl refl
-- swap y x xs = comm y x (x ∷ xs) (y ∷ xs) xs refl refl

module FMGpdElim {B : FMGpd A → Type ℓ}
  ([]* : B [])
  (_∷*_ : (x : A) {xs : FMGpd A} → (b : B xs) → B (x ∷ xs))
  (comm* : (a b : A) {as bs cs : FMGpd A} (bas : B as) (bbs : B bs) (bcs : B cs)
         → {p : as ≡ b ∷ cs} → (bp : PathP (λ i → B (p i)) bas (b ∷* bcs))
         → {q : a ∷ cs ≡ bs} → (bq : PathP (λ i → B (q i)) (a ∷* bcs) bbs)
         → PathP (λ i → B (comm a b as bs cs p q i)) (a ∷* bas) (b ∷* bbs))
  (trunc* : (xs : FMGpd A) → isGroupoid (B xs)) where

  f : (xs : FMGpd A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm a b as bs cs p q i) =
    comm* a b (f as) (f bs) (f cs) (cong f p) (cong f q) i
  f (trunc xs zs p q u v i j k) =
    isOfHLevel→isOfHLevelDep 3 trunc* (f xs) (f zs) (cong f p) (cong f q)
      (cong (cong f) u) (cong (cong f) v) (trunc xs zs p q u v) i j k

-- isSet→isGroupoid : isSet A → isGroupoid A
-- isSet→isGroupoid = hLevelSuc 2 _

module FMGpdElimSet {B : FMGpd A → Type ℓ} (BSet : (xs : FMGpd A) → isSet (B xs))
  ([]* : B [])
  (_∷*_ : (x : A) {xs : FMGpd A} → (b : B xs) → B (x ∷ xs))
  (comm* : (a b : A) {as bs cs : FMGpd A} (bas : B as) (bbs : B bs) (bcs : B cs)
         → {p : as ≡ b ∷ cs} → (bp : PathP (λ i → B (p i)) bas (b ∷* bcs))
         → {q : a ∷ cs ≡ bs} → (bq : PathP (λ i → B (q i)) (a ∷* bcs) bbs)
         → PathP (λ i → B (comm a b as bs cs p q i)) (a ∷* bas) (b ∷* bbs)) where

  f : (xs : FMGpd A) → B xs
  f = FMGpdElim.f []* _∷*_ comm* (λ xs → isSet→isGroupoid (BSet xs))

module FMGpdElimProp {ℓ} {A : Type ℓ} {B : FMGpd A → Type ℓ} (BProp : {xs : FMGpd A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMGpd A} → B xs → B (x ∷ xs)) where

  f : (xs : FMGpd A) → B xs
  f = FMGpdElimSet.f (λ xs → isProp→isSet BProp) []* _∷*_
    (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq →
      toPathP (BProp (transp (λ i → B (comm a b as bs cs p q i)) i0 (a ∷* bas)) (b ∷* bbs)))


module FMGpdRec {B : Type ℓ} (BGpd : isGroupoid B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (a b : A) (bas bbs bcs : B)
         → (bp : bas ≡ b ∷* bcs)
         → (bq : a ∷* bcs ≡ bbs)
         → a ∷* bas ≡ b ∷* bbs) where

  f : FMGpd A → B
  f = FMGpdElim.f []* (λ x b → x ∷* b)
        (λ a b bas bbs bcs bp bq → comm* a b bas bbs bcs bp bq)
        (λ _ → BGpd)
