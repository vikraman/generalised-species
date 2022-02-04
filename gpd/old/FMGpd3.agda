{-# OPTIONS --without-K --rewriting #-}

module gpd.FMGpd3 where

open import HoTT

module FMGpd where

  FMGpd : ∀ {i} → Type i → Type i
  FMGpd A = List A

  postulate
    swap : ∀ {i} {A : Type i} (x y : A) (xs : FMGpd A)
         → _==_ {i} {List A} (x :: (y :: xs)) (y :: (x :: xs))
    trunc : ∀ {i} {A : Type i} → has-level 1 (FMGpd A)

  module FMGpdElim {i} {A : Type i} {B : FMGpd A → Type i}
    (nil* : B nil)
    (_::*_ : (x : A) {xs : FMGpd A} → (b : B xs) → B (x :: xs))
    (swap* : (x y : A) {xs : FMGpd A} (b : B xs)
           → (x ::* (y ::* b)) == (y ::* (x ::* b)) [ B ↓ swap x y xs ])
    -- (swap2* : (x y : A) {xs : FMGpd A} (b : B xs)
    --         → PathP (λ i → PathP (λ j → B (swap2 x y xs i j)) (y ::* (x ::* b)) (x ::* (y ::* b)))
    --                 (symP (swap* x y b)) (swap* y x b))
    (trunc* : {xs : FMGpd A} → has-level 1 (B xs)) where

      f : (xs : FMGpd A) → B xs
      f nil = nil*
      f (x :: xs) = x ::* f xs

      postulate
        f-swap-β : (x y : A) (xs : FMGpd A) → apd f (swap x y xs) ↦ swap* x y (f xs)
        {-# REWRITE f-swap-β #-}

open FMGpd

module FMGpdElimSet {i} {A : Type i} {B : FMGpd A → Type i} (BSet : {xs : FMGpd A} → is-set (B xs))
  (nil* : B nil)
  (_::*_ : (x : A) {xs : FMGpd A} → (b : B xs) → B (x :: xs))
  (swap* : (x y : A) {xs : FMGpd A} (b : B xs)
         → (x ::* (y ::* b)) == (y ::* (x ::* b)) [ B ↓ swap x y xs ]) where

  f : (xs : FMGpd A) → B xs
  f = FMGpdElim.f nil* _::*_ swap* (raise-level 0 BSet)

module FMGpdElimProp {i} {A : Type i} {B : FMGpd A → Type i} (BProp : {xs : FMGpd A} → is-prop (B xs))
  (nil* : B nil) (_::*_ : (x : A) {xs : FMGpd A} → B xs → B (x :: xs)) where

  f : (xs : FMGpd A) → B xs
  f = FMGpdElimSet.f (raise-level -1 BProp) nil* _::*_ λ _ _ _ → prop-has-all-paths-↓
    where instance _ = BProp

module FMGpdRec {i} {A B : Type i} (BGpd : has-level 1 B)
  (nil* : B) (_::*_ : A → B → B)
  (swap* : (x y : A) (b : B)
         → (x ::* (y ::* b)) == (y ::* (x ::* b))) where

  f : FMGpd A → B
  f = FMGpdElim.f nil* (λ x b → x ::* b) (λ x y b → ↓-cst-in (swap* x y b)) BGpd
