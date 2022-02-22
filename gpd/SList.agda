{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module gpd.SList where

open import gpd.Prelude

module _ {i} where
  postulate
    SList : (A : Type i) → Type i

  module _ {A : Type i} where
    infixr 40 _::_
    postulate
      nil : SList A
      _::_ : A → SList A → SList A

      swap : (x y : A) (xs : SList A) → x :: y :: xs == y :: x :: xs

      swap² : (x y : A) (xs : SList A) → swap x y xs ∙ swap y x xs == idp

      ⬡ : (x y z : A) (xs : SList A)
        → swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)
        == ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs)

      instance trunc : has-level 1 (SList A)

    -- pattern [_] x = x :: nil
    [_] : A → SList A
    [ x ] = x :: nil

    module SListElim {j} {P : SList A → Type j}
      (nil* : P nil)
      (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
      (swap* : (x y : A) {xs : SList A} (xs* : P xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ P ↓ swap x y xs ])
      (swap²* : (x y z : A) {xs : SList A} (xs* : P xs)
              → (swap* x y xs* ∙ᵈ swap* y x xs*) == idp [ (λ p → (x ::* (y ::* xs*)) == (x ::* (y ::* xs*)) [ P ↓ p ]) ↓ swap² x y xs ])
      (⬡* : (x y z : A) {xs : SList A} (xs* : P xs)
          → let p1 = swap* x y (z ::* xs*) ∙ᵈ ($ (y ::*_) (swap* x z xs*) ∙ᵈ swap* y z (x ::* xs*))
                p2 = $ (x ::*_) (swap* y z xs*) ∙ᵈ (swap* x z (y ::* xs*) ∙ᵈ $ (z ::*_) (swap* x y xs*))
             in p1 == p2 [ (λ p → (x ::* (y ::* (z ::* xs*))) == (z ::* (y ::* (x ::* xs*))) [ P ↓ p ]) ↓ ⬡ x y z xs ])
      (trunc* : {xs : SList A} → has-level 1 (P xs))
      where

      postulate
        f : (xs : SList A) → P xs
        f-nil-β : f nil ↦ nil*
        {-# REWRITE f-nil-β #-}
        f-::-β : {x : A} {xs : SList A} → f (x :: xs) ↦ (x ::* f xs)
        {-# REWRITE f-::-β #-}

      postulate
        f-swap-β : {x y : A} {xs : SList A} → apd f (swap x y xs) == swap* x y (f xs)

    module SListElimSet {j} {P : SList A → Type j} ⦃ trunc* : {X : SList A} → has-level 0 (P X) ⦄
      (nil* : P nil)
      (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
      (swap* : (x y : A) {xs : SList A} (xs* : P xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ P ↓ swap x y xs ])
      where

        private module F = SListElim {P = P} nil* (λ x p → x ::* p) swap*
                                     (λ x y z xs* → set-↓-has-all-paths-↓)
                                     (λ x y z xs* → set-↓-has-all-paths-↓)
                                     (raise-level 0 trunc*)

        f : (xs : SList A) → P xs
        f = F.f

        f-swap-β : {x y : A} {xs : SList A} → apd f (swap x y xs) == swap* x y (f xs)
        f-swap-β = F.f-swap-β

    module SListElimProp {j} {P : SList A → Type j} ⦃ trunc* : {X : SList A} → has-level -1 (P X) ⦄
      (nil* : P nil)
      (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
      where

        f : (xs : SList A) → P xs
        f = SListElimSet.f {P = P} ⦃ raise-level -1 trunc* ⦄ nil* _::*_ (λ x y xs* → prop-has-all-paths-↓)

    module SListRec {j} {P : Type j}
      (nil* : P)
      (_::*_ : (x : A) → P → P)
      (swap* : (x y : A) (xs* : P)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)))
      (swap²* : (x y z : A) (xs* : P)
              → (swap* x y xs* ∙ swap* y x xs*) == idp)
      (⬡* : (x y z : A) (xs* : P)
          → let p1 = swap* x y (z ::* xs*) ∙ (ap (y ::*_) (swap* x z xs*) ∙ swap* y z (x ::* xs*))
                p2 = (ap (x ::*_) (swap* y z xs*) ∙ (swap* x z (y ::* xs*) ∙ ap (z ::*_) (swap* x y xs*)))
             in p1 == p2)
      (trunc* : has-level 1 P)
      where

      module Elim =
        SListElim {P = λ _ → P}
          nil*
          (λ x p → x ::* p)
          (λ x y {xs} xs* → ↓-cst-in (swap* x y xs*))
          (λ x y z {xs} xs* → ↓-cst-in-∙ (swap x y xs) (swap y x xs) (swap* x y xs*) (swap* y x xs*)
                            !◃ ↓-cst-in2 (swap²* x y z xs*))
          (λ x y z {xs} xs* → TODO
                            -- !◃ ↓-cst-in2 (⬡* x y z xs*)
                            )
          trunc*

      f : SList A → P
      f = Elim.f

      f-swap-β : {x y : A} {xs : SList A} → ap f (swap x y xs) == swap* x y (f xs)
      f-swap-β = apd=cst-in Elim.f-swap-β

    module SListElimPaths {j} {P : SList A → Type j} ⦃ trunc* : {X : SList A} → has-level 1 (P X) ⦄
      (f g : (xs : SList A) → P xs)
      (nil* : f nil == g nil)
      (_::*_ : (x : A) {xs : SList A} → f xs == g xs → f (x :: xs) == g (x :: xs))
      (swap* : (x y : A) {xs : SList A} (xs* : f xs == g xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ (λ z → f z == g z) ↓ swap x y xs ])
      where

      private module F = SListElimSet nil* _::*_ swap*

      elim : (xs : SList A) → f xs == g xs
      elim = F.f

      elim-swap-β : {x y : A} {xs : SList A} → apd elim (swap x y xs) == swap* x y (elim xs)
      elim-swap-β = F.f-swap-β

    module SListElimPathsSet {j} {P : SList A → Type j} ⦃ trunc* : {X : SList A} → has-level 0 (P X) ⦄
      (f g : (xs : SList A) → P xs)
      (nil* : f nil == g nil)
      (_::*_ : (x : A) {xs : SList A} → f xs == g xs → f (x :: xs) == g (x :: xs))
      where

      elim : (xs : SList A) → f xs == g xs
      elim = SListElimProp.f nil* _::*_

    module SListRecPaths {j} {P : Type j} ⦃ trunc* : has-level 1 P ⦄
      (f g : SList A → P)
      (nil* : f nil == g nil)
      (_::*_ : (x : A) {xs : SList A} (p : f xs == g xs)
             → f (x :: xs) == g (x :: xs))
      (swap* : (x y : A) {xs : SList A} (xs* : f xs == g xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ (λ z → f z == g z) ↓ swap x y xs ])
      where

      rec : (xs : SList A) → f xs == g xs
      rec = SListElimPaths.elim f g nil* _::*_ swap*

    module SListRecPathsSet {j} {P : Type j} ⦃ trunc* : has-level 0 P ⦄
      (f g : SList A → P)
      (nil* : f nil == g nil)
      (_::*_ : (x : A) {xs : SList A} (p : f xs == g xs) → f (x :: xs) == g (x :: xs))
      where

      rec : (xs : SList A) → f xs == g xs
      rec = SListElimPathsSet.elim f g nil* _::*_
