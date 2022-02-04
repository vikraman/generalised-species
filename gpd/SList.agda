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

      ⬡ : (x y z : A) (xs : SList A)
        → swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)
        == ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs)

      swap² : (x y : A) (xs : SList A) → swap x y xs ∙ swap y x xs == idp

      instance trunc : has-level 1 (SList A)

    module SListElim {j} {P : SList A → Type j}
      (nil* : P nil)
      (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
      (swap* : (x y : A) {xs : SList A} (xs* : P xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ P ↓ swap x y xs ])
      (swap²* : (x y z : A) {xs : SList A} (xs* : P xs)
              → (swap* x y xs* ∙ᵈ swap* y x xs*) == idp [ (λ p → (x ::* (y ::* xs*)) == (x ::* (y ::* xs*)) [ P ↓ p ]) ↓ swap² x y xs ])
      (⬡* : (x y z : A) {xs : SList A} (xs* : P xs)
          → let p1 = swap* x y (z ::* xs*) ∙ᵈ ($ (y ::*_) (swap* x z xs*) ∙ᵈ swap* y z (x ::* xs*)) in
            let p2 = ($ (x ::*_) (swap* y z xs*) ∙ᵈ (swap* x z (y ::* xs*) ∙ᵈ $ (z ::*_) (swap* x y xs*))) in
            p1 == p2 [ (λ p → (x ::* (y ::* (z ::* xs*))) == (z ::* (y ::* (x ::* xs*))) [ P ↓ p ]) ↓ ⬡ x y z xs ])
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

    module SListElimSet {j} {P : SList A → Type j} {{trunc* : {X : SList A} → has-level 0 (P X)}}
      (nil* : P nil)
      (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
      (swap* : (x y : A) {xs : SList A} (xs* : P xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ P ↓ swap x y xs ])
      where

        f : (xs : SList A) → P xs
        f = SListElim.f {P = P} nil* (λ x p → x ::* p) swap* 
            (λ x y z xs* → set-↓-has-all-paths-↓) (λ x y z xs* → set-↓-has-all-paths-↓)
            (raise-level 0 trunc*)

    module SListRec {j} {P : Type j}
      (nil* : P)
      (_::*_ : (x : A) → P → P)
      (swap* : (x y : A) (xs* : P)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)))
      (swap²* : (x y z : A) (xs* : P)
              → (swap* x y xs* ∙ swap* y x xs*) == idp)
      (⬡* : (x y z : A) (xs* : P)
          → let p1 = swap* x y (z ::* xs*) ∙ (ap (y ::*_) (swap* x z xs*) ∙ swap* y z (x ::* xs*)) in
            let p2 = (ap (x ::*_) (swap* y z xs*) ∙ (swap* x z (y ::* xs*) ∙ ap (z ::*_) (swap* x y xs*))) in
            p1 == p2)
      (trunc* : has-level 1 P)
      where

      f : SList A → P
      f = SListElim.f {P = λ _ → P} nil* (λ x p → x ::* p) (λ x y {xs} xs* → ↓-cst-in (swap* x y xs*)) TODO TODO trunc*