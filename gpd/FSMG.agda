{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import UF-Univalence

module gpd.FSMG (ua : Univalence) where

open import UF-hlevels ua

PathOver : {A : 𝓤 ̇} (P : A → 𝓤 ̇) {x y : A} → (p : x ≡ y) → P x → P y → 𝓤 ̇
PathOver P p u v = transport P p u ≡ v

↓-cst-in : {A : 𝓤 ̇} {x y : A} (p : x ≡ y) → x ≡ y [ (λ _ → A) ↓ p ]
↓-cst-in refl = refl

syntax PathOver P p u v = u ≡ v [ P ↓ p ]

■ : {A : 𝓤 ̇} {P : A → 𝓤 ̇ }
  → {x y z : A} {u : P x} {v : P y} {w : P z}
  → (p : x ≡ y) (q : y ≡ z)
  → u ≡ v [ P ↓ p ] → v ≡ w [ P ↓ q ] → u ≡ w [ P ↓ (p ∙ q) ]
■ refl refl = _∙_

$ : {A : 𝓤 ̇} {P : A → 𝓤 ̇}
  → {x y : A} {u : P x} {v : P y}
  → (f : A → A) (g : {x : A} → P x → P (f x))
  → (p : x ≡ y)
  → u ≡ v [ P ↓ p ] → g u ≡ g v [ P ↓ ap f p ]
$ f g refl = ap g

data FSMG (A : 𝓤 ̇) : 𝓤 ̇ where
  nil : FSMG A
  _::_ : (x : A) (xs : FSMG A) → FSMG A

infixr 50 _::_

postulate
  swap : {A : 𝓤 ̇} (x y : A) (xs : FSMG A)
       → x :: y :: xs ≡ y :: x :: xs

  swap2 : {A : 𝓤 ̇} (x y : A) (xs : FSMG A)
        → swap x y xs ∙ swap y x xs ≡ refl

  hexagon : {A : 𝓤 ̇} (x y z : A) (xs : FSMG A)
          → swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)
          ≡ ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs)

  trunc : {A : 𝓤 ̇} → FSMG A is-of-hlevel 2

module elim {A : 𝓤 ̇} {B : FSMG A → 𝓤 ̇}
  (nil* : B nil)
  (_::*_ : (x : A) {xs : FSMG A} → (b : B xs) → B (x :: xs))
  (swap* : (x y : A) {xs : FSMG A} (b : B xs)
         → (x ::* (y ::* b)) ≡ (y ::* (x ::* b)) [ B ↓ swap x y xs ])
  (swap2* : (x y : A) {xs : FSMG A} (b : B xs)
          → (■ (swap x y xs) (swap y x xs) (swap* x y b) (swap* y x b))
          ≡ ap (λ p → transport B p (x ::* (y ::* b))) (swap2 x y xs))
  (hexagon* : (x y z : A) {xs : FSMG A} (b : B xs)
            → ■ _ (swap y z (x :: xs))
                (■ _ (ap (y ::_) (swap x z xs))
                   (swap* x y (z ::* b))
                   ($ (y ::_) (y ::*_) (swap x z xs) (swap* x z b)))
                (swap* y z (x ::* b))
            ≡ ap (λ p → transport B p (x ::* (y ::* (z ::* b)))) (hexagon x y z xs)
            ∙ ■ _ (ap (z ::_) (swap x y xs))
                (■ _ (swap x z (y :: xs))
                   ($ (x ::_) (x ::*_) (swap y z xs) (swap* y z b))
                   (swap* x z (y ::* b)))
                ($ (z ::_) (z ::*_) (swap x y xs) (swap* x y b)))
  (trunc* : {xs : FSMG A} → B xs is-of-hlevel 2)
  where

  postulate
    f : (xs : FSMG A) → B xs

module rec {A B : 𝓤 ̇}
  (nil* : B)
  (_::*_ : A → B → B)
  (swap* : (x y : A) (b : B)
         → (x ::* (y ::* b)) ≡ (y ::* (x ::* b)))
  (swap2* : (x y : A) (b : B)
          → (swap* x y b) ∙ (swap* y x b) ≡ refl)
  (hexagon* : (x y z : A) (b : B)
            → swap* x y (z ::* b) ∙ ap (y ::*_) (swap* x z b) ∙ swap* y z (x ::* b)
            ≡ ap (x ::*_) (swap* y z b) ∙ swap* x z (y ::* b) ∙ ap (z ::*_) (swap* x y b))
  (trunc* : B is-of-hlevel 2)
  where

    f : FSMG A → B
    f = elim.f {B = λ _ → B} nil* (λ x b → b) (λ x y b → {!!}) {!!} {!!} trunc*
