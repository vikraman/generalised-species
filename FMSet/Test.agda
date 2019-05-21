{-# OPTIONS --without-K #-}

module FMSet.Test where

infixr 20 _∷_

data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : A → List A → List A

open import Agda.Builtin.Equality

private
  variable
    A : Set
    a : A
    x y z : A

pattern [_] x = x ∷ []

module _ {ℓ} (P : ∀ y → x ≡ y → Set ℓ) (d : P x refl) where
  J : (p : x ≡ y) → P y p
  J refl = d

  JRefl : J refl ≡ d
  JRefl = refl

sing-intro : ∀ (x a : A) → x ≡ a → [ x ] ≡ [ a ]
sing-intro x a p = J (λ y p → [ x ] ≡ [ y ]) refl p

head : A → List A → A
head a [] = a
head a [ x ] = x
head a (x ∷ y ∷ xs) = x

sing-elim : ∀ (x a : A) → [ x ] ≡ [ a ] → x ≡ a
sing-elim x a p = J (λ y p → x ≡ head a y) refl p

sing-elim' : ∀ (x a : A) → [ x ] ≡ [ a ] → head a [ x ] ≡ head a [ a ]
sing-elim' x a p = J (λ y p → x ≡ head a y) refl p

open import Agda.Builtin.Unit

data ⊥ : Set where

code : List A → List A → Set
code [] ys = ⊥
code (x ∷ xs) [] = ⊥
code [ x ] [ y ] = x ≡ y
code [ x ] (y ∷ y' ∷ ys) = ⊥
code (x ∷ x' ∷ xs) (y ∷ ys) = ⊥

encode : (x y : A) → x ≡ y → code [ x ] [ y ]
encode x y p = p

decode : (x y : A) → code [ x ] [ y ] → x ≡ y
decode x y p = p

f : (x y : A) → [ x ] ≡ [ y ] → x ≡ y
f x y p = {!!}
