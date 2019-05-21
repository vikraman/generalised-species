{-# OPTIONS --cubical --safe #-}

module FMSet.Product where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Prod

open import FMSet
open import FMSet.Properties

private
  variable
    A B : Type₀

FMSet×-isSet : isSet (FMSet A ×Σ FMSet B)
FMSet×-isSet = isOfHLevelΣ 2 trunc (λ _ → trunc)

map : (A → B) → FMSet A → FMSet B
map f = FMSetRec.f trunc [] (λ a bs → f a ∷ bs) (λ x y bs → comm (f x) (f y) bs)

map-++ : (f : A → B) (xs ys : FMSet A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f = FMSetElimProp.f (λ {xs} → propPi (λ ys → trunc (map f (xs ++ ys)) (map f xs ++ map f ys)))
  (λ ys → refl)
  (λ x {xs} p ys → cong (f x ∷_) (p ys))

f : FMSet (A ⊎ B) → FMSet A ×Σ FMSet B
f = FMSetUniversal.f♯
    (record
       { e = [] , []
       ; _⊗_ = λ { (xs , ys) (zs , ws) → (xs ++ zs , ys ++ ws)}
       ; comm-⊗ = λ { (xs , ys) (zs , ws) i → comm-++ xs zs i , comm-++ ys ws i }
       ; assoc-⊗ = λ { (xs , ys) (zs , ws) (us , vs) i → assoc-++ xs zs us i , assoc-++ ys ws vs i }
       ; unit-⊗ = λ { (xs , ys) → refl}
       ; MSet = FMSet×-isSet
       })
    (λ { (inl a) → [ a ] , [] ; (inr b) → [] , [ b ] })

g : FMSet A ×Σ FMSet B → FMSet (A ⊎ B)
g (as , bs) = map inl as ++ map inr bs

f-g : ∀ (as : FMSet A) (bs : FMSet B) → f (g (as , bs)) ≡ (as , bs)
f-g = {!!}

g-f : ∀ (xs : FMSet (A ⊎ B)) → g (f xs) ≡ xs
g-f = {!!}
