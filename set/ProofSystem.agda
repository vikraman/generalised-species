{-# OPTIONS --cubical --exact-split --safe #-}

module set.ProofSystem where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List
open import Cubical.Data.Empty as E
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod

open import set.NSet

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

infix 10 _≈_

-- defining the relation on NSet?
-- we can only eliminate to hProp, since hSet is a groupoid

-- _≈_ : NSet A → NSet A → Type _
-- xs ≈ ys = {!!}

-- this won't compute in cubical

-- data _≈_ {ℓ} {A : Type ℓ} : NSet A → NSet A → Type ℓ where
--   nil-refl : [] ≈ []
--   cons-cong : ∀ a as bs
--             → (as ≈ bs)
--             → (a :: as) ≈ (a :: bs)
--   comm-rel : ∀ a b as bs cs
--            → (as ≈ b :: cs) → (a :: cs ≈ bs)
--            → (a :: as) ≈ (b :: bs)

-- defining on lists

-- _≈_ : List A → List A → Type {!!}
-- [] ≈ [] = Lift Unit
-- [] ≈ (x ∷ ys) = Lift ⊥
-- (x ∷ xs) ≈ [] = Lift ⊥
-- (x ∷ xs) ≈ (y ∷ ys) =
--   ((x ≡ y) × (xs ≈ ys)) ⊎ {!!}

-- as inductive family (won't compute?)

data _≈_ {ℓ} {A : Type ℓ} : List A → List A → Type ℓ where
  nil-refl : [] ≈ []
  cons-cong : ∀ a {as bs}
            → (as ≈ bs)
            → (a ∷ as) ≈ (a ∷ bs)
  comm-rel : ∀ {a b as bs cs}
           → (p : as ≈ (b ∷ cs)) → (q : (a ∷ cs) ≈ bs)
           → (a ∷ as) ≈ (b ∷ bs)

-- on lists?
≈-refl : (xs : List A) → xs ≈ xs
≈-refl [] = nil-refl
≈-refl (x ∷ xs) = cons-cong x (≈-refl xs)

q : List A → NSet A
q [] = []
q (x ∷ xs) = x :: q xs

-- claim: (List A / _≈_) ≃ NSet A ?

f : {as bs : List A} → as ≈ bs → q as ≡ q bs
f nil-refl = refl
f (cons-cong a p) = cong (a ::_) (f p)
f (comm-rel p q) = comm (f p) (f q)

module _
  (disj-cons-nil : {x : A} {xs : NSet A} → [] ≡ x :: xs → ⊥)
  (disj-nil-cons : {x : A} {xs : NSet A} → x :: xs ≡ [] → ⊥) where

  g : {as bs : List A} → q as ≡ q bs → as ≈ bs
  g {as = []} {bs = []} p = nil-refl
  g {as = []} {bs = b ∷ bs} p = E.rec (disj-cons-nil p)
  g {as = a ∷ as} {bs = []} p = E.rec (disj-nil-cons p)
  g {as = a ∷ as} {bs = b ∷ bs} p = comm-rel {!!} {!!}
