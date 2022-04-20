{-# OPTIONS --cubical --exact-split #-}

module set.MSet.Cover where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Relation.Binary

open import set.Prelude
open import set.MSet
open import set.MSet.Universal
open import set.MSet.Length
open import set.MSet.Nat

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A
    a b x y : A
    xs ys as bs cs : MSet A

data _≈₀_ {ℓ} {A : Type ℓ} : MSet A → MSet A → Type ℓ where
  nil-refl : [] ≈₀ []
  cons-cong : ∀ {a as bs}
            → (as ≈₀ bs)
            → (a :: as) ≈₀ (a :: bs)
  comm-rel : ∀ {a b as bs cs}
           → (p : as ≈₀ (b :: cs)) → (q : (a :: cs) ≈₀ bs)
           → (a :: as) ≈₀ (b :: bs)

_≈_ : MSet A → MSet A → Type _
xs ≈ ys = ∥ xs ≈₀ ys ∥

≈-refl : (xs : MSet A) → xs ≈ xs
≈-refl = elimProp.f squash ∣ nil-refl ∣ (λ x → P.map cons-cong)

encode : (xs ys : MSet A) → xs ≡ ys → xs ≈ ys
encode xs ys = J (λ ys p → xs ≈ ys) (≈-refl xs)

decode₀ : (xs ys : MSet A) → xs ≈₀ ys → xs ≡ ys
decode₀ _ _ nil-refl = refl
decode₀ _ _ (cons-cong p) = cong (_ ::_) (decode₀ _ _ p)
decode₀ _ _ (comm-rel p q) = commrel (decode₀ _ _ p) (decode₀ _ _ q)

decode : (xs ys : MSet A) → xs ≈ ys → xs ≡ ys
decode xs ys = P.rec (trunc xs ys) (decode₀ xs ys)

≈-equiv-≡ : {xs ys : MSet A} → (xs ≈ ys) ≃ (xs ≡ ys)
≈-equiv-≡ {xs = xs} {ys = ys} = propBiimpl→Equiv squash (trunc xs ys) (decode xs ys) (encode xs ys)

module _ {ℓ} {A : Type ℓ} where
  open BinaryRelation {A = MSet A} _≈_

  ≈₀-sym : (xs ys : MSet A) → xs ≈₀ ys → ys ≈₀ xs
  ≈₀-sym .[] .[] nil-refl = nil-refl
  ≈₀-sym .(_ :: _) .(_ :: _) (cons-cong p) = cons-cong (≈₀-sym _ _ p)
  ≈₀-sym .(_ :: _) .(_ :: _) (comm-rel p q) = comm-rel (≈₀-sym _ _ q) (≈₀-sym _ _ p)

  ≈-sym : isSym
  ≈-sym as bs = P.map (≈₀-sym as bs)

  ≈-trans : isTrans
  ≈-trans as bs cs p q = encode as cs (decode as bs p ∙ decode bs cs q)

  ≈-isEquivRel : isEquivRel
  ≈-isEquivRel = equivRel ≈-refl ≈-sym ≈-trans
