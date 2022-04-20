{-# OPTIONS --cubical --exact-split #-}

module set.ProofSystem where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetTruncation as S
open import Cubical.Relation.Binary
open import Cubical.Data.List as L
open import Cubical.HITs.SetQuotients as Q

open import set.NSet
open import set.Prelude

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

infix 10 _≈₀_ _≈_

data _≈₀_ {ℓ} {A : Type ℓ} : List A → List A → Type ℓ where
  nil-refl : [] ≈₀ []
  cons-cong : ∀ {a b as bs}
            → (a ≡ b) → (as ≈₀ bs)
            → (a ∷ as) ≈₀ (b ∷ bs)
  comm-rel : ∀ {a b as bs cs}
           → (p : as ≈₀ (b ∷ cs)) → (q : (a ∷ cs) ≈₀ bs)
           → (a ∷ as) ≈₀ (b ∷ bs)

_≈_ : List A → List A → Type _
xs ≈ ys = ∥ xs ≈₀ ys ∥

≈₀-refl : (xs : List A) → xs ≈₀ xs
≈₀-refl [] = nil-refl
≈₀-refl (x ∷ xs) = cons-cong refl (≈₀-refl xs)

encode : (xs ys : List A) → xs ≡ ys → xs ≈₀ ys
encode xs ys = J (λ ys p → xs ≈₀ ys) (≈₀-refl xs)

≈₀-sym : (xs ys : List A) → xs ≈₀ ys → ys ≈₀ xs
≈₀-sym .[] .[] nil-refl = nil-refl
≈₀-sym .(_ ∷ _) .(_ ∷ _) (cons-cong p q) = cons-cong (sym p) (≈₀-sym _ _ q)
≈₀-sym .(_ ∷ _) .(_ ∷ _) (comm-rel p q) = comm-rel (≈₀-sym _ _ q) (≈₀-sym _ _ p)

QSet : Type ℓ → Type ℓ
QSet A = List A / _≈_

i : List A → NSet A
i [] = []
i (x ∷ xs) = x :: i xs

i-≈₀ : (xs ys : List A) → xs ≈₀ ys → i xs ≡ i ys
i-≈₀ .[] .[] nil-refl = refl
i-≈₀ .(_ ∷ _) .(_ ∷ _) (cons-cong p q) = cong₂ _::_ p (i-≈₀ _ _ q)
i-≈₀ .(_ ∷ _) .(_ ∷ _) (comm-rel p q) = comm (i-≈₀ _ _ p) (i-≈₀ _ _ q)

i-≈ : (xs ys : List A) → xs ≈ ys → i xs ≡ i ys
i-≈ xs ys = P.rec (trunc _ _) (i-≈₀ xs ys)

Q→N : QSet A → NSet A
Q→N = Q.rec trunc i i-≈

_q::_ : A → QSet A → QSet A
_q::_ x =
  Q.rec squash/
        (λ xs → Q.[ x ∷ xs ])
        (λ xs ys p → eq/ (x ∷ xs) (x ∷ ys) (P.map (cons-cong refl) p))

-- N→Q : NSet A → QSet A
-- N→Q =
--   elim.f Q.[ [] ]
--          (λ x {xs} → x q::_)
--          (λ {a} {b} {as bs cs} {bas bbs bcs} {p} bp {q} bq → {!!})
--          (λ _ → squash/)

module _ {ℓ} {A : Type ℓ} where
  open BinaryRelation {A = List A} _≈_

  ≈-refl : isRefl
  ≈-refl as = ∣ ≈₀-refl as ∣

  ≈-sym : isSym
  ≈-sym as bs = P.map (≈₀-sym as bs)

  ≈-trans : isTrans
  ≈-trans as bs cs p q = TODO

  ≈-isEquivRel : isEquivRel
  ≈-isEquivRel = equivRel ≈-refl ≈-sym ≈-trans

  ≈-isPropValued : isPropValued
  ≈-isPropValued _ _ p q = squash p q

  ≈-isEffective : isEffective
  ≈-isEffective = isEquivRel→isEffective ≈-isPropValued ≈-isEquivRel

  ≈-iso-≡ : (as bs : List A) → Iso (_/_.[ as ] ≡ _/_.[ bs ]) (as ≈ bs)
  ≈-iso-≡ = isEquivRel→effectiveIso ≈-isPropValued ≈-isEquivRel
