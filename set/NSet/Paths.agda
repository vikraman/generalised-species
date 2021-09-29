{-# OPTIONS --cubical --exact-split --safe #-}

module set.NSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetTruncation as S
open import Cubical.Relation.Binary
open import Cubical.Data.List
open import Cubical.HITs.SetQuotients

open import set.NSet
open import set.NSet.Universal

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A

data _≈₀_ {A : Type ℓ} : NSet A → NSet A → Type ℓ where
  nil-refl : [] ≈₀ []
  cons-cong : ∀ {a b as bs}
            → (p : a ≡ b) → (q : as ≈₀ bs)
            → (a :: as) ≈₀ (b :: bs)
  comm-rel : ∀ {a b as bs cs}
           → (p : as ≈₀ (b :: cs)) → (q : (a :: cs) ≈₀ bs)
           → (a :: as) ≈₀ (b :: bs)

_≈_ : {A : Type ℓ} → NSet A → NSet A → Type ℓ
as ≈ bs = ∥ as ≈₀ bs ∥

≈-refl : (as : NSet A) → as ≈ as
≈-refl = elimProp.f squash ∣ nil-refl ∣ λ _ → P.map (cons-cong refl)

encode : {as bs : NSet A} → as ≡ bs → as ≈ bs
encode {as = as} = J (λ xs _ → as ≈ xs) (≈-refl as)

decode₀ : {as bs : NSet A} → as ≈₀ bs → as ≡ bs
decode₀ nil-refl = refl
decode₀ (cons-cong p q) = cong₂ _::_ p (decode₀ q)
decode₀ (comm-rel p q) = comm (decode₀ p) (decode₀ q)

decode : {as bs : NSet A} → as ≈ bs → as ≡ bs
decode = P.rec (trunc _ _) decode₀

≈-equiv-≡ : {as bs : NSet A} → (as ≈ bs) ≃ (as ≡ bs)
≈-equiv-≡ = propBiimpl→Equiv squash (trunc _ _) decode encode

≈₀-sym : (as bs : NSet A) → as ≈₀ bs → bs ≈₀ as
≈₀-sym .[] .[] nil-refl = nil-refl
≈₀-sym .(_ :: _) .(_ :: _) (cons-cong p q) = cons-cong (sym p) (≈₀-sym _ _ q)
≈₀-sym .(_ :: _) .(_ :: _) (comm-rel p q) = comm-rel (≈₀-sym _ _ q) (≈₀-sym _ _ p)

≈-sym : (as bs : NSet A) → as ≈ bs → bs ≈ as
≈-sym as bs = P.map (≈₀-sym as bs)

-- can't prove
-- ≈-trans₀ : (as bs cs : NSet A) → as ≈₀ bs → bs ≈₀ cs → as ≈₀ cs

-- but can prove this by transport
≈-trans : (as bs cs : NSet A) → as ≈ bs → bs ≈ cs → as ≈ cs
≈-trans as bs cs p q = encode (decode p ∙ decode q)

-- alternate set-truncated version

-- _≈₁_ : {A : Type ℓ} → NSet A → NSet A → Type ℓ
-- as ≈₁ bs = ∥ as ≈₀ bs ∥₂

-- ≈₁-refl : (as : NSet A) → as ≈₁ as
-- ≈₁-refl =
--   elim.f ∣ nil-refl ∣₂ (λ x {xs} → S.map (cons-cong refl))
--          {!!}
--          (λ _ → squash₂)

q : List A → NSet A
q [] = []
q (x ∷ xs) = x :: q xs

_≋_ : List A → List A → Type _
xs ≋ ys = q xs ≈ q ys

module _ {ℓ} {A : Type ℓ} where
  open BinaryRelation {A = List A} _≋_

  ≋-refl : isRefl
  ≋-refl as = ≈-refl (q as)

  ≋-sym : isSym
  ≋-sym as bs =  ≈-sym (q as) (q bs)

  ≋-trans : isTrans
  ≋-trans as bs cs = ≈-trans (q as) (q bs) (q cs)

  ≋-isEquivRel : isEquivRel
  ≋-isEquivRel = equivRel ≋-refl ≋-sym ≋-trans

  ≋-isPropValued : isPropValued
  ≋-isPropValued _ _ p q = squash p q

  ≋-isEffective : isEffective
  ≋-isEffective = isEquivRel→isEffective ≋-isPropValued ≋-isEquivRel

  ≋-iso-≡ : (as bs : List A) → Iso (_/_.[ as ] ≡ _/_.[ bs ]) (as ≋ bs)
  ≋-iso-≡ = isEquivRel→effectiveIso ≋-isPropValued ≋-isEquivRel
