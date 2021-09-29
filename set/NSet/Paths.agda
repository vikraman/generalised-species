{-# OPTIONS --cubical --exact-split --safe #-}

module set.NSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation as P

open import set.NSet
open import set.NSet.Universal

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A
    a x : A
    xs ys : NSet A

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
≈-refl = elimProp.f squash ∣ nil-refl ∣ λ x {xs} → P.map (cons-cong refl)

encode : {as bs : NSet A} → as ≡ bs → as ≈ bs
encode {as = as} {bs = bs} = J (λ xs _ → as ≈ xs) (≈-refl as)

decode₀ : {as bs : NSet A} → as ≈₀ bs → as ≡ bs
decode₀ {as = .[]} {bs = .[]} nil-refl = refl
decode₀ {as = .(_ :: _)} {bs = .(_ :: _)} (cons-cong p q) = cong₂ _::_ p (decode₀ q)
decode₀ {as = .(_ :: _)} {bs = .(_ :: _)} (comm-rel p q) = comm (decode₀ p) (decode₀ q)

decode : {as bs : NSet A} → as ≈ bs → as ≡ bs
decode {as = as} {bs = bs} = P.rec (trunc as bs) decode₀

≈-equiv-≡ : {as bs : NSet A} → (as ≈ bs) ≃ (as ≡ bs)
≈-equiv-≡ = propBiimpl→Equiv squash (trunc _ _) decode encode
