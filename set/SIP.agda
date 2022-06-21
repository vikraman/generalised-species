{-# OPTIONS --cubical --safe #-}

module set.SIP where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma
open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto

module _ {ℓ} where

  RawCMStr : Type ℓ → Type ℓ
  RawCMStr M = M × (M → M → M)

  RawCM : Type (ℓ-suc ℓ)
  RawCM = TypeWithStr ℓ RawCMStr

  RawCMEquivStr : (M N : RawCM) → typ M ≃ typ N → Type ℓ
  RawCMEquivStr = AutoEquivStr RawCMStr

  RawCMUnivalentStr : UnivalentStr RawCMStr RawCMEquivStr
  RawCMUnivalentStr = autoUnivalentStr RawCMStr

  isCM : (M : Type ℓ) → RawCMStr M → Type ℓ
  isCM M (e , _⊗_) =
    isSet M ×
    (∀ x → e ⊗ x ≡ x) ×
    (∀ x y → x ⊗ y ≡ y ⊗ x) ×
    (∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z)

  isPropIsCM : (M : Type ℓ) → (S : RawCMStr M) → isProp (isCM M S)
  isPropIsCM M _ = isPropΣ isPropIsSet
                           λ ϕ → isProp× (isPropΠ λ _ → ϕ _ _)
                                          (isProp× (isPropΠ2 λ _ _ → ϕ _ _)
                                                   (isPropΠ3 λ _ _ _ → ϕ _ _))

  CMStr : Type ℓ → Type ℓ
  CMStr = AxiomsStructure RawCMStr isCM

  CM : Type (ℓ-suc ℓ)
  CM = TypeWithStr ℓ CMStr

  CMEquivStr : (M N : CM) → typ M ≃ typ N → Type ℓ
  CMEquivStr = AxiomsEquivStr RawCMEquivStr isCM

  CMUnivalentStr : UnivalentStr CMStr CMEquivStr
  CMUnivalentStr = axiomsUnivalentStr RawCMEquivStr isPropIsCM RawCMUnivalentStr

  CMSIP : (M N : CM) → M ≃[ CMEquivStr ] N ≃ (M ≡ N)
  CMSIP = SIP CMUnivalentStr

  module _ {M N : CM} where

    e₁ = str M .fst .fst
    _⊗₁_ = str M .fst .snd
    e₂ = str N .fst .fst
    _⊗₂_ = str N .fst .snd

    isCMHom : (typ M → typ N) → Type ℓ
    isCMHom f = (f e₁ ≡ e₂) × (∀ x y → f (x ⊗₁ y) ≡ (f x ⊗₂ f y))

  module _ (A : Type ℓ) (ASet : isSet A) where

    FCMStr : Type ℓ → Type ℓ
    FCMStr = AxiomsStructure (λ M → (A → M) × CMStr M) (λ M S → isCM M (S .snd .fst))

    FCM : Type (ℓ-suc ℓ)
    FCM = TypeWithStr ℓ FCMStr
