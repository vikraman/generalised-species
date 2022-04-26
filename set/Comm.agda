{-# OPTIONS --cubical --exact-split --safe #-}

module set.Comm where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.MSet
open import set.MSet.Paths
open import set.MSet.Universal

private
  variable
    ℓ : Level
    A B : Type ℓ

σ : MSet A × B → MSet (A × B)
σ (as , b) = mmap (λ a → (a , b)) as

σ♯ : MSet (MSet A × B) → MSet (A × B)
σ♯ = univ.f♯ (MSetCMon _) σ

τ : A × MSet B → MSet (A × B)
τ (a , bs) = mmap (λ b → (a , b)) bs

τ♯ : MSet (A × MSet B) → MSet (A × B)
τ♯ = univ.f♯ (MSetCMon _) τ

-- comm-htpy-nil : (as : MSet A) → τ♯ (σ (as , [])) ≡ σ♯ (τ (as , []))
-- comm-htpy-nil =
--   elimProp.f (λ {as} → trunc (τ♯ (σ (as , []))) (σ♯ (τ (as , []))))
--              refl
--              (λ a {as} p → p)

-- comm-htpy : (bs : MSet B) → (as : MSet A) → τ♯ (σ (as , bs)) ≡ σ♯ (τ (as , bs))
-- comm-htpy =
--   elimProp.f (λ {bs} → isPropΠ (λ as → trunc (τ♯ (σ (as , bs))) (σ♯ (τ (as , bs)))))
--              {!!}
--              {!!}

-- comm : τ♯ ∘ σ ≡ σ♯ ∘ τ
-- comm = funExt (λ (as , bs) → comm-htpy bs as)
