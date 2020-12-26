{-# OPTIONS --cubical --exact-split #-}

module set.DLaw where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

-- record DLaw {ℓ} {ℓ₂} (S : Type ℓ → Type ℓ) {{MS : Monad S}} (T : Type ℓ → Type ℓ₂) {{MT : RMonad T}} : Type {!!} where
--   private
--     module S = Monad MS
--     module T = RMonad MT
--   field
--     Λ : (X : Type ℓ) → S {!T X!} → T (S X)

open import set.CMon using (CMon)
open import set.MSet as M
open import set.MSet.Universal as M
open import set.Power as P

module day {ℓ} {M : Type ℓ} {{CM : CMon M}} where
  private
    module CM = CMon CM

    e : ℙ M
    e = P.η {ASet = M , CM.isSetM} CM.e

    _∙̂_ : ℙ M → ℙ M → ℙ M
    (p ∙̂ q) x = ∃[ x₁ ] ∃[ x₂ ] ((x ≡ x₁ CM.⊗ x₂) , CM.isSetM _ _) ⊓ p x₁ ⊓ q x₂

  ℙMCMon : CMon (ℙ M)
  CMon.e ℙMCMon = e
  CMon._⊗_ ℙMCMon = _∙̂_
  CMon.unit-⊗ ℙMCMon = TODO
  CMon.comm-⊗ ℙMCMon = TODO
  CMon.assoc-⊗ ℙMCMon = TODO
  CMon.isSetM ℙMCMon = TODO

Λ : ∀ {ℓ} (XSet@(X , ϕ) : hSet ℓ) → MSet (ℙ X) → ℙ (MSet X)
Λ (X , ϕ) = M.univ.f♯ (day.ℙMCMon {{MSetCMon X}}) (map {ASet = X , ϕ} {MSet X , trunc} ([_]))

unit1 : ∀ {ℓ} {XSet@(X , ϕ) : hSet ℓ}
      → Λ XSet ∘ [_] ≡ map {ASet = XSet} {BSet = MSet X , trunc} [_]
unit1 = TODO

Mmap : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → MSet A → MSet B
Mmap f = univ.f♯ (MSetCMon _) ([_] ∘ f)

unit2 : ∀ {ℓ} {XSet@(X , ϕ) : hSet ℓ}
      → Λ XSet ∘ Mmap (η {ASet = XSet}) ≡ η {ASet = MSet X , trunc}
unit2 = TODO

Mμ : ∀ {ℓ} {A : Type ℓ} → MSet (MSet A) → MSet A
Mμ = univ.f♯ (MSetCMon _) (idfun (MSet _))

mult1 : ∀ {ℓ} {XSet@(X , ϕ) : hSet ℓ}
      → map {ASet = MSet (MSet X) , trunc} {BSet = MSet X , trunc} (Mμ)
      ∘ Λ (MSet X , trunc) ∘ Mmap (Λ XSet)
      ≡ Λ XSet ∘ Mμ {A = ℙ X}
mult1 = TODO

-- we can't write this since P is relative
-- mult2 : ∀ {ℓ} {XSet@(X , ϕ) : hSet ℓ} → {!!}
-- mult2 = {!!}
