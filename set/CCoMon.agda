{-# OPTIONS --cubical #-}

module set.CCoMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.Prelude
open import set.hRel
open import set.CMon using (CMon)
open import set.DLaw

private
  variable
    ℓ : Level
    A B : Type ℓ

record CCoMon {ℓ} (C : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    e : C ⇸ II {ℓ}
    Δ : C ⇸ (C ⊗ C)
    isSetC : isSet C

  CSet : hSet ℓ
  CSet = C , isSetC

open import set.MSet
open import set.MSet.Universal as M using (_++_ ; MSetCMon)
open import set.Power as P

module _ {ℓ} {A : Type ℓ} (C : CMon A) where

  module C = CMon C
  open C

  _∗ : (B → A) → (B ⇸ A)
  _∗ = _# {BSet = A , isSetM}

  ∇ : CCoMon A
  CCoMon.e ∇ = (const e ∗) †
  CCoMon.Δ ∇ = ((uncurry C._⊗_) ∗) †
  CCoMon.isSetC ∇ = isSetM

MSetCCoMon : CCoMon (MSet A)
MSetCCoMon = ∇ (MSetCMon _)

module univ {M : Type _} (C : CMon M) (f : M ⇸ A) where

  f♯ : M ⇸ MSet A
  f♯ = M.univ.f♯ (day.ℙMCMon {{C}}) (f †) †

open univ
