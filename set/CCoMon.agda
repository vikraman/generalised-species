{-# OPTIONS --cubical #-}

module set.CCoMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.Prelude
open import set.hRel
open import set.CMon using (CMon)
open import set.DLaw using (module day)

private
  variable
    ℓ : Level
    A B : Type ℓ

record CCoMon {ℓ} (C : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    k : C ⇸ II {ℓ}
    w : C ⇸ (C ⊗ C)
    isSetC : isSet C

  CSet : hSet ℓ
  CSet = C , isSetC

  field
    counit-l : ⊗[ idr CSet , k ] ⊚ w ≡ ρ⁻¹ CSet
    counit-r : ⊗[ k , idr CSet ] ⊚ w ≡ Λ⁻¹ CSet
    coassoc : ⊗[ w , idr CSet ] ⊚ w ≡ α⁻¹ CSet CSet CSet ⊚ ⊗[ idr CSet , w ] ⊚ w
    cocomm : β CSet CSet ⊚ w ≡ w

open import set.MSet
open import set.MSet.Universal as M using (_++_ ; MSetCMon)
open import set.Power as P

module _ {ℓ} {A : Type ℓ} (C : CMon A) where

  module C = CMon C
  open C

  _∗ : (B → A) → (B ⇸ A)
  _∗ = _# {BSet = A , isSetM}

  ∇ : CCoMon A
  CCoMon.k ∇ = (const e ∗) †
  CCoMon.w ∇ = ((uncurry C._⊗_) ∗) †
  CCoMon.isSetC ∇ = isSetM
  CCoMon.counit-l ∇ = TODO
  CCoMon.counit-r ∇ = TODO
  CCoMon.coassoc ∇ = TODO
  CCoMon.cocomm ∇ = TODO

MSetCCoMon : CCoMon (MSet A)
MSetCCoMon = ∇ (MSetCMon _)

module univ {M : Type _} (C : CMon M) (f : M ⇸ A) where

  f♯ : M ⇸ MSet A
  f♯ = M.univ.f♯ (day.ℙMCMon {{C}}) (f †) †

open univ
