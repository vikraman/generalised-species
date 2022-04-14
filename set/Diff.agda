{-# OPTIONS --cubical --exact-split #-}

module set.Diff where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Agda.Primitive

-- open import set.Power as P
open import set.Prelude
open import set.hRel as hRel
open import set.MSet
open import set.MSet.Paths
open import set.MSet.Universal using (_++_)
open import set.CMon using (CMon)
open import set.CCoMon using (module univ)

private
  variable
    ℓ : Level
    A B : Type ℓ

_∗ : (A → MSet B) → (A ⇸ MSet B)
_∗ = _# {BSet = MSet _ , trunc}

δ : MSet A ⇸ MSet (MSet A)
δ = (μ ∗) †

ε : MSet A ⇸ A
ε = (η ∗) †

ϕ-⊗ : (MSet A ⊗ MSet B) ⇸ MSet (A ⊗ B)
ϕ-⊗ = univ.f♯ TODO TODO

IICMon : CMon {lzero} II
CMon.e IICMon = tt*
CMon._⊗_ IICMon = const (const tt*)
CMon.unit-⊗ IICMon = isPropUnit* tt*
CMon.comm-⊗ IICMon = λ _ _ → refl
CMon.assoc-⊗ IICMon = λ _ _ _ → refl
CMon.isSetM IICMon = isSetUnit*

ϕ-II : II ⇸ MSet II
ϕ-II = univ.f♯ IICMon (hRel.idr (II , isSetUnit*))

w : MSet A ⇸ (MSet A ⊗ MSet A)
w = (uncurry _++_ ∗) †

k : MSet A ⇸ II
k = ((λ _ → []) ∗) †
