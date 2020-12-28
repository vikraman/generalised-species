{-# OPTIONS --cubical --exact-split #-}

module gpd.FSMG2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

infix 40 _⊗_

data FSMG2 {ℓ} (A : Type ℓ) : Type ℓ where
  η : A → FSMG2 A
  unit : FSMG2 A
  _⊗_ : FSMG2 A → FSMG2 A → FSMG2 A

  α : (X Y Z : FSMG2 A) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
  Λ : (X : FSMG2 A) → unit ⊗ X ≡ X
  ρ : (X : FSMG2 A) → X ⊗ unit ≡ X
  β : (X Y : FSMG2 A) → X ⊗ Y ≡ Y ⊗ X

  ⬠ : (W X Y Z : FSMG2 A)
    → α (W ⊗ X) (Y) (Z) ∙ α (W) (X) (Y ⊗ Z)
    ≡ cong (_⊗ Z) (α (W) (X) (Y)) ∙ α (W) (X ⊗ Y) (Z) ∙ cong (W ⊗_) (α (X) (Y) (Z))
  ▽ : (X Y : FSMG2 A)
    → α (X) (unit) (Y) ∙ cong (X ⊗_) (Λ (Y))
    ≡ cong (_⊗ Y) (ρ (X))
  ⬡ : (X Y Z : FSMG2 A)
    → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
    ≡ cong (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ cong (Y ⊗_) (β (X) (Z))

  β² : (X Y : FSMG2 A) → β X Y ∙ β Y X ≡ refl

  trunc : isGroupoid (FSMG2 A)

open import gpd.SMG

FSMG2-SMGStructure : ∀ {ℓ} {A : Type ℓ} → SMGStructure (FSMG2 A) {trunc}
SMGStructure.unit FSMG2-SMGStructure = unit
SMGStructure._⊗_ FSMG2-SMGStructure = _⊗_
SMGStructure.α FSMG2-SMGStructure = α _ _ _
SMGStructure.Λ FSMG2-SMGStructure = Λ _
SMGStructure.ρ FSMG2-SMGStructure = ρ _
SMGStructure.β FSMG2-SMGStructure = β _ _
SMGStructure.⬠ FSMG2-SMGStructure = ⬠ _ _ _ _
SMGStructure.▽ FSMG2-SMGStructure = ▽ _ _
SMGStructure.⬡ FSMG2-SMGStructure = ⬡ _ _ _
SMGStructure.β² FSMG2-SMGStructure = β² _ _

univ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {M : Type ℓ₂} {GM : isGroupoid M} {SMGM : SMGStructure M {GM}}
     → (f : A → M) → SMFunctor (FSMG2 A) {trunc} {FSMG2-SMGStructure} M {GM} {SMGM}
SMFunctor.f (univ f) x = {!!}
SMFunctor.f-unit (univ f) = {!!}
SMFunctor.f-⊗ (univ f) = {!!}
SMFunctor.f-α (univ f) = {!!}
SMFunctor.f-Λ (univ f) = {!!}
SMFunctor.f-ρ (univ f) = {!!}
SMFunctor.f-β (univ f) = {!!}
