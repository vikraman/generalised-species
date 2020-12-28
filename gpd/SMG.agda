{-# OPTIONS --cubical --exact-split #-}

module gpd.SMG where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

record SMGStructure {i} (El : Type i) {El-level : isGroupoid El} : Type i where
  constructor smg-structure
  field
    unit : El
    _⊗_ : El → El → El
  infix 40 _⊗_
  field
    α : {X Y Z : El} → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : {X : El} → unit ⊗ X ≡ X
    ρ : {X : El} → X ⊗ unit ≡ X
    β : {X Y : El} → X ⊗ Y ≡ Y ⊗ X

    ⬠ : {W X Y Z : El}
      → α {W ⊗ X} {Y} {Z} ∙ α {W} {X} {Y ⊗ Z}
      ≡ cong (_⊗ Z) (α {W} {X} {Y}) ∙ α {W} {X ⊗ Y} {Z} ∙ cong (W ⊗_) (α {X} {Y} {Z})
    ▽ : {X Y : El}
      → α {X} {unit} {Y} ∙ cong (X ⊗_) (Λ {Y})
      ≡ cong (_⊗ Y) (ρ {X})
    ⬡ : {X Y Z : El}
      → α {X} {Y} {Z} ∙ β {X} {Y ⊗ Z} ∙ α {Y} {Z} {X}
      ≡ cong (_⊗ Z) (β {X} {Y}) ∙ α {Y} {X} {Z} ∙ cong (Y ⊗_) (β {X} {Z})

    β² : {X Y : El} → β {X} {Y} ∙ β {Y} {X} ≡ refl

record SMFunctor {i} {j} (A : Type i) {GA : isGroupoid A} {SMGA : SMGStructure A {GA}}
                         (B : Type j) {GB : isGroupoid B} {SMGB : SMGStructure B {GB}} : Type (ℓ-max i j) where
  constructor sm-functor
  private
    module A = SMGStructure SMGA
    module B = SMGStructure SMGB
  field
    f : A → B
    f-unit : f A.unit ≡ B.unit
    f-⊗ : {X Y : A} → f (X A.⊗ Y) ≡ f X B.⊗ f Y
  field
    f-α : {X Y Z : A}
        → cong f (A.α {X} {Y} {Z}) ∙ f-⊗ {X} {Y A.⊗ Z} ∙ cong (f X B.⊗_) (f-⊗ {Y} {Z})
        ≡ f-⊗ {X A.⊗ Y} {Z} ∙ cong (B._⊗ f Z) (f-⊗ {X} {Y}) ∙ B.α {f X} {f Y} {f Z}
    f-Λ : {X : A} → cong f (A.Λ {X}) ≡ f-⊗ {A.unit} {X} ∙ cong (B._⊗ f X) f-unit ∙ B.Λ {f X}
    f-ρ : {X : A} → cong f (A.ρ {X}) ≡ f-⊗ {X} {A.unit} ∙ cong (f X B.⊗_) f-unit ∙ B.ρ {f X}
    f-β : {X Y : A} → cong f (A.β {X} {Y}) ∙ f-⊗ {Y} {X} ≡ f-⊗ {X} {Y} ∙ B.β {f X} {f Y}
