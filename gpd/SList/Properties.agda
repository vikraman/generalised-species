{-# OPTIONS --without-K --exact-split --rewriting #-}

open import gpd.Prelude
open import gpd.SMG
open import gpd.SList
open import gpd.SList.SMGStructure
open import gpd.SList.SMGStructure.Tensor

module gpd.SList.Properties {i} {A : Type i} where

  module _ {j} {N : Type j} ⦃ N-level : has-level 1 N ⦄ ⦃ GN : SMGStructure N ⦄ where

    module _ (f : A → N) where

      module G = SMGStructure GN
      module F =
        SListRec {A = A} {P = N}
          G.I
          (λ x n → f x G.⊗ n)
          (λ x y n → ! (G.α (f x) (f y) n)
                    ∙ ap (G._⊗ n) (G.β (f x) (f y))
                    ∙ G.α (f y) (f x) n)
          (λ x y z n → {!!})
          (λ x y z n → {!!})
          N-level

      F-:: : (x : A) (xs : SList A) → F.f (x :: xs) == f x G.⊗ F.f xs
      F-:: x xs = idp

      F-η : (x : A) → F.f [ x ] == f x
      F-η x = G.ρ (f x)

      F-++ : (xs ys : SList A) → F.f (xs ++ ys) == F.f xs G.⊗ F.f ys
      F-++ =
        SListElimSet.f
          ⦃ Π-level (λ _ → has-level-apply G.trunc _ _) ⦄
          (λ ys → ! (G.Λ (F.f ys)))
          (λ x {xs} p ys → ap (f x G.⊗_) (p ys) ∙ ! (G.α (f x) (F.f xs) (F.f ys)))
          (λ x y {xs} p → {!!})

      _♯ : SMFunctor (SList A) N
      SMFunctor.f _♯ = F.f
      SMFunctor.f-I _♯ = idp
      SMFunctor.f-⊗ _♯ = F-++
      SMFunctor.f-α _♯ = {!!}
      SMFunctor.f-Λ _♯ = {!!}
      SMFunctor.f-ρ _♯ = {!!}
      SMFunctor.f-β _♯ = {!!}

    SList-Universal : SMFunctor (SList A) N ≃ (A → N)
    SList-Universal = TODO
