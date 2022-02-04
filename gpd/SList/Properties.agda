{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module gpd.SList.Properties where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG

module _ {i} {A : Type i} where

  app : SList A -> SList A -> SList A
  app =
    SListRec.f (λ ys → ys) (λ x f ys → x :: f ys)
               (λ x y f → λ= (λ ys → swap x y (f ys)))
               (λ x y z f → let h1 = λ ys → swap x y (f ys)
                                h2 = λ ys → swap y x (f ys)
                            in λ=-∙' h1 h2
                             ∙ ap λ= (λ= λ ys → swap² x y (f ys))
                             ∙ λ=-idp)
               (λ x y z f → TODO)
               ⟨⟩

  infixr 40 _++_
  _++_ : SList A -> SList A -> SList A
  _++_ = app

  ++-α : {xs ys zs : SList A} → (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
  ++-α {xs = xs} {ys = ys} {zs = zs} =
    SListElimSet.f {P = λ xs* → (xs* ++ ys) ++ zs == xs* ++ (ys ++ zs)}
    idp (λ x {xs*} p → ap (x ::_) p)
    (λ x y {xs*} p → TODO)
    xs

  ++-Λ : {xs : SList A} → nil ++ xs == xs
  ++-Λ {xs = xs} =
    SListElimSet.f {P = λ ys → nil ++ ys == ys}
    idp (λ x {xs} p → ap (x ::_) p)
    (λ x y {xs} p → TODO)
    xs

  ++-ρ : {xs : SList A} → xs ++ nil == xs
  ++-ρ {xs = xs} =
    SListElimSet.f {P = λ ys → ys ++ nil == ys}
    idp (λ x {xs} p → ap (x ::_) p)
    (λ x y {xs} p → TODO)
    xs

  instance
    SList-SMGStructure : SMGStructure (SList A)
    SMGStructure.I SList-SMGStructure = nil
    SMGStructure._⊗_ SList-SMGStructure = _++_
    SMGStructure.α SList-SMGStructure {X = X} {Y = Y} {Z = Z} = ++-α {xs = X} {ys = Y} {zs = Z}
    SMGStructure.Λ SList-SMGStructure = ++-Λ
    SMGStructure.ρ SList-SMGStructure = ++-ρ
    SMGStructure.β SList-SMGStructure = TODO
    SMGStructure.▽ SList-SMGStructure = TODO
    SMGStructure.⬠ SList-SMGStructure = TODO
    SMGStructure.⬡ SList-SMGStructure = TODO
    SMGStructure.β² SList-SMGStructure = TODO

  module _ {j} {N : Type j} {{_ : has-level 1 N}} {{GN : SMGStructure N}} where

    SList-Universal : SMFunctor (SList A) N ≃ (A → N)
    SList-Universal = TODO
