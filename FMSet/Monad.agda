{-# OPTIONS --cubical --safe #-}

module FMSet.Monad where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import FMSet renaming (FMSet to M)
open import FMSet.Universal

map : {B : Type₀} → (A → B) → M A → M B
map f = FMSetRec.f trunc [] (λ a bs → f a ∷ bs)
  λ a b bas bbs bcs bp bq → comm (f a) (f b) bas bbs bcs bp bq

η : A → M A
η a = [ a ]

μ : M (M A) → M A
-- μ = FMSetUniversal.f♯ FMSetCMon (idfun (M _))
μ = FMSetRec.f trunc [] _++_
  λ a b bas bbs bcs bp bq → cong (a ++_) bp ∙ assoc-++ a b bcs
                          ∙ cong (_++ bcs) (comm-++ a b)
                          ∙ sym (assoc-++ b a bcs) ∙ cong (b ++_) bq

map-id : map (idfun A) ≡ idfun (M A)
map-id = funExt (FMSetElimProp.f (trunc _ _) refl λ x p → cong (x ∷_) p)

map-∘ : {B C : Type₀} (g : B → C) (f : A → B)
      → map (g ∘ f) ≡ map g ∘ map f
map-∘ g f = funExt (FMSetElimProp.f (trunc _ _) refl λ x p → cong (g (f x) ∷_) p)

tr-left : {B : Type₀} → μ ∘ map η ≡ idfun (M B)
tr-left = funExt (FMSetElimProp.f (trunc _ _) refl λ x p → cong (x ∷_) p)

tr-right : {B : Type₀} → μ ∘ η {A = M B} ≡ idfun (M B)
tr-right = funExt unitr-++

sq : {B : Type₀} → μ {A = B} ∘ map μ ≡ μ ∘ μ
sq = funExt (FMSetElimProp.f (trunc _ _) refl λ x p → {!!})
