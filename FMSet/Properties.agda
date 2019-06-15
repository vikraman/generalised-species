{-# OPTIONS --cubical --safe #-}

module FMSet.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import FMSet
open import FMSet.Universal

open import Cubical.Data.Nat

length : FMSet A → ℕ
length = FMSetRec.f isSetℕ 0 (λ _ → suc)
  λ a b bas bbs bcs bp bq → cong suc (bp ∙ bq)

singSet : Type₀ → Type₀
singSet A = Σ (FMSet A) (λ xs → 1 ≡ length xs)

is-sing-pred : FMSet A → A → Type₀
is-sing-pred xs z = [ z ] ≡ xs

is-sing-pred-prop : (xs : FMSet A) (z : A) → isProp (is-sing-pred xs z)
is-sing-pred-prop xs z = trunc [ z ] xs

is-sing : FMSet A → Type₀
is-sing xs = Σ _ (is-sing-pred xs)

is-sing-prop : (xs : FMSet A) → isProp (is-sing xs)
is-sing-prop xs (y , py) (z , pz) = ΣProp≡ (is-sing-pred-prop xs) {!!}

import Cubical.Data.Empty as D

lenZero-out : (xs : FMSet A) → 0 ≡ length xs → [] ≡ xs
lenZero-out = FMSetElimProp.f
  (propPi (λ _ → trunc _ _))
  (λ _ → refl)
  (λ x {xs} f p → D.⊥-elim (znots p))

lem1 : ∀ {a b as bs cs p q i} → 1 ≡ length (comm a b as bs cs p q i) → [] ≡ as
lem1 r = {!⊥-elim!}

lenOne-out : (xs : FMSet A) → 1 ≡ length xs → is-sing xs
lenOne-out = FMSetElim.f
  (λ p → D.⊥-elim (snotz p))
  (λ x {xs} f p → let q : 0 ≡ length xs ; q = injSuc p
                      r : [] ≡ xs ; r = lenZero-out xs q
                  in x , cong (x ∷_) r)
  (λ a b {as bs cs} fas fbs fcs {p} fp {q} fq → λ i r → {!!})
  {!!}

open import Cubical.Foundations.Logic

code : FMSet A → FMSet A → hProp
code [] [] = ⊤
code [] (y ∷ ys) = ⊥
code [] (comm a b as bs cs p q i) = ⊥
code [] (trunc ys zs p q i j) = {!!}
code (x ∷ xs) [] = ⊥
code (x ∷ xs) (y ∷ ys) = {!!}
code (x ∷ xs) (comm a b as bs cs p q i) = {!!}
code (x ∷ xs) (trunc ys zs p q i j) = {!!}
code (comm a b as bs cs p q i) ys = {!!}
code (trunc xs zs p q i j) ys = {!!}
