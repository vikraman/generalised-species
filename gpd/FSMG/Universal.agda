{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import UF-Univalence

module gpd.FSMG.Universal (ua : Univalence) where

open import UF-FunExt
open import UF-UA-FunExt
open import UF-hlevels ua

open import gpd.FSMG ua

private fe : FunExt
fe = FunExt-from-Univalence ua

abstract
  λ≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g
  λ≡ {X} {Y} = nfunext (fe X Y)

_∼∙_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g h : X → Y} → f ∼ g → g ∼ h → f ∼ h
p ∼∙ q = λ x → p x ∙ q x

λ≡-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g h : X → Y}
     → (p : f ∼ g) → (q : g ∼ h)
     → λ≡ p ∙ λ≡ q ≡ λ≡ (p ∼∙ q)
λ≡-∙ p q = {!!}

_⊗_ : {A : 𝓤 ̇} → FSMG A → FSMG A → FSMG A
_⊗_ = rec.f {B = FSMG _ → FSMG _}
            (λ ys → ys) (λ x b ys → x :: b ys)
            (λ x y b → λ≡ λ ys → swap x y (b ys))
            (λ x y b → λ≡-∙ (λ ys → swap x y (b ys)) (λ ys → swap y x (b ys)) ∙ {!!})
            (λ x y z b → {!!})
            (hlevels-closed-under-Π 2 (FSMG _) (λ _ → FSMG _) λ _ → trunc)
