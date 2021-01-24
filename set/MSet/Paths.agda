{-# OPTIONS --cubical --exact-split #-}

module set.MSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import set.Prelude
open import set.MSet
open import set.MSet.Universal
open import set.MSet.Length
open import set.MSet.Nat

private
  variable
    ℓ : Level
    A B : Type ℓ
    ϕ : isSet A
    a x : A
    xs ys : MSet A

module _ {ϕ : isSet A} (a b : A) where

  lem71 : ([ a ] ≡ [ b ]) ≃ (a ≡ b)
  lem71 = propBiimpl→Equiv (trunc _ _) (ϕ _ _) (λ p → [-]-inj {ϕ = ϕ} (lenOnePath-in {ϕ = ϕ} p)) (cong [_])

μ : MSet (MSet A) → MSet A
μ = univ.f♯ (MSetCMon _) (idfun (MSet _))

μ-cons : (x : MSet A) (xs : MSet (MSet A)) → μ (x :: xs) ≡ x ++ μ xs
μ-cons = univ.f♯-cons (MSetCMon _) (idfun (MSet _))

length-++ : (x y : MSet A) → length (x ++ y) ≡ length x + length y
length-++ x y = elimProp.f {B = λ xs → length (xs ++ y) ≡ length xs + length y} (isSetℕ _ _) refl TODO x

mlen : MSet (MSet A) → MSet ℕ
mlen = univ.f♯ (MSetCMon _) ([_] ∘ length)

mlen-cons : (x : MSet A) (xs : MSet (MSet A)) → mlen (x :: xs) ≡ length x :: mlen xs
mlen-cons = univ.f♯-cons (MSetCMon ℕ) ([_] ∘ length)

mlenfold : MSet ℕ → ℕ
mlenfold = univ.f♯ ℕCMon (idfun ℕ)

mlenfold-cons : (n : ℕ) (xs : MSet (MSet A)) → mlenfold (n :: mlen xs) ≡ n + mlenfold (mlen xs)
mlenfold-cons n xs = univ.f♯-cons ℕCMon (idfun ℕ) n (mlen xs)

μ-len : (s : MSet (MSet A)) → length (μ s) ≡ mlenfold (mlen s)
μ-len = elimProp.f (isSetℕ _ _)
  refl
  λ x {xs} p → cong length (μ-cons x xs)
             ∙ length-++ x (μ xs)
             ∙ sym (cong mlenfold (mlen-cons x xs)
                   ∙ mlenfold-cons (length x) xs
                   ∙ cong (length x +_) (sym p))

module _ {ϕ : isSet A} (a : A) (s : MSet (MSet A)) where

  lem72 : [ a ] ≡ μ s → Σ (MSet (MSet A)) λ s' → (μ s' ≡ []) × ([ a ] :: s' ≡ s)
  lem72 = TODO

module _ {ϕ : isSet A} (s1 s2 : MSet (MSet A)) where

  lem73 : μ (s1 ++ s2) ≡ μ s1 ++ μ s2
  lem73 = univ.f♯-++ (MSetCMon A) (idfun (MSet A)) s1 s2

module _ {ϕ : isSet A} {ψ : isSet B} (a : A) (t : MSet (A × B)) where

  mfst : MSet (A × B) → MSet A
  mfst = univ.f♯ (MSetCMon A) ([_] ∘ fst)

  lem74 : mfst t ≡ [ a ] → Σ B λ b → t ≡ [ (a , b) ]
  lem74 = TODO
