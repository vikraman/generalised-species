{-# OPTIONS --cubical --exact-split #-}

module set.MSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum

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

++-nil-out : xs ++ ys ≡ [] → (xs ≡ []) × (ys ≡ [])
++-nil-out {xs = xs} {ys = ys} p =
  let u = m+n≡0→m≡0×n≡0 {m = length xs} {n = length ys} (sym (length-++ xs ys) ∙ cong length p)
  in sym (lenZero-out xs (u .fst)) , sym (lenZero-out ys (u .snd))

++-nil-in : (xs ≡ []) × (ys ≡ []) → xs ++ ys ≡ []
++-nil-in (p , q) i = p i ++ q i

++-nil-eqv : (xs ++ ys ≡ []) ≃ ((xs ≡ []) × (ys ≡ []))
++-nil-eqv =
  propBiimpl→Equiv (trunc _ _) (isProp× (trunc _ _) (trunc _ _)) ++-nil-out ++-nil-in

m+n≡1→m≡1×n≡0⊎m≡0×n≡1 : {m n : ℕ} → m + n ≡ 1 → ((m ≡ 1) × (n ≡ 0)) ⊎ ((m ≡ 0) × (n ≡ 1))
m+n≡1→m≡1×n≡0⊎m≡0×n≡1 {zero} {n} p = inr (refl , p)
m+n≡1→m≡1×n≡0⊎m≡0×n≡1 {suc m} {n} p =
  let q = injSuc {m = m + n} {n = 0} p
      r = m+n≡0→m≡0×n≡0 {m = m} {n = n} q
  in inl (cong suc (r .fst) , r .snd)

++-sing-out : xs ++ ys ≡ [ a ] → ((xs ≡ [ a ]) × (ys ≡ [])) ⊎ ((xs ≡ []) × (ys ≡ [ a ]))
++-sing-out {xs = xs} {ys = ys} p =
  let u = m+n≡1→m≡1×n≡0⊎m≡0×n≡1 {m = length xs} {n = length ys} (sym (length-++ xs ys) ∙ cong length p)
  in rec (uncurry (λ q r → let s = lenZero-out ys r in inl (sym (unitr-++ xs) ∙ cong (xs ++_) s ∙ p , sym s)))
         (uncurry (λ q r → let s = lenZero-out xs q in inr (sym s , cong (_++ ys) s ∙ p)))
         u

++-sing-in : ((xs ≡ [ a ]) × (ys ≡ [])) ⊎ ((xs ≡ []) × (ys ≡ [ a ])) → xs ++ ys ≡ [ a ]
++-sing-in = rec (uncurry (λ p q i → p i ++ q i)) (uncurry (λ p q i → p i ++ q i))

η : A → MSet A
η = [_]

μ : MSet (MSet A) → MSet A
μ = univ.f♯ (MSetCMon _) (idfun (MSet _))

μ-cons : (x : MSet A) (xs : MSet (MSet A)) → μ (x :: xs) ≡ x ++ μ xs
μ-cons = univ.f♯-cons (MSetCMon _) (idfun (MSet _))

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
