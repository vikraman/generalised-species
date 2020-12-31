{-# OPTIONS --cubical --exact-split --safe #-}

module set.MSet.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty as E
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import set.MSet
open import set.MSet.Universal

private
  variable
    ℓ : Level
    A B : Type ℓ
    ASet : isSet A
    a x : A
    xs ys : MSet A

disj-nil-cons : x :: xs ≡ [] → ⊥
disj-nil-cons p = transport (λ i → fst (code (p i))) tt
  where code : MSet A → hProp ℓ-zero
        code = rec.f (⊥ , isProp⊥)
                     (λ _ _ → Unit , isPropUnit)
                     (λ _ _ _ _ → Unit , isPropUnit)
                     isSetHProp

disj-cons-nil : [] ≡ x :: xs → ⊥
disj-cons-nil p = disj-nil-cons (sym p)

open import set.MSet.Nat using (length)

lenZero-out : (xs : MSet A) → length xs ≡ 0 → [] ≡ xs
lenZero-out = elimProp.f (isPropΠ λ _ → trunc _ _)
                         (λ _ → refl)
                         (λ x {xs} f p → E.rec (snotz p))

singSet : Type ℓ → Type ℓ
singSet A = Σ (MSet A) (λ xs → 1 ≡ length xs)

is-sing-pred : MSet A → A → Type _
is-sing-pred xs a = [ a ] ≡ xs

is-sing-pred-prop : (xs : MSet A) (z : A) → isProp (is-sing-pred xs z)
is-sing-pred-prop xs a = trunc [ a ] xs

is-sing : MSet A → Type _
is-sing xs = Σ _ (is-sing-pred xs)

[_]-is-sing : (a : A) → is-sing [ a ]
[ a ]-is-sing = a , refl

sing=isProp : ∀ {x y : A} → isProp ([ x ] ≡ [ y ])
sing=isProp {x = x} {y = y} = trunc [ x ] [ y ]

sing=-in : ∀ {x y : A} → x ≡ y → [ x ] ≡ [ y ]
sing=-in p i = [ p i ]

sing=isContr : ∀ {x y : A} → x ≡ y → isContr ([ x ] ≡ [ y ])
sing=isContr p = sing=-in p , sing=isProp (sing=-in p)

is-sing-set : {ϕ : isSet A} (xs : MSet A) → isSet (is-sing xs)
is-sing-set {ϕ = ϕ} xs = isSetΣ ϕ λ x → isProp→isSet (is-sing-pred-prop xs x)

lenOne-down : (x : A) (xs : MSet A) → length (x :: xs) ≡ 1 → [] ≡ xs
lenOne-down x xs p = lenZero-out xs (injSuc p)

lenOne-cons : (x : A) (xs : MSet A) → length (x :: xs) ≡ 1 → is-sing (x :: xs)
lenOne-cons x xs p =
  let q = lenOne-down x xs p
  in transp (λ i → is-sing (x :: q i)) i0 [ x ]-is-sing

lenTwo-⊥ : (x y : A) (xs : MSet A) → (length (y :: x :: xs) ≡ 1) ≃ ⊥
lenTwo-⊥ x y xs = (λ p → E.rec (snotz (injSuc p))) , record { equiv-proof = E.elim }

isContrlenTwo-⊥→X : (X : Type ℓ) (x y : A) (xs : MSet A) → isContr (length (y :: x :: xs) ≡ 1 → X)
isContrlenTwo-⊥→X X x y xs = subst (λ Z → isContr (Z → X)) (sym (ua (lenTwo-⊥ x y xs))) (isContr⊥→A {A = X})

lenOne-swap : {A : Type ℓ} (x y : A) (xs : MSet A)
            → PathP (λ i → length (MSet.swap x y xs i) ≡ 1 → is-sing (MSet.swap x y xs i))
                    (λ p → lenOne-cons x (y :: xs) p)
                    (λ p → lenOne-cons y (x :: xs) p)
lenOne-swap {A = A} x y xs =
  transport (sym (PathP≡Path (λ i → length (MSet.swap x y xs i) ≡ 1 → is-sing (MSet.swap x y xs i)) _ _))
            (isContr→isProp (isContrlenTwo-⊥→X _ x y xs) _ _)

lenOne-out : {ϕ : isSet A} (xs : MSet A) → length xs ≡ 1 → is-sing xs
lenOne-out {ϕ = ϕ} =
  elim.f (λ p → E.rec (znots p))
         (λ x {xs} f p → lenOne-cons x xs p)
         (λ x y {xs} f → lenOne-swap x y xs)
         (λ xs → isSetΠ (λ p → is-sing-set {ϕ = ϕ} xs))
