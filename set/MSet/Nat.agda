{-# OPTIONS --cubical --exact-split --safe #-}

module set.MSet.Nat where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import set.MSet as M
open import set.MSet.Universal as M
open import set.CMon

Nat : Type₀
Nat = MSet Unit

ℕCMon : CMon ℕ
CMon.e ℕCMon = 0
CMon._⊗_ ℕCMon = _+_
CMon.unit-⊗ ℕCMon = λ x → refl
CMon.comm-⊗ ℕCMon = +-comm
CMon.assoc-⊗ ℕCMon = +-assoc
CMon.isSetM ℕCMon = isSetℕ

Nat≃ℕ : Nat ≃ ℕ
Nat≃ℕ = isoToEquiv (iso f g f-g g-f)
  where f : Nat → ℕ
        f = rec.f 0 (λ _ → suc) (λ _ _ _ → refl) isSetℕ
        g : ℕ → Nat
        g zero = []
        g (suc n) = tt :: g n
        f-g : ∀ n → f (g n) ≡ n
        f-g zero = refl
        f-g (suc n) = cong suc (f-g n)
        g-f : ∀ x → g (f x) ≡ x
        g-f = M.elimProp.f (trunc _ _) refl λ x {xs} p → cong (tt ::_) p

private
  variable
    ℓ : Level
    A : Type ℓ

! : A → Unit
! ._ = tt

length : MSet A → ℕ
length = (Nat≃ℕ .fst) ∘ M.univ.f♯ (MSetCMon Unit) ([_] ∘ !)

length2 : MSet A → ℕ
length2 = rec.f 0 (λ _ → suc) (λ _ _ _ → refl) isSetℕ

l1~l2 : (xs : MSet A) → length xs ≡ length2 xs
l1~l2 = M.elimProp.f (isSetℕ _ _) refl λ x p → cong suc p
