{-# OPTIONS --cubical --exact-split --safe #-}

module set.Iso where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import set.MSet as M
open import set.NSet as N
open import set.MSet.Universal as M
open import set.NSet.Universal as N

private
  variable
    ℓ : Level
    A : Type ℓ

M≃N : MSet A ≃ NSet A
M≃N {ℓ} {A} = isoToEquiv (iso f g f-g g-f)
  where module f-univ = M.univ (NSetCMon A) N.[_]
        f : MSet A → NSet A
        f = f-univ.f♯
        module g-univ = N.univ (MSetCMon A) M.[_]
        g : NSet A → MSet A
        g = g-univ.f♯
        f-g : (xs : NSet A) → f (g xs) ≡ xs
        f-g = N.elimProp.f (trunc _ _) refl λ x → cong (x ::_)
        g-f : (xs : MSet A) → g (f xs) ≡ xs
        g-f = M.elimProp.f (trunc _ _) refl λ x → cong (x ::_)

_ : (M≃N .fst) (1 :: 2 :: 3 :: []) ≡ (1 :: 2 :: 3 :: [])
_ = refl

M≃N' : MSet A ≃ NSet A
M≃N' {ℓ} {A} = isoToEquiv (iso f g f-g g-f)
  where f : MSet A → NSet A
        f = M.elim.f [] (λ x xs → x :: xs) (λ x y xs → N.swap x y xs) (λ _ → trunc)
        g : NSet A → MSet A
        g = N.elim.f [] (λ x xs → x :: xs) (λ p q → M.commrel p q) (λ _ → trunc)
        f-g : (xs : NSet A) → f (g xs) ≡ xs
        f-g = N.elimProp.f (trunc _ _) refl (λ x → cong (x ::_))
        g-f : (xs : MSet A) → g (f xs) ≡ xs
        g-f = M.elimProp.f (trunc _ _) refl (λ x → cong (x ::_))

open import set.CMon as F

F≃M : Free A ≃ MSet A
F≃M {ℓ} {A} = isoToEquiv (iso f g f-g g-f)
  where module f-univ = F.univ (MSetCMon A) M.[_]
        f : Free A → MSet A
        f = f-univ.f♯
        module g-univ = M.univ (FreeCMon A) F.η
        g : MSet A → Free A
        g = g-univ.f♯
        f-g : (xs : MSet A) → f (g xs) ≡ xs
        f-g = M.elimProp.f (trunc _ _) refl (λ x → cong (x ::_))
        g-f : (xs : Free A) → g (f xs) ≡ xs
        g-f = F.elimProp.f (trunc _ _) (λ x → comm (η x) e ∙ unit (η x)) refl
                           (λ {m₁} {m₂} ϕ ψ → cong g (f-univ.f♯-⊗ m₁ m₂) ∙ g-univ.f♯-++ (f m₁) (f m₂) ∙ cong₂ _⊗_ ϕ ψ)

_ : F≃M .fst (η 1 ⊗ (η 2 ⊗ (η 3 ⊗ η 4))) ≡ 1 :: 2 :: 3 :: 4 :: []
_ = refl

_ : F≃M .fst ((η 1 ⊗ η 2) ⊗ (η 3 ⊗ η 4)) ≡ 1 :: 2 :: 3 :: 4 :: []
_ = refl

_ : F≃M .fst (((η 1 ⊗ η 2) ⊗ η 3) ⊗ η 4) ≡ 1 :: 2 :: 3 :: 4 :: []
_ = refl
