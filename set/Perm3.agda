{-# OPTIONS --cubical --exact-split --termination-depth=2 --allow-unsolved-metas #-}

module set.Perm3 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetTruncation as S
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.Data.Vec as V
open import Cubical.Data.Nat as N
import Cubical.Data.Nat.Order as N
import Cubical.Data.FinData as FD
open import Cubical.Data.Fin as F
open import Cubical.Data.Fin.LehmerCode as F
open import Cubical.HITs.SetQuotients as Q

open import set.NSet
open import set.Prelude

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ
    n m o : ℕ

open import set.Perm2

lemma : (k : Fin (suc n)) → FinExcept k ≃ Fin n
lemma k = punchOutEquiv

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) where

  fun : A → B
  fun = equivFun e

  inv : B → A
  inv = (equivFun ∘ invEquiv) e

  fun-inv : ∀ y → fun (inv y) ≡ y
  fun-inv = secEq e

  inv-fun : ∀ x → inv (fun x) ≡ x
  inv-fun = retEq e

  funInj : ∀ x y → fun x ≡ fun y → x ≡ y
  funInj x y p = sym (retEq e x) ∙ cong inv p ∙ retEq e y

  invInj : ∀ x y → inv x ≡ inv y → x ≡ y
  invInj x y p = sym (secEq e x) ∙ cong fun p ∙ secEq e y

-- deletes i and p(i) from p

module _ (i : Fin (suc n)) (p : Fin (suc n) ≃ Fin (suc m)) where

  q :  FinExcept i ≃ FinExcept (fun p i)
  q = isoToEquiv (iso f g f-g g-f)
    where f : _
          f (j , ϕ) = fun p j , λ ψ → ϕ (funInj p i j ψ)
          g : _
          g (j , ϕ) = inv p j , λ ψ → ϕ (invInj p (fun p i) j (inv-fun p i ∙ ψ))
          f-g : _
          f-g (j , ϕ) = Σ≡Prop (λ _ → isPropΠ (λ _ → isProp⊥)) (fun-inv p j)
          g-f : _
          g-f (j , ϕ) = Σ≡Prop (λ _ → isPropΠ (λ _ → isProp⊥)) (inv-fun p j)

  pdel : Fin n ≃ Fin m
  pdel = compEquiv (invEquiv (punchOutEquiv {i = i}))
                   (compEquiv q (punchOutEquiv {i = fun p i}))
