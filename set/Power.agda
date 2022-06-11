{-# OPTIONS --cubical --exact-split --safe #-}

module set.Power where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Agda.Primitive

private
  variable
    ℓ : Level

open import Cubical.Functions.Logic public
open import Cubical.Foundations.Powerset public

PSet : hSet ℓ → hSet (ℓ-suc ℓ)
PSet (A , ϕ) = ℙ A , isSetℙ

η : {ASet@(A , ϕ) : hSet ℓ} → A → ℙ A
η {ASet = (A , ϕ)} x = λ y → (x ≡ y) , ϕ x y

よ : (ASet@(A , ϕ) : hSet ℓ) → A → ℙ A
よ (A , ϕ) a = λ x → (a ≡ x) , ϕ a x

_* : {A B : Type ℓ} → (A → ℙ B) → ℙ A → ℙ B
_* {A = A} {B} f = λ X b → ∃[ a ] f a b ⊓ X a

map : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} → (A → B) → ℙ A → ℙ B
map {BSet = BSet} f = (η {ASet = BSet} ∘ f) *

open import Cubical.HITs.PropositionalTruncation as P

よ* : {ASet@(A , ϕ) : hSet ℓ} → (よ ASet) * ≡ idfun (ℙ A)
よ* = funExt λ f → funExt λ a → ⇔toPath (rec (f a .snd) λ { (x , p , ψ) → transp (λ i → ⟨ f (p i) ⟩) i0 ψ }) (λ ξ → ∣ a , refl , ξ ∣₁)

*よ : {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} (f : A → ℙ B) → f ≡ f * ∘ (よ ASet)
*よ f = funExt λ a → funExt λ b → ⇔toPath (λ ξ → ∣ a , ξ , refl ∣₁) (rec (f a b .snd) λ { (x , ξ , p) → transp (λ i → ⟨ f (p (~ i)) b ⟩) i0 ξ })

_**_ : {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) : hSet ℓ} (g : B → ℙ C) (f : A → ℙ B) → (g * ∘ f) * ≡ g * ∘ f *
g ** f = funExt λ α → funExt λ c → ⇔toPath (rec squash₁ λ { (a , δ , θ) → P.map (λ { (b , κ , ϵ) → b , κ , ∣ a , ϵ , θ ∣₁ }) δ })
                                               (rec squash₁ λ { (b , δ , θ) → P.map (λ { (a , κ , ϵ) → a , ∣ b , δ , κ ∣₁ , ϵ }) θ })

open import set.Monad

codensity : ∀ {ℓ} {ASet@(A , ϕ) : hSet ℓ} {a : A} {P : A → hProp ℓ} → (∃[ x ] ((x ≡ a) , ϕ x a) ⊓ P x) ≡ P a
codensity {a = a} {P} = ⇔toPath (rec (P a .snd) λ { (x , p , ψ) → transp (λ i → ⟨ P (p i) ⟩) i0 ψ }) (λ p → ∣ (a , refl , p) ∣₁)
