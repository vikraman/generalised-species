{-# OPTIONS --cubical --exact-split --safe #-}

module set.PSh where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

private
  variable
    ℓ : Level

PSh : Type ℓ → Type (ℓ-suc ℓ)
PSh {ℓ} X = X → Type ℓ

η : {A : Type ℓ} → A → PSh A
η a = λ b → a ≡ b

_* : {A B : Type ℓ} → (A → PSh B) → PSh A → PSh B
f * = λ X b → Σ _ λ a → f a b × X a

map : {A B : Type ℓ} → (A → B) → PSh A → PSh B
map f = (η ∘ f) *

unitl : {A : Type ℓ} → η * ≡ idfun (PSh A)
unitl {A = A} = funExt λ X → funExt (λ b → h X b)
  where h : (X : PSh A) (b : A)
          → (Σ A (λ a → (a ≡ b) × X a)) ≡ X b
        h X b = ua (isoToEquiv (iso f g f-g g-f))
          where f : (Σ A (λ a → Σ (a ≡ b) (λ _ → X a))) → X b
                f (a , p , z) = transp (λ i → X (p i)) i0 z
                g : X b → (Σ A (λ a → Σ (a ≡ b) (λ _ → X a)))
                g z = b , refl , z
                f-g : ∀ z → f (g z) ≡ z
                f-g z i = transp (λ _ → X b) i z
                g-f : ∀ z → g (f z) ≡ z
                g-f (a , p , z) i = p (~ i) , (λ j → p (~ i ∨ j)) , transp (λ j → X (p (~ i ∧ j))) i z

unitr : {A B : Type ℓ} → (f : A → PSh B) → f * ∘ η ≡ f
unitr {A = A} {B} f = funExt λ a → funExt λ b → h a b
  where h : (a : A) (b : B) → Σ A (λ x → (f x b) × (a ≡ x)) ≡ f a b
        h a b = ua (isoToEquiv (iso t s t-s s-t))
          where t : Σ A (λ x → f x b × (a ≡ x)) → f a b
                t (x , z , p) = transp (λ i → f (p (~ i)) b) i0 z
                s : f a b → Σ A (λ x → f x b × (a ≡ x))
                s z = a , z , refl
                t-s : ∀ z → t (s z) ≡ z
                t-s z i = transp (λ _ → f a b) i z
                s-t : ∀ z → s (t z) ≡ z
                s-t (x , z , p) i = p i , transp (λ j → f (p (i ∨ ~ j)) b) i z , λ j → p (i ∧ j)

assoc : {A B C : Type ℓ} (f : A → PSh B) (g : B → PSh C) → g * ∘ f * ≡ (g * ∘ f) *
assoc {A = A} {B} {C} f g = funExt λ X → funExt λ c → h X c
  where h : (X : PSh A) (c : C) → Σ B (λ b → (g b c) × (Σ A (λ a → (f a b) × (X a)))) ≡ Σ A (λ a → (Σ B (λ b → (g b c) × (f a b))) × (X a))
        h X c = ua (isoToEquiv (iso t s t-s s-t))
          where t : Σ B (λ b → (g b c) × (Σ A (λ a → (f a b) × (X a)))) → Σ A (λ a → (Σ B (λ b → (g b c) × (f a b))) × (X a))
                t (b , u , a , v , w) = a , (b , u , v) , w
                s : Σ A (λ a → (Σ B (λ b → (g b c) × (f a b))) × (X a)) → Σ B (λ b → (g b c) × (Σ A (λ a → (f a b) × (X a))))
                s (a , (b , u , v) , w) = b , u , a , v , w
                t-s : ∀ z → t (s z) ≡ z
                t-s (a , (b , u , v) , w) = refl
                s-t : ∀ z → s (t z) ≡ z
                s-t (b , u , a , v , w) = refl

open import set.Monad

PshRMonad : ∀ {ℓ} → RMonad {ℓ} PSh
RMonad.map PshRMonad = map
RMonad.η PshRMonad = η
PshRMonad RMonad.* = _*
RMonad.unitl PshRMonad = unitl
RMonad.unitr PshRMonad = unitr
RMonad.assoc PshRMonad = assoc
