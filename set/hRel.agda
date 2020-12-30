{-# OPTIONS --cubical --exact-split #-}

module set.hRel where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc ; isIso ; id)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Agda.Primitive

open import set.Power as P

private
  variable
    ℓ : Level

infixr 10 _⇸_

_⇸_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⇸ B = A → ℙ B

isSet⇸ : {A B : Type ℓ} → isSet (A ⇸ B)
isSet⇸ = isSetΠ (λ _ → powersets-are-sets)

id : (ASet@(A , ϕ) : hSet ℓ) → A ⇸ A
id = よ

module _ {A B C : Type ℓ} where

  infixr 10 _⊚_
  _⊚_ : B ⇸ C → A ⇸ B → A ⇸ C
  g ⊚ f = g * ∘ f

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  unitl : {f : A ⇸ B} → id BSet ⊚ f ≡ f
  unitl {f} i = よ* {ASet = BSet} i ∘ f

  unitr : {f : A ⇸ B} → f ≡ f ⊚ id ASet
  unitr {f} i = *よ {ASet = ASet} {BSet = BSet} f i

module _ {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) DSet@(D , χ) : hSet ℓ} where

  assoc : {f : A ⇸ B} {g : B ⇸ C} {h : C ⇸ D} → h ⊚ (g ⊚ f) ≡ (h ⊚ g) ⊚ f
  assoc {f} {g} {h} i = (_**_ {ASet = BSet} {BSet = CSet} {CSet = DSet} h g) (~ i) ∘ f

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  isIso : (f : A ⇸ B) → Type (ℓ-suc ℓ)
  isIso f = Σ _ λ g → (g ⊚ f ≡ id ASet) × (f ⊚ g ≡ id BSet)

  isPropIsIso : {f : A ⇸ B} → isProp (isIso f)
  isPropIsIso {f} (g , p , q) (g' , p' , q') =
    Σ≡Prop (λ _ → isProp× (isSet⇸ _ _) (isSet⇸ _ _))
           (g ≡⟨ sym (unitl {ASet = BSet} {BSet = ASet}) ⟩
            id ASet ⊚ g ≡⟨ cong (_⊚ g) (sym p') ⟩
            (g' ⊚ f) ⊚ g ≡⟨ sym (assoc {ASet = BSet} {BSet = ASet} {CSet = BSet} {DSet = ASet} {g} {f} {g'}) ⟩
            g' ⊚ (f ⊚ g) ≡⟨ cong (g' ⊚_) q ⟩
            g' ⊚ id BSet ≡⟨ sym (unitr {ASet = BSet} {BSet = ASet}) ⟩
            g' ∎)

_≅_ : hSet ℓ → hSet ℓ → Type (ℓ-suc ℓ)
(A , ϕ) ≅ (B , ψ) = Σ _ (isIso {ASet = A , ϕ} {BSet = B , ψ})

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  ω' : A ≡ B → A ⇸ B
  ω' p = subst (A ⇸_) p (id ASet)

  -- ω : ASet ≡ BSet → ASet ≅ BSet
  -- ω p = subst (λ X → ASet ≅ X) p (id ASet , id ASet , {!!})

  -- isEquivω : isEquiv ω
  -- isEquivω = {!!}

data O {ℓ} : Type ℓ where

! : {A : Type ℓ} → O ⇸ A
! ()

¡ : {A : Type ℓ} → A ⇸ O
¡ a ()

ptd : {A B : Type ℓ} → A ⇸ B
ptd = ! ⊚ ¡

open import Cubical.Data.Sum

_⊕_ : (A B : Type ℓ) → Type ℓ
A ⊕ B = A ⊎ B

_⊕₀_ : (ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ) → hSet ℓ
(A , ϕ) ⊕₀ (B , ψ) = A ⊕ B , isSetSum ϕ ψ

module _ {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) DSet@(D , χ) : hSet ℓ} where

  ⊕[_,_] : A ⇸ B → C ⇸ D → (A ⊕ C) ⇸ (B ⊕ D)
  ⊕[ f , g ] (inl a) (inl b) = f a b
  ⊕[ f , g ] (inl a) (inr d) = ptd a d
  ⊕[ f , g ] (inr c) (inl b) = ptd c b
  ⊕[ f , g ] (inr c) (inr d) = g c d

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  p₁ : A ⊕ B ⇸ A
  p₁ (inl a) = よ ASet a
  p₁ (inr b) = ptd b

  p₂ : A ⊕ B ⇸ B
  p₂ (inl a) = ptd a
  p₂ (inr b) = よ BSet b

  i₁ : A ⇸ A ⊕ B
  i₁ x (inl a) = よ ASet x a
  i₁ x (inr b) = ptd x b

  i₂ : B ⇸ A ⊕ B
  i₂ y (inl a) = ptd y a
  i₂ y (inr b) = よ BSet y b

module _ {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) : hSet ℓ} where

  [_,_] : A ⇸ B → A ⇸ C → A ⇸ B ⊕ C
  [ f , g ] a (inl b) = f a b
  [ f , g ] a (inr c) = g a c

  [[_,_]]  : A ⇸ C → B ⇸ C → A ⊕ B ⇸ C
  [[ f , g ]] (inl a) c = f a c
  [[ f , g ]] (inr b) c = g b c

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where
  σ : A ⊕ B ⇸ B ⊕ A
  σ = [_,_] {ASet = ASet ⊕₀ BSet} {BSet = BSet} {CSet = ASet}
      (p₂ {ASet = ASet} {BSet = BSet}) (p₁ {ASet = ASet} {BSet = BSet})
