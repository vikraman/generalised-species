{-# OPTIONS --cubical --exact-split #-}

module set.hRel where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc ; isIso ; id)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit public
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
isSet⇸ = isSetΠ (λ _ → isSetℙ)

idr : (ASet@(A , ϕ) : hSet ℓ) → A ⇸ A
idr = よ

module _ {A B C : Type ℓ} where

  infixr 10 _⊚_
  _⊚_ : B ⇸ C → A ⇸ B → A ⇸ C
  g ⊚ f = g * ∘ f

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  unitl : {f : A ⇸ B} → idr BSet ⊚ f ≡ f
  unitl {f} i = よ* {ASet = BSet} i ∘ f

  unitr : {f : A ⇸ B} → f ≡ f ⊚ idr ASet
  unitr {f} i = *よ {ASet = ASet} {BSet = BSet} f i

module _ {ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , ξ) DSet@(D , χ) : hSet ℓ} where

  assoc : {f : A ⇸ B} {g : B ⇸ C} {h : C ⇸ D} → h ⊚ (g ⊚ f) ≡ (h ⊚ g) ⊚ f
  assoc {f} {g} {h} i = (_**_ {ASet = BSet} {BSet = CSet} {CSet = DSet} h g) (~ i) ∘ f

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  isIso : (f : A ⇸ B) → Type (ℓ-suc ℓ)
  isIso f = Σ _ λ g → (g ⊚ f ≡ idr ASet) × (f ⊚ g ≡ idr BSet)

  isPropIsIso : {f : A ⇸ B} → isProp (isIso f)
  isPropIsIso {f} (g , p , q) (g' , p' , q') =
    Σ≡Prop (λ _ → isProp× (isSet⇸ _ _) (isSet⇸ _ _))
           (g ≡⟨ sym (unitl {ASet = BSet} {BSet = ASet}) ⟩
            idr ASet ⊚ g ≡⟨ cong (_⊚ g) (sym p') ⟩
            (g' ⊚ f) ⊚ g ≡⟨ sym (assoc {ASet = BSet} {BSet = ASet} {CSet = BSet} {DSet = ASet} {g} {f} {g'}) ⟩
            g' ⊚ (f ⊚ g) ≡⟨ cong (g' ⊚_) q ⟩
            g' ⊚ idr BSet ≡⟨ sym (unitr {ASet = BSet} {BSet = ASet}) ⟩
            g' ∎)

_≅_ : hSet ℓ → hSet ℓ → Type (ℓ-suc ℓ)
(A , ϕ) ≅ (B , ψ) = Σ _ (isIso {ASet = A , ϕ} {BSet = B , ψ})

module _ {ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ} where

  ω' : A ≡ B → A ⇸ B
  ω' p = subst (A ⇸_) p (idr ASet)

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

II = Unit*

-- record II {ℓ} : Type ℓ where
--   constructor tt

-- IIContr : isContr (II {ℓ})
-- IIContr = tt , λ { tt → refl }

-- IISet : ∀ {ℓ} → hSet ℓ
-- IISet = II , isProp→isSet (isContr→isProp IIContr)

ii : {A : Type ℓ} → A ⇸ II
ii a = よ (Unit* , isSetUnit*) tt*

open import Cubical.Data.Sum

_⊕_ : (A B : Type ℓ) → Type ℓ
A ⊕ B = A ⊎ B

_⊕₀_ : (ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ) → hSet ℓ
(A , ϕ) ⊕₀ (B , ψ) = A ⊕ B , isSet⊎ ϕ ψ

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

_⊗_ : (A B : Type ℓ) → Type ℓ
A ⊗ B = A × B

⊗[_,_] : {A B C D : Type ℓ} → (f : A ⇸ B) (g : C ⇸ D) → (A ⊗ C) ⇸ (B ⊗ D)
⊗[ f , g ] (a , c) (b , d) = f a b ⊓ g c d

module _ (ASet@(A , ϕ) : hSet ℓ) where
  ρ : (A ⊗ II) ⇸ A
  ρ (a , _) = よ ASet a

  ρ⁻¹ : A ⇸ (A ⊗ II)
  ρ⁻¹ a = よ (A ⊗ II , isSet× ϕ isSetUnit*) (a , tt*)

module _ (ASet@(A , ϕ) : hSet ℓ) where
  Λ : (II ⊗ A) ⇸ A
  Λ (_ , a) = よ ASet a

  Λ⁻¹ : A ⇸ (II ⊗ A)
  Λ⁻¹ a = よ (II ⊗ A , isSet× isSetUnit* ϕ) (tt* , a)

module _ (ASet@(A , ϕ) BSet@(B , ψ) CSet@(C , δ) : hSet ℓ) where
  α : ((A ⊗ B) ⊗ C) ⇸ (A ⊗ (B ⊗ C))
  α ((a , b) , c) = よ (A ⊗ (B ⊗ C) , isSet× ϕ (isSet× ψ δ)) (a , b , c)

  α⁻¹ : (A ⊗ (B ⊗ C)) ⇸ ((A ⊗ B) ⊗ C)
  α⁻¹ (a , (b , c)) = よ ((A ⊗ B) ⊗ C , isSet× (isSet× ϕ ψ) δ) ((a , b) , c)

module _ (ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ) where
  β : (A ⊗ B) ⇸ (B ⊗ A)
  β (a , b) = よ (B × A , isSet× ψ ϕ) (b , a)

  β⁻¹ : (B ⊗ A) ⇸ (A ⊗ B)
  β⁻¹ (b , a) = よ (A × B , isSet× ϕ ψ) (a , b)

_⊗₀_ : (ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ) → hSet ℓ
(A , ϕ) ⊗₀ (B , ψ) = A ⊗ B , isSet× ϕ ψ

_⊸_ : (A B : Type ℓ) → Type ℓ
A ⊸ B = A × B

_⊸₀_ : (ASet@(A , ϕ) BSet@(B , ψ) : hSet ℓ) → hSet ℓ
(A , ϕ) ⊸₀ (B , ψ) = A ⊸ B , isSet× ϕ ψ

module _ {A B C : Type ℓ} where

  κ : C ⊗ (A ⊸ B) → A ⊸ (C ⊗ B)
  κ (c , a , b) = a , c , b

  κ-equiv : isEquiv κ
  κ-equiv =
    isoToIsEquiv
      (iso κ (λ { (a , c , b) → c , a , b  })
             (λ { (c , a , b) → refl })
             (λ { (a , c , b) → refl }))

module _ {A B : Type ℓ} where

  _† :  A ⇸ B → B ⇸ A
  f † = λ b a → f a b

  †-equiv : isEquiv _†
  †-equiv =
    isoToIsEquiv
      (iso _† (λ f a b → f b a)
              (λ f → funExt (λ b → funExt (λ a → refl)))
              (λ f → funExt (λ a → funExt (λ b → refl))))

module _ {ASet@(A , ϕ) : hSet ℓ} where

  †-id : (idr ASet) † ≡ idr ASet
  †-id = TODO

module _ {A B C : Type ℓ} where

  †-⊚ : {f : A ⇸ B} {g : B ⇸ C} → (g ⊚ f) † ≡ f † ⊚ g †
  †-⊚ = TODO

module _ {A : Type ℓ} {BSet@(B , ϕ) : hSet ℓ} where

  _# : (A → B) → (A ⇸ B)
  f # = よ BSet ∘ f
