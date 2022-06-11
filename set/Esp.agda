{-# OPTIONS --cubical --exact-split --no-import-sorts --allow-unsolved-metas #-}

module set.Esp where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (id ; curry ; uncurry)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Agda.Primitive

open import set.Prelude
open import set.MSet
open import set.MSet.Universal

private
  variable
    ℓ : Level

infixr 10 _⇸_ _↝_

_⇸_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⇸ B = A × B → hProp _

よ : (ASet@(A , ϕ) : hSet ℓ) → A → (A → hProp _)
よ (A , ϕ) a = λ x → (a ≡ x) , ϕ a x

_↝_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ↝ B = MSet A ⇸ B

open import set.CMon using (CMon)
import Cubical.Functions.Logic as L

hPropCMon : ∀ {ℓ} → CMon (hProp ℓ)
CMon.e hPropCMon = Unit* , λ { tt* tt* → refl }
CMon._⊗_ hPropCMon = L._⊓_
CMon.unit-⊗ hPropCMon = λ { X → L.⇔toPath snd λ x → tt* , x }
CMon.comm-⊗ hPropCMon = L.⊓-comm
CMon.assoc-⊗ hPropCMon = L.⊓-assoc
CMon.isSetM hPropCMon = isSetHProp

module _ (M : Type ℓ) {CM : CMon M} where
  open CMon CM

  hProp^CMon : CMon (M → hProp ℓ)
  CMon.e hProp^CMon = よ (M , isSetM) e
  CMon._⊗_ hProp^CMon = λ p q → λ m → L.∃[ m₁ ∶ M ] L.∃[ m₂ ∶ M ] p m₁ L.⊓ q m₂ L.⊓ ((m ≡ m₁ ⊗ m₂) , isSetM _ _)
  CMon.unit-⊗ hProp^CMon = TODO
  CMon.comm-⊗ hProp^CMon = TODO
  CMon.assoc-⊗ hProp^CMon = TODO
  CMon.isSetM hProp^CMon = isSetΠ (λ _ → isSetHProp)

module _ {A B : Type ℓ} (f : A ↝ B) where

  _^ : B → (MSet A → hProp _)
  _^ b α = f (α , b)

  _^♯ : MSet B × MSet A → hProp _
  _^♯ (β , α) = univ.f♯ (hProp^CMon (MSet A) {MSetCMon A}) _^ β α

ids : {A : Type ℓ} → A ↝ A
ids (α , a) = よ (MSet _ , trunc) α [ a ]

module _ {A B C : Type ℓ} where
  infixr 10 _⊚_
  _⊚_ : B ↝ C → A ↝ B → A ↝ C
  g ⊚ f = λ { (α , c) → L.∃[ β ∶ MSet B ] (f ^♯) (β , α) L.⊓ g (β , c) }

![_] : {A : Type ℓ} → A ↝ Lift ⊥
![ () ]

module _ {A B C : Type ℓ} where
  s⟨_,_⟩ : A ↝ B → A ↝ C → A ↝ B ⊎ C
  s⟨ p , q ⟩ (α , inl b) = p (α , b)
  s⟨ p , q ⟩ (α , inr c) = q (α , c)

module _ {A B : Type ℓ} where

  π₁ : A ⊎ B ↝ A
  π₁ (γ , a) = よ (MSet _ , trunc) [ inl a ] γ

  π₂ : A ⊎ B ↝ B
  π₂ (γ , b) = よ (MSet _ , trunc) [ inr b ] γ

module _ {A B C : Type ℓ} where

  eqv : (f : A ↝ B ⊎ C) → s⟨ π₁ ⊚ f , π₂ ⊚ f ⟩ ≡ f
  eqv f = funExt h
    where h : (x : MSet A × (B ⊎ C)) → s⟨ π₁ ⊚ f , π₂ ⊚ f ⟩ x ≡ f x
          h (α , inl b) = (π₁ ⊚ f) (α , b)
                        ≡⟨ refl ⟩
                          (L.∃[ β ∶ MSet (B ⊎ C) ] (f ^♯) (β , α) L.⊓ π₁ (β , b))
                        ≡⟨ TODO ⟩
                          f (α , inl b)
                        ∎
          h (α , inr c) = TODO

open import set.Monoidal using (mmap ; f ; g)

module _ {A B : Type ℓ} where

  ev : (MSet A × B) ⊎ A ↝ B
  ev (x , b) = let (y , α) = f x in よ (MSet _ , trunc) [ (α , b) ] y

module _ {A B C : Type ℓ} where

  currys : (C ⊎ A) ↝ B → C ↝ (MSet A × B)
  currys p (γ , α , b) = p (g (γ , α) , b)

  uncurrys : C ↝ (MSet A × B) → (C ⊎ A) ↝ B
  uncurrys p (x , b) = let (γ , α) = f x in p (γ , α , b)

module _ {A B : Type ℓ} where

  ι : (A × B) ↝ (MSet A × B)
  ι (x , α , b) = L.∃[ a ∶ A ] よ (MSet _ , trunc) [ a , b ] x L.⊓ よ (MSet _ , trunc) [ a ] α

module _ {A B C : Type ℓ} where

  _~ : C ↝ (A × B) → (C ⊎ A) ↝ B
  (p ~) (x , b) = TODO 
