{-# OPTIONS --cubical --exact-split --safe #-}

open import Cubical.Data.Nat using (ℕ ; suc)

module set.nPSh (n : ℕ) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

private
  variable
    ℓ : Level

PSh : Type ℓ → Type (ℓ-suc ℓ)
PSh {ℓ} X = X → TypeOfHLevel ℓ n

nPSh : TypeOfHLevel ℓ (suc n) → TypeOfHLevel (ℓ-suc ℓ) (suc n)
nPSh {ℓ} (X , ϕ) = PSh X , isOfHLevelΠ (suc n) λ _ → isOfHLevelTypeOfHLevel n

η : {A@(A , ϕ) : TypeOfHLevel ℓ (suc n)} → A → PSh A
η {A = (A , ϕ)} a = λ b → (a ≡ b) , isOfHLevelPath' n ϕ a b

_* : {A@(A , ϕ) : TypeOfHLevel ℓ n} {B : Type ℓ} → (A → PSh B) → PSh A → PSh B
_* {A = (A , ϕ)} {B} f = λ X b → (Σ _ λ a → f a b .fst × X a .fst) , isOfHLevelΣ n ϕ λ a → isOfHLevel× n (f a b .snd) (X a .snd )

map : {A@(A , ϕ) : TypeOfHLevel ℓ n} {B@(B , ψ) : TypeOfHLevel ℓ (suc n)} → (A → B) → PSh A → PSh B
map {A = A} {(B , ψ)} f = _* {A = A} {B = B} (η {A = B , ψ} ∘ f)

unitl : {A@(A , ϕ) : TypeOfHLevel ℓ n} → η * ≡ idfun (PSh A)
unitl {A = (A , ϕ)} = funExt λ X → funExt λ b → h X b
  where h : (X : PSh A) (b : A)
          → (Σ A (λ a → (a ≡ b) × X a .fst) , isOfHLevelΣ n ϕ λ a → isOfHLevel× n (isOfHLevelPath' n (isOfHLevelSuc n ϕ) a b) (X a .snd)) ≡ X b
        h X b = Σ≡Prop (λ _ → isPropIsOfHLevel n) (ua (isoToEquiv (iso f g f-g g-f)))
          where f : (Σ A (λ a → Σ (a ≡ b) (λ _ → X a .fst))) → X b .fst
                f (a , p , z) = transp (λ i → X (p i) .fst) i0 z
                g : X b .fst → (Σ A (λ a → Σ (a ≡ b) (λ _ → X a .fst)))
                g z = b , refl , z
                f-g : ∀ z → f (g z) ≡ z
                f-g z i = transp (λ _ → X b .fst) i z
                g-f : ∀ z → g (f z) ≡ z
                g-f (a , p , z) i = p (~ i) , (λ j → p (~ i ∨ j)) , transp (λ j → X (p (~ i ∧ j)) .fst) i z

unitr : {A@(A , ϕ) B@(B , ψ) : TypeOfHLevel ℓ n} → (f : A → PSh B) → f * ∘ η ≡ f
unitr {A = (A , ϕ)} {(B , ψ)} f = funExt λ a → funExt λ b → h a b
  where h : (a : A) (b : B)
          → (Σ A (λ x → (f x b .fst) × (a ≡ x)) , isOfHLevelΣ n ϕ λ a → isOfHLevel× n (f a b .snd) (isOfHLevelPath' n (isOfHLevelSuc n ϕ) _ a)) ≡ f a b
        h a b = Σ≡Prop (λ _ → isPropIsOfHLevel n) (ua (isoToEquiv (iso t s t-s s-t)))
          where t : Σ A (λ x → f x b .fst × (a ≡ x)) → f a b .fst
                t (x , z , p) = transp (λ i → f (p (~ i)) b .fst) i0 z
                s : f a b .fst → Σ A (λ x → f x b .fst × (a ≡ x))
                s z = a , z , refl
                t-s : ∀ z → t (s z) ≡ z
                t-s z i = transp (λ _ → f a b .fst) i z
                s-t : ∀ z → s (t z) ≡ z
                s-t (x , z , p) i = p i , transp (λ j → f (p (i ∨ ~ j)) b .fst) i z , λ j → p (i ∧ j)

assoc : {A@(A , ϕ) B@(B , ψ) C@(C , χ) : TypeOfHLevel ℓ n} (f : A → PSh B) (g : B → PSh C) → g * ∘ f * ≡ (g * ∘ f) *
assoc {A = (A , ϕ)} {(B , ψ)} {(C , χ)} f g = funExt λ X → funExt λ c → h X c
  where h : (X : PSh A) (c : C)
          → (Σ B (λ b → (g b c .fst) × (Σ A (λ a → (f a b .fst) × (X a .fst)))) , isOfHLevelΣ n ψ (λ b → isOfHLevel× n (g b c .snd) (isOfHLevelΣ n ϕ (λ a → isOfHLevel× n (f a b .snd) (X a .snd)))))
          ≡ (Σ A (λ a → (Σ B (λ b → (g b c .fst) × (f a b .fst))) × (X a .fst)) , isOfHLevelΣ n ϕ (λ a → isOfHLevelΣ n (isOfHLevelΣ n ψ (λ b → isOfHLevel× n (g b c .snd) (f a b .snd))) (λ _ → X a .snd)))
        h X c = Σ≡Prop (λ _ → isPropIsOfHLevel n) (ua (isoToEquiv (iso t s t-s s-t)))
          where t : Σ B (λ b → (g b c .fst) × (Σ A (λ a → (f a b .fst) × (X a .fst)))) → Σ A (λ a → (Σ B (λ b → (g b c .fst) × (f a b .fst))) × (X a .fst))
                t (b , u , a , v , w) = a , (b , u , v) , w
                s : Σ A (λ a → (Σ B (λ b → (g b c .fst) × (f a b .fst))) × (X a .fst)) → Σ B (λ b → (g b c .fst) × (Σ A (λ a → (f a b .fst) × (X a .fst))))
                s (a , (b , u , v) , w) = b , u , a , v , w
                t-s : ∀ z → t (s z) ≡ z
                t-s (a , (b , u , v) , w) = refl
                s-t : ∀ z → s (t z) ≡ z
                s-t (b , u , a , v , w) = refl

open import set.Monad

-- nPshRMonad : ∀ {ℓ} → RMonad {ℓ} PSh
-- RMonad.map nPshRMonad = {!!}
-- RMonad.η nPshRMonad = {!!}
-- nPshRMonad RMonad.* = {!!}
-- RMonad.unitl nPshRMonad = {!!}
-- RMonad.unitr nPshRMonad = {!!}
-- RMonad.assoc nPshRMonad = {!!}
