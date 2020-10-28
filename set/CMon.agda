{-# OPTIONS --cubical --safe #-}

module set.CMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Agda.Primitive

record CMon {ℓ} (M : Type ℓ) : Type ℓ where
  field
    e : M
    _⊗_ : M → M → M
    unit-⊗ : ∀ x → e ⊗ x ≡ x
    comm-⊗ : ∀ x y → x ⊗ y ≡ y ⊗ x
    assoc-⊗ : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    isSetM : isSet M

  unitr-⊗ : ∀ x → x ⊗ e ≡ x
  unitr-⊗ x = comm-⊗ x e ∙ unit-⊗ x

module _ {ℓ₁ ℓ₂} {M : Type ℓ₁} {N : Type ℓ₂} (CM : CMon M) (CN : CMon N) where

  module M = CMon CM ; module N = CMon CN

  isCMonHom : (M → N) → Type (ℓ₁ ⊔ ℓ₂)
  isCMonHom f = (f M.e ≡ N.e) × (∀ x y → f (x M.⊗ y) ≡ (f x N.⊗ f y))

  isCMonHomProp : (f : M → N) → isProp (isCMonHom f)
  isCMonHomProp f = isPropΣ (N.isSetM (f M.e) N.e) λ _ → isPropΠ λ _ → isPropΠ (λ _ → N.isSetM _ _)

  CMonHom : Type (ℓ₁ ⊔ ℓ₂)
  CMonHom = Σ (M → N) isCMonHom

CMonHom≡ : ∀ {ℓ₁ ℓ₂} {M : Type ℓ₁} {N : Type ℓ₂} {CM : CMon M} {CN : CMon N} {H1 H2 : CMonHom CM CN}
         → (p : H1 .fst ≡ H2 .fst)
         → H1 ≡ H2
CMonHom≡ {CM = CM} {CN} = Σ≡Prop (λ f → isCMonHomProp CM CN f)

CMonHom∘ : ∀ {ℓ₁ ℓ₂ ℓ₃} {M : Type ℓ₁} {N : Type ℓ₂} {O : Type ℓ₃}
         → (CM : CMon M) (CN : CMon N) (CO : CMon O)
         → CMonHom CN CO → CMonHom CM CN → CMonHom CM CO
CMonHom∘ _ _ _ (g , g-e , g-⊗) (f , f-e , f-⊗) = g ∘ f , cong g f-e ∙ g-e , λ x y → cong g (f-⊗ x y) ∙ g-⊗ (f x) (f y)

data Free {ℓ} (A : Type ℓ) : Type ℓ where
  η : A → Free A
  e : Free A
  _⊗_ : Free A → Free A → Free A
  unit : ∀ x → e ⊗ x ≡ x
  comm : ∀ x y → x ⊗ y ≡ y ⊗ x
  assoc : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
  trunc : isSet (Free A)

module elim {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Free A → Type ℓ₂}
  (η* : (x : A) → B (η x))
  (e* : B e)
  (_⊗*_ : ∀ {m₁ m₂} (b₁ : B m₁) (b₂ : B m₂) → B (m₁ ⊗ m₂))
  (unit* : ∀ {m} → (b : B m) → PathP (λ i → B (unit m i)) (e* ⊗* b) b)
  (comm* : ∀ {m₁ m₂} → (b₁ : B m₁) (b₂ : B m₂) → PathP (λ i → B (comm m₁ m₂ i)) (b₁ ⊗* b₂) (b₂ ⊗* b₁))
  (assoc* : ∀ {m₁ m₂ m₃} → (b₁ : B m₁) (b₂ : B m₂) (b₃ : B m₃) → PathP (λ i → B (assoc m₁ m₂ m₃ i)) (b₁ ⊗* (b₂ ⊗* b₃)) ((b₁ ⊗* b₂) ⊗* b₃))
  (trunc* : (m : Free A) → isSet (B m))
  where

  f : (m : Free A) → B m
  f (η x) = η* x
  f e = e*
  f (m₁ ⊗ m₂) = f m₁ ⊗* f m₂
  f (unit m i) = unit* (f m) i
  f (comm m₁ m₂ i) = comm* (f m₁) (f m₂) i
  f (assoc m₁ m₂ m₃ i) = assoc* (f m₁) (f m₂) (f m₃) i
  f (trunc m₁ m₂ p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f m₁) (f m₂) (cong f p) (cong f q) (trunc m₁ m₂ p q) i j

module elimProp {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Free A → Type ℓ₂} (BProp : {m : Free A} → isProp (B m))
  (η* : (x : A) → B (η x))
  (e* : B e)
  (_⊗*_ : ∀ {m₁ m₂} (b₁ : B m₁) (b₂ : B m₂) → B (m₁ ⊗ m₂))
  where

  f : (m : Free A) → B m
  f = elim.f η* e* _⊗*_
             (λ {m} b → toPathP (BProp (transp (λ i → B (unit m i)) i0 (e* ⊗* b)) b))
             (λ {m₁} {m₂} b₁ b₂ → toPathP (BProp (transp (λ i → B (comm m₁ m₂ i)) i0 (b₁ ⊗* b₂)) (b₂ ⊗* b₁)))
             (λ {m₁} {m₂} {m₃} b₁ b₂ b₃ → toPathP (BProp (transp (λ i → B (assoc m₁ m₂ m₃ i)) i0 (b₁ ⊗* (b₂ ⊗* b₃))) ((b₁ ⊗* b₂) ⊗* b₃)))
             (λ _ → isProp→isSet BProp)

open CMon

FreeCMon : ∀ {ℓ} (A : Type ℓ) → CMon (Free A)
CMon.e (FreeCMon A) = Free.e
CMon._⊗_ (FreeCMon A) = Free._⊗_
unit-⊗ (FreeCMon A) = unit
assoc-⊗ (FreeCMon A) = assoc
comm-⊗ (FreeCMon A) = comm
isSetM (FreeCMon A) = trunc

module univ {ℓ₁} {M : Type ℓ₁} (C : CMon M) {ℓ₂} {A : Type ℓ₂} (f : A → M) where
  module C = CMon C

  f♯ : Free A → M
  f♯ = elim.f f C.e (λ m₁ m₂ → m₁ C.⊗ m₂) C.unit-⊗ C.comm-⊗ C.assoc-⊗ λ _ → C.isSetM

  f♯-e : f♯ Free.e ≡ C.e
  f♯-e = refl

  f♯-η : f♯ ∘ η ≡ f
  f♯-η = refl

  f♯-⊗ : ∀ m₁ m₂ → f♯ (m₁ Free.⊗ m₂) ≡ (f♯ m₁) C.⊗ (f♯ m₂)
  f♯-⊗ m₁ m₂ = refl

  module _ (h : Free A → M)
           (h-η : ∀ m → h (η m) ≡ f m)
           (h-e : h Free.e ≡ C.e)
           (h-⊗ : ∀ m₁ m₂ → h (m₁ Free.⊗ m₂) ≡ (h m₁) C.⊗ (h m₂)) where

    f♯-unique : f♯ ≡ h
    f♯-unique = sym (funExt p)
      where p : (m : Free A) → h m ≡ f♯ m
            p = elimProp.f (λ {m} → C.isSetM (h m) (f♯ m)) h-η h-e
                           (λ {m₁} {m₂} p q → h-⊗ m₁ m₂ ∙ cong (C._⊗ h m₂) p ∙ cong ((f♯ m₁) C.⊗_) q)

univ : ∀ {ℓ₁} {ℓ₂} (A : Type ℓ₁) {M : Type ℓ₂} (CM : CMon M) → CMonHom (FreeCMon A) CM ≃ (A → M)
univ A {M} CM = isoToEquiv (iso q p q-p p-q)
  where module C = CMon CM ; module u = univ CM
        p : (A → M) → CMonHom (FreeCMon A) CM
        p f = u.f♯ f , u.f♯-e f , u.f♯-⊗ f
        q : CMonHom (FreeCMon A) CM → (A → M)
        q (h , h-e , h-⊗) = h ∘ η
        q-p : (f : A → M) → q (p f) ≡ f
        q-p f = refl
        p-q : (h : CMonHom (FreeCMon A) CM) → p (q h) ≡ h
        p-q (h , h-e , h-⊗) = CMonHom≡ {CM = FreeCMon A} {CN = CM} (u.f♯-unique (h ∘ η) h (λ _ → refl) h-e h-⊗)

univ-η : ∀ {ℓ} (A : Type ℓ) → univ.f♯ (FreeCMon A) η ≡ idfun (Free A)
univ-η A = funExt p
  where p : (x : Free A) → univ.f♯ (FreeCMon A) η x ≡ idfun (Free A) x
        p = elimProp.f (trunc _ _) (λ _ → refl) refl (λ p q → cong (Free._⊗ _) p ∙ cong (_ Free.⊗_) q)

open import set.Monad

-- FreeCMonMonad : ∀ {ℓ} → Monad {ℓ} Free
-- Monad.map FreeCMonMonad f = univ.f♯ (FreeCMon _) λ a → Free.η (f a)
-- Monad.η FreeCMonMonad = Free.η
-- FreeCMonMonad Monad.* = univ.f♯ (FreeCMon _)
-- Monad.unitl FreeCMonMonad = univ-η _
-- Monad.unitr FreeCMonMonad = univ.f♯-η (FreeCMon _)
-- Monad.assoc FreeCMonMonad f g = funExt (elimProp.f (trunc _ _) (λ _ → refl) refl λ p q → {!!})
