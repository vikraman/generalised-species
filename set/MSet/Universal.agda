{-# OPTIONS --cubical --exact-split --safe #-}

module set.MSet.Universal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import set.MSet

private
  variable
    ℓ ℓ₁ : Level
    A : Type ℓ

infixr 30 _++_

_++_ : ∀ (xs ys : MSet A) → MSet A
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys
swap x y xs i ++ ys = swap x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

abstract
  unitl-++ : (xs : MSet A) → [] ++ xs ≡ xs
  unitl-++ xs = refl

  unitr-++ : (xs : MSet A) → xs ++ [] ≡ xs
  unitr-++ = elimProp.f (trunc _ _)
    refl
    (λ x p → cong (x ::_) p)

  assoc-++ : (xs ys zs : MSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
  assoc-++ = elimProp.f (isPropΠ (λ _ → isPropΠ (λ _ → trunc _ _)))
    (λ ys zs → refl)
    (λ x p ys zs → cong (x ::_) (p ys zs))

  cons-++ : (x : A) (xs : MSet A) → x :: xs ≡ xs ++ [ x ]
  cons-++ x = elimProp.f (trunc _ _)
    refl
    (λ y {xs} p → swap x y xs ∙ cong (y ::_) p)

  comm-++ : (xs ys : MSet A) → xs ++ ys ≡ ys ++ xs
  comm-++ = elimProp.f (isPropΠ (λ _ → trunc _ _))
    (λ ys → sym (unitr-++ ys))
    (λ x {xs} p ys → cong (x ::_) (p ys)
                   ∙ cong (_++ xs) (cons-++ x ys)
                   ∙ sym (assoc-++ ys [ x ] xs))

module _ {a b : A} {as bs cs : MSet A} where

  commrel : (as ≡ b :: cs) → (a :: cs ≡ bs) → a :: as ≡ b :: bs
  commrel p q = cong (a ::_) p ∙ swap a b cs ∙ cong (b ::_) q

open import set.CMon using (CMon; CMonHom; CMonHom≡)

MSetCMon : (A : Type ℓ) → CMon (MSet A)
MSetCMon A = record
              { e = []
              ; _⊗_ = _++_
              ; comm-⊗ = comm-++
              ; assoc-⊗ = assoc-++
              ; unit-⊗ = unitl-++
              ; isSetM = trunc
              }

module univ {M : Type ℓ₁} (C : CMon M) (f : A → M) where

  open CMon C

  f♯ : MSet A → M
  f♯ = elim.f e (λ x m → f x ⊗ m) ϕ (λ _ → isSetM)
     where
       abstract ϕ : (x y : A) {xs : MSet A} (b : M) → (f x ⊗ (f y ⊗ b)) ≡ (f y ⊗ (f x ⊗ b))
                ϕ = (λ x y {xs} b → assoc-⊗ (f x) (f y) b
                  ∙ cong (_⊗ b) (comm-⊗ (f x) (f y))
                  ∙ sym (assoc-⊗ (f y) (f x) b))

  abstract
    f♯-nil : f♯ [] ≡ e
    f♯-nil = refl

    f♯-cons : ∀ x xs → f♯ (x :: xs) ≡ f x ⊗ f♯ xs
    f♯-cons x xs = refl

    f♯-sing : ∀ x → f♯ [ x ] ≡ f x
    f♯-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

    f♯-++ : ∀ xs ys → f♯ (xs ++ ys) ≡ f♯ xs ⊗ f♯ ys
    f♯-++ = elimProp.f (isPropΠ λ _ → isSetM _ _)
      (λ ys → sym (unit-⊗ (f♯ ys)))
      (λ x {xs} p ys → cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f♯ xs) (f♯ ys))

  module _ (h : MSet A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    abstract
      f♯-htpy : ∀ xs → h xs ≡ f♯ xs
      f♯-htpy = elimProp.f (isSetM _ _)
        h-nil (λ x {xs} p → h-++ [ x ] xs ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p)

      f♯-unique : f♯ ≡ h
      f♯-unique = sym (funExt f♯-htpy)

univ : ∀ {ℓ₁} {ℓ₂} (A : Type ℓ₁) {M : Type ℓ₂} (CM : CMon M) → CMonHom (MSetCMon A) CM ≃ (A → M)
univ A {M} CM = isoToEquiv (iso q p q-p p-q)
  where module C = CMon CM ; module u = univ CM
        p : (A → M) → CMonHom (MSetCMon A) CM
        p f = u.f♯ f , u.f♯-nil f , u.f♯-++ f
        q : CMonHom (MSetCMon A) CM → (A → M)
        q (h , h-e , h-⊗) = h ∘ [_]
        abstract
          q-p : (f : A → M) → q (p f) ≡ f
          q-p f = funExt (λ x → C.unitr-⊗ (f x))
          p-q : (h : CMonHom (MSetCMon A) CM) → p (q h) ≡ h
          p-q (h , h-nil , h-++) = CMonHom≡ {CM = MSetCMon A} {CN = CM} (u.f♯-unique (h ∘ [_]) h h-nil (λ _ → refl) h-++)

univ-htpy : ∀ {ℓ} {A : Type ℓ} → (h : CMonHom (MSetCMon A) (MSetCMon A)) (p : ∀ x → h .fst ([ x ]) ≡ [ x ]) → ∀ xs → h .fst xs ≡ xs
univ-htpy {A = A} (h , h-nil , h-++) h-sing xs = h~η♯ xs ∙ η♯~id xs
  where
    abstract
      h~η♯ : ∀ xs → h xs ≡ univ.f♯ (MSetCMon A) [_] xs
      h~η♯ = univ.f♯-htpy (MSetCMon A) [_] h h-nil h-sing h-++
      η♯~id : ∀ xs → univ.f♯ (MSetCMon A) [_] xs ≡ xs
      η♯~id xs i = univ.f♯-htpy (MSetCMon A) [_] (idfun _) refl (λ _ → refl) (λ _ _ → refl) xs (~ i)
