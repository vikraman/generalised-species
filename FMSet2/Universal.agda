{-# OPTIONS --cubical --safe #-}

module FMSet2.Universal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import FMSet2

private
  variable
    ℓ : Level
    A : Type₀

infixr 30 _++_

_++_ : ∀ (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
swap x y xs i ++ ys = swap x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : ∀ (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : ∀ (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ = FMSetElimProp.f (trunc _ _)
  refl
  (λ x p → cong (_∷_ x) p)

assoc-++ : ∀ (xs ys zs : FMSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = FMSetElimProp.f (propPi (λ _ → propPi (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (_∷_ x) (p ys zs))

■ : (xs ys zs : FMSet A) → xs ≡ ys → ys ≡ zs → xs ≡ zs
■ xs ys zs p q i = hcomp (λ j → λ { (i = i0) → xs ; (i = i1) → q j }) (p i)

-- x ∷ y ∷ xs ----> y ∷ (xs ++ [ x ])
--     |                |
--     |                | y ∷ p j
--     V                V
-- x ∷ y ∷ xs ----> y ∷ x ∷ xs
--         swap x y xs i

cons-++ : ∀ (x : A) (xs : FMSet A) → x ∷ xs ≡ xs ++ [ x ]
cons-++ x = FMSetElimProp.f (trunc _ _)
  refl
  (λ y {xs} p i → hcomp (λ j → λ { (i = i0) → x ∷ y ∷ xs
                                 ; (i = i1) → y ∷ p j })
                        (swap x y xs i))

-- [] ++ ys = ys ----> ys ++ []

-- x ∷ (xs ++ ys) ----> ys ++ (x ∷ xs)
--      |                    |
--      |                    |
--      |                    V
--      |               ys ++ (xs ++ [ x ])
--      |                    |
--      |                    |
--      V                    V
-- x ∷ (ys ++ xs) ----> (ys ++ xs) ++ [ x ]

-- right : ∀ (ys : FMSet A) (x : A) (xs : FMSet A) → ys ++ (x ∷ xs) ≡ (ys ++ xs) ++ [ x ]
-- right ys x xs j = hcomp (λ k → λ { (j = i0) → ys ++ (x ∷ xs) ; (j = i1) → assoc-++ ys xs [ x ] k }) (ys ++ (cons-++ x xs j))

comm-++ : ∀ (xs ys : FMSet A) → xs ++ ys ≡ ys ++ xs
comm-++ = FMSetElimProp.f (propPi (λ _ → trunc _ _))
  (λ ys i → unitr-++ ys (~ i))
  (λ x {xs} p ys i → hcomp (λ j → λ { (i = i0) → x ∷ p ys (~ j)
                                    ; (i = i1) → hcomp (λ k → λ { (j = i0) → assoc-++ ys xs [ x ] k
                                                                ; (j = i1) → ys ++ (x ∷ xs)
                                                                })
                                                       (ys ++ (cons-++ x xs (~ j)))
                                    })
                           (cons-++ x (ys ++ xs) i)
    -- hcomp (λ j → λ { (i = i0) → (x ∷ xs ++ ys)
    --                ; (i = i1) →
    --                  hcomp (λ k → λ { (j = i0) → (x ∷ ys ++ xs)
    --                                 ; (j = i1) → assoc-++ ys [ x ] xs (~ k) })
    --                        (cons-++ x ys j ++ xs) })
    --       (x ∷ p ys i)
          )

                 -- cong (x ∷_) (p ys)
                 -- ∙ cong (_++ xs) (cons-++ x ys)
                 -- ∙ sym (assoc-++ ys [ x ] xs)


open import CMon

FMSetCMon : CMon (FMSet A)
FMSetCMon = record
              { e = []
              ; _⊗_ = _++_
              ; comm-⊗ = comm-++
              ; assoc-⊗ = assoc-++
              ; unit-⊗ = unitl-++
              ; MSet = trunc
              }

module FMSetUniversal {M : Type ℓ} (C : CMon M) (f : A → M) where

  open CMon.CMon C

  f♯ : FMSet A → M
  f♯ = FMSetRec.f MSet e (λ x m → f x ⊗ m)
         (λ x y m i → hcomp (λ j → λ { (i = i0) → assoc-⊗ (f x) (f y) m (~ j)
                                     ; (i = i1) → assoc-⊗ (f y) (f x) m (~ j) })
                            (comm-⊗ (f x) (f y) i ⊗ m))

  f♯-nil : f♯ [] ≡ e
  f♯-nil = refl

  f♯-cons : ∀ x xs → f♯ (x ∷ xs) ≡ f x ⊗ f♯ xs
  f♯-cons x xs = refl

  f♯-sing : ∀ x → f♯ [ x ] ≡ f x
  f♯-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

  f♯-++ : ∀ xs ys → f♯ (xs ++ ys) ≡ f♯ xs ⊗ f♯ ys
  f♯-++ = FMSetElimProp.f (propPi λ _ → MSet _ _)
    (λ ys → sym (unit-⊗ (f♯ ys)))
    (λ x {xs} p ys i → hcomp (λ j → λ { (i = i0) → f x ⊗ p ys (~ j)
                                      ; (i = i1) → (f x ⊗ f♯ xs) ⊗ f♯ ys })
                             (assoc-⊗ (f x) (f♯ xs) (f♯ ys) i)
      -- cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f♯ xs) (f♯ ys)
    )

  module _ (h : FMSet A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    f♯-unique : h ≡ f♯
    f♯-unique = funExt (FMSetElimProp.f (MSet _ _)
      h-nil (λ x {xs} p → (h-++ [ x ] xs) ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p))
