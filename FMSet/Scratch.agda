{-# OPTIONS --cubical #-}

module FMSet.Scratch where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.HITs.SetTruncation

infixr 20 _∷_

data FMSet (A : Type₀) : Type₀ where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  comm  : ∀ a b as bs cs
        → (p : as ≡ b ∷ cs)
        → (q : a ∷ cs ≡ bs)
        → a ∷ as ≡ b ∷ bs
  trunc : isSet (FMSet A)

pattern [_] x = x ∷ []

private
  variable
    ℓ : Level
    A : Type₀

swap : (x y : A) (xs : FMSet A)
     → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
swap x y xs = comm x y (y ∷ xs) (x ∷ xs) xs refl refl
-- swap y x xs = comm y x (x ∷ xs) (y ∷ xs) xs refl refl

module FMSetElim {B : FMSet A → Type ℓ}
  ([]* : B [])
  (_∷*_ : (x : A) {xs : FMSet A} → (b : B xs) → B (x ∷ xs))
  (comm* : (a b : A) {as bs cs : FMSet A} (bas : B as) (bbs : B bs) (bcs : B cs)
         → {p : as ≡ b ∷ cs} → (bp : PathP (λ i → B (p i)) bas (b ∷* bcs))
         → {q : a ∷ cs ≡ bs} → (bq : PathP (λ i → B (q i)) (a ∷* bcs) bbs)
         → PathP (λ i → B (comm a b as bs cs p q i)) (a ∷* bas) (b ∷* bbs))
  (trunc* : (xs : FMSet A) → isSet (B xs)) where

  f : (xs : FMSet A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm a b as bs cs p q i) =
    comm* a b (f as) (f bs) (f cs) (cong f p) (cong f q) i
  f (trunc xs zs p q i j) =
    elimSquash₀ trunc* (trunc xs zs p q) (f xs) (f zs) (cong f p) (cong f q) i j

module FMSetElimProp {B : FMSet A → Type ℓ} (BProp : {xs : FMSet A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → (p : B xs) → B (x ∷ xs)) where

  f : (xs : FMSet A) → B xs
  f = FMSetElim.f []* _∷*_
        (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq →
          toPathP (BProp (transp (λ i → B (comm a b as bs cs p q i)) i0 (a ∷* bas)) (b ∷* bbs)))
        (λ xs → isProp→isSet BProp)

module FMSetRec {B : Type ℓ} (BSet : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (a b : A) (bas bbs bcs : B)
         → (bp : bas ≡ b ∷* bcs)
         → (bq : a ∷* bcs ≡ bbs)
         → a ∷* bas ≡ b ∷* bbs) where

  f : FMSet A → B
  f = FMSetElim.f []* (λ x b → x ∷* b)
        (λ a b bas bbs bcs bp bq → comm* a b bas bbs bcs bp bq)
        (λ _ → BSet)

infixr 30 _++_

_++_ : ∀ (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm a b as bs cs p q i ++ ys =
  comm a b (as ++ ys) (bs ++ ys) (cs ++ ys)
       (cong (_++ ys) p) (cong (_++ ys) q) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

unitl-++ : ∀ (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : ∀ (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ = FMSetElimProp.f (trunc _ _)
  refl
  (λ x p → cong (x ∷_) p)

assoc-++ : ∀ (xs ys zs : FMSet A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ = FMSetElimProp.f (propPi (λ _ → propPi (λ _ → trunc _ _)))
  (λ ys zs → refl)
  (λ x p ys zs → cong (_∷_ x) (p ys zs))

cons-++ : ∀ (x : A) (xs : FMSet A) → x ∷ xs ≡ xs ++ [ x ]
cons-++ x = FMSetElimProp.f (trunc _ _)
  refl
  (λ y {xs} p → swap x y xs ∙ cong (_∷_ y) p)

comm-++ : ∀ (xs ys : FMSet A) → xs ++ ys ≡ ys ++ xs
comm-++ = FMSetElimProp.f (propPi (λ _ → trunc _ _))
  (λ ys → sym (unitr-++ ys))
  (λ x {xs} p ys → cong (x ∷_) (p ys)
                 ∙ cong (_++ xs) (cons-++ x ys)
                 ∙ sym (assoc-++ ys [ x ] xs))


record IsCMon (M : Type ℓ) : Type ℓ where
  field
    e : M
    _⊗_ : M → M → M
    comm-⊗ : ∀ x y → x ⊗ y ≡ y ⊗ x
    assoc-⊗ : ∀ x y z → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    unit-⊗ : ∀ x → e ⊗ x ≡ x
    MSet : isSet M

FMSetCMon : IsCMon (FMSet A)
FMSetCMon = record
              { e = []
              ; _⊗_ = _++_
              ; comm-⊗ = comm-++
              ; assoc-⊗ = assoc-++
              ; unit-⊗ = unitl-++
              ; MSet = trunc
              }

record IsCMonHom {M N : Type ℓ} (CM : IsCMon M) (CN : IsCMon N) : Type ℓ where
  open IsCMon CM renaming (e to eM ; _⊗_ to _⊗M_)
  open IsCMon CN renaming (e to eN ; _⊗_ to _⊗N_)
  field
    f : M → N
    f-e : f eM ≡ eN
    f-++ : ∀ x y → f (x ⊗M y) ≡ f x ⊗N f y
    f-sing : ∀ x → f (eM ⊗M x) ≡ eN ⊗N f x

module FMSetUniversal {M : Type ℓ} (C : IsCMon M) (f : A → M) where

  open IsCMon C

  f♯ : FMSet A → M
  f♯ = FMSetElim.f e (λ x m → f x ⊗ m)
                   (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq
                      → cong (f a ⊗_) bp
                      ∙ assoc-⊗ (f a) (f b) bcs
                      ∙ cong (_⊗ bcs) (comm-⊗ (f a) (f b))
                      ∙ sym (assoc-⊗ (f b) (f a) bcs) ∙ cong (f b ⊗_) bq)
                   (λ _ → MSet)

  f♯-nil : f♯ [] ≡ e
  f♯-nil = refl

  f♯-cons : ∀ x xs → f♯ (x ∷ xs) ≡ f x ⊗ f♯ xs
  f♯-cons x xs = refl

  f♯-sing : ∀ x → f♯ [ x ] ≡ f x
  f♯-sing x = comm-⊗ (f x) e ∙ unit-⊗ (f x)

  f♯-++ : ∀ xs ys → f♯ (xs ++ ys) ≡ f♯ xs ⊗ f♯ ys
  f♯-++ = FMSetElimProp.f (propPi λ _ → MSet _ _)
    (λ ys → sym (unit-⊗ (f♯ ys)))
    (λ x {xs} p ys → cong (f x ⊗_) (p ys) ∙ assoc-⊗ (f x) (f♯ xs) (f♯ ys))

  module _ (h : FMSet A → M) (h-nil : h [] ≡ e) (h-sing : ∀ x → h [ x ] ≡ f x)
           (h-++ : ∀ xs ys → h (xs ++ ys) ≡ h xs ⊗ h ys) where

    f♯-unique : h ≡ f♯
    f♯-unique = funExt (FMSetElimProp.f (MSet _ _)
      h-nil (λ x {xs} p → (h-++ [ x ] xs) ∙ cong (_⊗ h xs) (h-sing x) ∙ cong (f x ⊗_) p))

open import Cubical.Data.Nat

length : FMSet A → ℕ
length = FMSetRec.f isSetℕ 0 (λ _ → suc) λ a b bas bbs bcs bp bq → cong suc (bp ∙ bq)

singSet : Type₀ → Type₀
singSet A = Σ (FMSet A) (λ xs → 1 ≡ length xs)

is-sing-pred : FMSet A → A → Type₀
is-sing-pred xs z = [ z ] ≡ xs

is-sing-pred-prop : (xs : FMSet A) (z : A) → isProp (is-sing-pred xs z)
is-sing-pred-prop xs z = trunc [ z ] xs

is-sing : FMSet A → Type₀
is-sing xs = Σ _ (is-sing-pred xs)

is-sing-prop : (xs : FMSet A) → isProp (is-sing xs)
is-sing-prop xs (y , py) (z , pz) = ΣProp≡ (is-sing-pred-prop xs) {!!}

import Cubical.Data.Empty as D

lenZero-out : (xs : FMSet A) → 0 ≡ length xs → [] ≡ xs
lenZero-out = FMSetElimProp.f
  (propPi (λ _ → trunc _ _))
  (λ _ → refl)
  (λ x {xs} f p → D.⊥-elim (znots p))

lem1 : ∀ {a b as bs cs p q i} → 1 ≡ length (comm a b as bs cs p q i) → [] ≡ as
lem1 r = {!⊥-elim!}

lenOne-out : (xs : FMSet A) → 1 ≡ length xs → is-sing xs
lenOne-out = FMSetElim.f
  (λ p → D.⊥-elim (snotz p))
  (λ x {xs} f p → let q : 0 ≡ length xs ; q = injSuc p
                      r : [] ≡ xs ; r = lenZero-out xs q
                  in x , cong (x ∷_) r)
  (λ a b {as bs cs} fas fbs fcs {p} fp {q} fq → λ i r → {!!})
  {!!}

open import Cubical.Foundations.Logic

code : FMSet A → FMSet A → hProp
code [] [] = ⊤
code [] (y ∷ ys) = ⊥
code [] (comm a b as bs cs p q i) = ⊥
code [] (trunc ys zs p q i j) = {!!}
code (x ∷ xs) [] = ⊥
code (x ∷ xs) (y ∷ ys) = {!!}
code (x ∷ xs) (comm a b as bs cs p q i) = {!!}
code (x ∷ xs) (trunc ys zs p q i j) = {!!}
code (comm a b as bs cs p q i) ys = {!!}
code (trunc xs zs p q i j) ys = {!!}

test : FMSet A
test = []
