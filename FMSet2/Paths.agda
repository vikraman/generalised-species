{-# OPTIONS --cubical #-}

module FMSet2.Paths where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import FMSet2
open import FMSet2.Universal

private
  variable
    A B : Type₀
    ASet : isSet A
    a x : A
    xs ys : FMSet A

disj-nil-cons : x ∷ xs ≡ [] → ⊥
disj-nil-cons p = transport (λ i → fst (code (p i))) tt
  where code : FMSet A → hProp ℓ-zero
        code = FMSetRec.f isSetHProp
          (⊥ , isProp⊥)
          (λ _ _ → Unit , isPropUnit)
          (λ _ _ _ _ → Unit , isPropUnit)

disj-cons-nil : [] ≡ x ∷ xs → ⊥
disj-cons-nil p = disj-nil-cons (sym p)

length : FMSet A → ℕ
length = FMSetRec.f isSetℕ 0 (λ _ → suc) (λ _ _ _ → refl)

-- lenOneSet : Type₀ → Type₀
-- lenOneSet A = Σ (FMSet A) (λ xs → length xs ≡ 1)

-- sing=isProp : ∀ {x y : A} → isProp ([ x ] ≡ [ y ])
-- sing=isProp {x = x} {y = y} = trunc [ x ] [ y ]

-- sing=-in : ∀ {x y : A} → x ≡ y → [ x ] ≡ [ y ]
-- sing=-in p i = [ p i ]

-- sing=isContr : ∀ {x y : A} → x ≡ y → isContr ([ x ] ≡ [ y ])
-- sing=isContr p = sing=-in p , sing=isProp (sing=-in p)

-- is-sing : FMSet A → Type₀
-- is-sing xs = Σ _ (λ z → [ z ] ≡ xs)

-- lenZero-out : (xs : FMSet A) → length xs ≡ 0 → [] ≡ xs
-- lenZero-out = FMSetElimProp.f
--   (propPi (λ _ → trunc _ _))
--   (λ _ → refl)
--   (λ x {xs} f p → ⊥-elim (znots (sym p)))

-- test : ∀ {X : Type₀} {x y : X} → Path (⊥ → X) (λ p → x) (λ p → y)
-- test = funExt (λ x → ⊥-elim x)

-- test2 : ∀ (x y : A) xs i → length (comm x y xs i) ≡ 1 → ⊥
-- test2 x y xs i p = snotz (injSuc p)

-- lenOne-out : (xs : FMSet A) → length xs ≡ 1 → is-sing xs
-- lenOne-out = FMSetElim.f
--   (λ p → ⊥-elim (znots p))
--   (λ x {xs} f p → let q : length xs ≡ 0; q = injSuc p
--                       r : [] ≡ xs ; r = lenZero-out xs q
--                   in x , (cong (x ∷_) r))
--   (λ x y {xs} b → toPathP ({!!}
--                          ∙ {!!}
--                          ∙ (funExt (λ p → ⊥-elim (test2 x y xs i1 p)))))
--   {!!}

-- is-sing-isProp : {xs : FMSet A} → isProp (is-sing xs)
-- is-sing-isProp (x , p) (y , q) = {!!}

-- sing-is-sing : (x : A) → is-sing [ x ]
-- sing-is-sing x = x , refl

-- singSet : Type₀ → Type₀
-- singSet A = Σ (FMSet A) is-sing

-- singSet= : (x y : singSet A) → Type₀
-- singSet= x y = x ≡ y

-- sing-out : (x y : singSet A) → x ≡ y → fst (snd x) ≡ fst (snd y)
-- sing-out (xs , (x , p)) (ys , (y , q)) r i = fst (snd (r i))

-- sing-is-inj' : ∀ (x y : A) → [ x ] ≡ [ y ] → x ≡ y
-- sing-is-inj' x y p = sing-out ([ x ] , sing-is-sing x) ([ y ] , sing-is-sing y) {!!}

-- head : singSet A → A
-- head (xs , a , p) = a

-- sing-out' : (x y : singSet A) → x ≡ y → head x ≡ head y
-- sing-out' x y p = λ i → head (p i)

-- sing-is-inj : (x a : A) → [ x ] ≡ [ a ] → head ([ x ] , sing-is-sing x) ≡ head ([ a ] , sing-is-sing a)
-- sing-is-inj x a = J (λ y q → x ≡ head (y , {!!} , {!!})) {!!}

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
import Cubical.Foundations.Logic as hProp

lenZero-out : (xs : FMSet A) → 0 ≡ length xs → [] ≡ xs
lenZero-out = FMSetElimProp.f
  (propPi (λ _ → trunc _ _))
  (λ _ → refl)
  (λ x {xs} f p → D.⊥-elim (znots p))

test : ∀ {X : Type₀} {x y : X} → Path (⊥ → X) (λ _ → x) (λ _ → y)
test = funExt (λ x → ⊥-elim x)

test2 : ∀ (x y : A) xs i → (1 ≡ length (FMSet.swap x y xs i)) → ⊥
test2 x y xs i p = znots (injSuc p)

test3 : ∀ (x y : A) xs i → (1 ≡ length (FMSet.swap x y xs i)) ≡ ⊥
test3 x y xs i = {!!}

test4 : ∀ {X : Type₀} {x y : X} {P : I → Type₀} (p : ∀ i → P i → ⊥) → PathP (λ i → P i → X) (λ q → x) (λ q → y)
test4 {X} {x} {y} {P} p = toPathP {!!}

test5 : ∀ (x y : A) xs (X : Type₀) (z w : X) → PathP (λ i → 1 ≡ length (FMSet.swap x y xs i) → X) (λ p → z) (λ p → w)
test5 x y xs Z z w = {!!}

-- PathP
--       (λ i → 1 ≡ length (comm x y xs i) → is-sing (comm x y xs i))
--       (λ p → x , (λ i → x ∷ lenZero-out (y ∷ xs) (injSuc p) i))
--       (λ p → y , (λ i → y ∷ lenZero-out (x ∷ xs) (injSuc p) i))

lenOne-out : (xs : FMSet A) → 1 ≡ length xs → is-sing xs
lenOne-out = FMSetElim.f
  (λ p → D.⊥-elim (snotz p))
  (λ x {xs} f p → let q : 0 ≡ length xs ; q = injSuc p
                      r : [] ≡ xs ; r = lenZero-out xs q
                  in x , cong (x ∷_) r)
  (λ x y {xs} f → {!!})
  {!!}

-- toPathP (cong (transp (λ i → 1 ≡ length (comm x y xs i) → is-sing (comm x y xs i)) i0) (funExt (λ p → ⊥-elim (znots (injSuc p))))
                  --         ∙ {!!}
                  --         ∙ funExt (λ p → ⊥-elim (znots (injSuc p))))

module _ {ASet : isSet A} where

  infixr 15 _∈_

  _∈_ : A → FMSet A → hProp ℓ-zero
  _∈_ x = FMSetElim.f (⊥ , isProp⊥)
    (λ y {ys} p → FMSetRec.f isSetHProp ((x ≡ y) , ASet x y) (λ _ p → p) (λ _ _ _ → refl) ys)
    (λ x y {xs} b → {!!})
    (λ _ → isSetHProp)

  here : fst (x ∈ [ x ])
  here = refl

  there : ∀ y → fst (x ∈ xs) → fst (x ∈ (y ∷ xs))
  there y p = {!!}

-- data _∈_ (x : A) : FMSet A → Type₁ where
--   here : x ∈ [ x ]
--   there : ∀ {y} → x ∈ xs → x ∈ y ∷ xs

-- out : (x y : A) → [ x ] ≡ [ y ] → x ∈ [ y ]
-- out x y p = transport (λ i → x ∈ p i) here

-- in2 : (x y : A) → x ≡ y → x ∈ [ y ]
-- in2 x y = J (λ z p → x ∈ [ z ]) here

-- out2 : (x : A) → x ∈ [] → ⊥
-- out2 x p = {!!}

postulate
  isOfHLevel⊎ : ∀ n → isOfHLevel n A → isOfHLevel n B → isOfHLevel n (A ⊎ B)

FMSet×-isSet : isSet (FMSet A ×Σ FMSet B)
FMSet×-isSet = isOfHLevelΣ 2 trunc (λ _ → trunc)

module PathsEmpty where

  f1 : ∀ (xs ys : FMSet A) → xs ++ ys ≡ [] → xs ≡ []
  f1 = FMSetElimProp.f (propPi (λ _ → propPi (λ _ → trunc _ _)))
    (λ _ _ → refl)
    (λ _ _ _ p → ⊥-elim (disj-nil-cons p))

  f : ∀ (xs ys : FMSet A) → xs ++ ys ≡ [] → (xs ≡ []) ×Σ (ys ≡ [])
  f xs ys p = f1 xs ys p , f1 ys xs (comm-++ ys xs ∙ p)

  g : ∀ (xs ys : FMSet A) → (xs ≡ []) ×Σ (ys ≡ []) → xs ++ ys ≡ []
  g xs ys (p , q) i = p i ++ q i

module PathsSing where

  f : ∀ xs ys
    → xs ++ ys ≡ [ a ]
    → ((xs ≡ [ a ]) ×Σ (ys ≡ [])) ⊎ ((xs ≡ []) ×Σ (ys ≡ [ a ]))
  f = FMSetElimProp.f (propPi (λ _ → propPi (λ _ → isOfHLevel⊎ 1 (isOfHLevelΣ 1 (trunc _ _) (λ _ → trunc _ _))
                                                                 (isOfHLevelΣ 1 (trunc _ _) (λ _ → trunc _ _)))))
    (λ ys p → inr (refl , p))
    (λ x {xs} f ys p → let q = f [ x ] in inl ({!!} , {!!}))

  g : ∀ xs ys
    → ((xs ≡ [ a ]) ×Σ (ys ≡ [])) ⊎ ((xs ≡ []) ×Σ (ys ≡ [ a ]))
    → xs ++ ys ≡ [ a ]
  g xs ys (inl (p , q)) i = p i ++ q i
  g xs ys (inr (p , q)) i = p i ++ q i

open hProp

module PathsCons where

  code : (ASet : isSet A) (a b : A) (as bs : FMSet A) → hProp ℓ-zero
  code ASet a b as = FMSetElim.f
    (((a ≡ b) , (ASet a b)) ⊓ ((as ≡ []) , trunc as []))
    (λ c {bs} ϕ → (((a ≡ b) , ASet a b) ⊓ ((as ≡ c ∷ bs) , trunc as (c ∷ bs)))
                ⊔ (((a ≡ c) , ASet a c) ⊓ ((as ≡ b ∷ bs) , trunc as (b ∷ bs)))
                ⊔ (∃[ cs ] ((as ≡ b ∷ c ∷ cs) , trunc as (b ∷ c ∷ cs))
                         ⊓ ((bs ≡ a ∷ cs) , trunc bs (a ∷ cs))))
    (λ x y _ → {!!})
    (λ _ → isSetHProp)

module Paths (ASet : isSet A) where

  module _ (a : A) (as : FMSet A) where

    f : (b : A) → hProp ℓ-zero
    f b = ((a ≡ b) , ASet a b) ⊓ ((as ≡ []) , (trunc as []))

    g : A → A → FMSet A → hProp ℓ-zero
    g b₁ b₂ bs = (((a ≡ b₁) , (ASet a b₁)) ⊓ ((as ≡ b₂ ∷ bs) , trunc as (b₂ ∷ bs)))
               ⊔ (((a ≡ b₂) , (ASet a b₂)) ⊓ ((as ≡ b₁ ∷ bs) , trunc as (b₁ ∷ bs)))
               ⊔ (∃[ cs ] ((as ≡ b₁ ∷ b₂ ∷ cs) , trunc as (b₁ ∷ b₂ ∷ cs))
                        ⊓ ((bs ≡ a ∷ cs) , trunc bs (a ∷ cs)))

  code : (as bs : FMSet A) → hProp ℓ-zero
  code [] bs = (bs ≡ []) , (trunc bs [])
  code (a ∷ as) [] = hProp.⊥
  code (a ∷ as) [ b ] = f a as b
  code (a ∷ as) (b₁ ∷ b₂ ∷ bs) = hProp.⊥
  code (a ∷ as) (b ∷ swap b₁ b₂ bs i) = hProp.⊥
  code (a ∷ as) (b ∷ trunc bs cs p q i j) = {!!}
  code (a ∷ as) (swap b₁ b₂ bs i) = hProp.⊥
  code (a ∷ as) (trunc bs cs p q i j) = {!!}
  code (swap a₁ a₂ as i) bs = {!!}
  code (trunc as cs p q i j) bs = {!!}
