{-# OPTIONS --cubical --safe #-}

module FMGpd.Universal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import FMGpd

infixr 30 _⊗_

_⊗_ : ∀ (xs ys : FMGpd A) → FMGpd A
[] ⊗ ys = ys
(x ∷ xs) ⊗ ys = x ∷ xs ⊗ ys
comm a b as bs cs p q i ⊗ ys =
  comm a b (as ⊗ ys) (bs ⊗ ys) (cs ⊗ ys)
    (cong (_⊗ ys) p) (cong (_⊗ ys) q) i
trunc xs zs p q u v i j k ⊗ ys =
  trunc (xs ⊗ ys) (zs ⊗ ys) (cong (_⊗ ys) p)
    (cong (_⊗ ys) q) (cong (cong (_⊗ ys)) u) (cong (cong (_⊗ ys)) v) i j k

unitl-⊗ : ∀ (xs : FMGpd A) → [] ⊗ xs ≡ xs
unitl-⊗ xs = refl

unitr-⊗ : ∀ (xs : FMGpd A) → xs ⊗ [] ≡ xs
unitr-⊗ = FMGpdElimSet.f (λ _ → trunc _ _)
  refl
  (λ x p → cong (x ∷_) p)
  (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq i j →
    comm a b (bas j) (bbs j) (bcs j) (λ k → bp k j) (λ k → bq k j) i)

assoc-⊗ : ∀ (xs ys zs : FMGpd A) → xs ⊗ (ys ⊗ zs) ≡ (xs ⊗ ys) ⊗ zs
assoc-⊗ = FMGpdElimSet.f (λ _ → isSetPi λ _ → isSetPi λ _ → trunc _ _)
  (λ ys zs → refl)
  (λ x {xs} p ys zs → cong (x ∷_) (p ys zs))
  (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq i ys zs j →
    comm a b (bas ys zs j) (bbs ys zs j) (bcs ys zs j) (λ k → bp k ys zs j) (λ k → bq k ys zs j) i)

cons-⊗ : ∀ (x : A) (xs : FMGpd A) → x ∷ xs ≡ xs ⊗ [ x ]
cons-⊗ x = FMGpdElimSet.f (λ _ → trunc _ _)
  refl
  (λ y {xs} p i → hcomp (λ j → λ { (i = i0) → x ∷ y ∷ xs
                                 ; (i = i1) → y ∷ p j })
                        (swap x y xs i)
  -- swap x y xs ∙ cong (y ∷_) p
  )
  (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq i →
    let bpi : x ∷ p i ≡ p i ⊗ [ x ] ; bpi = bp i
        bqi = bq i
    in {!!}
  --   x ∷ comm a b as bs cs p q i
  -- ≡[ j ]⟨ {!!} ⟩
  --   comm a b (x ∷ as) (x ∷ bs) (x ∷ cs) (cong (x ∷_) p ∙ swap x b cs) (swap a x cs ∙ cong (x ∷_) q) i
  -- ≡[ j ]⟨ comm a b (x ∷ as) (x ∷ bs) (x ∷ cs) {!!} {!!} {!!} ⟩
  --   comm a b (as ⊗ [ x ]) (bs ⊗ [ x ]) (cs ⊗ [ x ]) (λ k → p k ⊗ [ x ]) (λ k → q k ⊗ [ x ]) i
  -- ∎
    -- hfill (λ j → λ { (i = i0) → swap x a as ∙ cong (a ∷_) bas
    --                ; (i = i1) → swap x b bs ∙ cong (b ∷_) bbs })
    --       (inS {!!}) i1
    -- x ∷ comm a b as bs cs p q i ≡
    --   comm a b (as ⊗ [ x ]) (bs ⊗ [ x ]) (cs ⊗ [ x ])
    --   (λ i₁ → p i₁ ⊗ [ x ]) (λ i₁ → q i₁ ⊗ [ x ]) i
      -- comm a b (bas j) (bbs j) (bcs j) {!!} {!!} {!!}
  )

comm-⊗ : ∀ (xs ys : FMGpd A) → xs ⊗ ys ≡ ys ⊗ xs
comm-⊗ = FMGpdElimSet.f (λ _ → isSetPi (λ _ → trunc _ _))
  (λ ys → sym (unitr-⊗ ys))
  (λ x {xs} p ys → cong (x ∷_) (p ys)
                 ∙ cong (_⊗ xs) (cons-⊗ x ys)
                 ∙ sym (assoc-⊗ ys [ x ] xs))
  (λ a b {as bs cs} bas bbs bcs {p} bp {q} bq i →
     {!!}
    -- comm a b (bas ys j) (bbs ys j) (bcs ys j) {!!} {!!} {!!}
  )

-- symmetric monoidal groupoid

map : {B : Type ℓ} → (A → B) → FMGpd A → FMGpd B
map f = FMGpdRec.f trunc [] (λ a bs → f a ∷ bs)
  λ a b bas bbs bcs bp bq → comm (f a) (f b) bas bbs bcs bp bq

map-⊗ : {B : Type ℓ} {f : A → B}
      → (xs ys : FMGpd A)
      → map f (xs ⊗ ys) ≡ map f xs ⊗ map f ys
map-⊗ {f = f} = FMGpdElimSet.f (λ _ → isSetPi (λ _ → trunc _ _))
  (λ ys → refl)
  (λ x {xs} p ys → cong (f x ∷_) (p ys))
  λ a b {as bs cs} bas bbs bcs {p} bp {q} bq i ys j →
    comm (f a) (f b) (bas ys j) (bbs ys j) (bcs ys j) (λ k → bp k ys j) (λ k → bq k ys j) i
