{-# OPTIONS --cubical --exact-split --safe #-}

module set.QSet.Universal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q
open import Cubical.Data.List as L

open import set.QSet

private
  variable
    ℓ ℓ₁ : Level
    A : Type ℓ

module _ {A : Type ℓ} (R : Rel A A ℓ) where
  open BinaryRelation R

  qmap2 : (f : A → A → A)
        → (R-isRefl : isRefl)
        → (f-cong₂ : ∀ {a₁ a₂ b₁ b₂} → R a₁ a₂ → R b₁ b₂ → R (f a₁ b₁) (f a₂ b₂))
        → A / R → A / R → A / R
  qmap2 f R-isRefl f-cong₂ = Q.rec2 squash/ (λ a₁ a₂ → Q.[ f a₁ a₂ ])
                                    (λ a b c p → eq/ (f a c) (f b c) (f-cong₂ p (R-isRefl c)))
                                    (λ a b c p → eq/ (f a b) (f a c) (f-cong₂ (R-isRefl a) p))

++-cong₀ : {as bs cs ds : List A} → as ≈₀ cs → bs ≈₀ ds → (as ++ bs) ≈₀ (cs ++ ds)
++-cong₀ nil-refl r = r
++-cong₀ (cons-cong p q) r = cons-cong p (++-cong₀ q r)
++-cong₀ (comm-rel p q) r = comm-rel (++-cong₀ p r) (++-cong₀ q (≈₀-refl _))

_q++_ : ∀ (xs ys : QSet A) → QSet A
_q++_ = qmap2 _≈_ _++_ (λ xs → ∣ ≈₀-refl xs ∣) (P.map2 ++-cong₀)

unitl-q++₀ : (xs : List A) → ([] ++ xs) ≈₀ xs
unitl-q++₀ xs = ≈₀-refl xs

unitl-q++ : (xs : QSet A) → Q.[ [] ] q++ xs ≡ xs
unitl-q++ = elimProp (λ _ → squash/ _ _) λ xs → eq/ _ _ ∣ unitl-q++₀ xs ∣

unitr-q++₀ : (xs : List A) → (xs ++ []) ≈₀ xs
unitr-q++₀ [] = nil-refl
unitr-q++₀ (x ∷ xs) = cons-cong refl (unitr-q++₀ xs)

unitr-q++ : (xs : QSet A) → xs q++ Q.[ [] ] ≡ xs
unitr-q++ = elimProp (λ _ → squash/ _ _) λ xs → eq/ _ _ ∣ unitr-q++₀ xs ∣

assoc-q++₀ : (xs ys zs : List A) → (xs ++ (ys ++ zs)) ≈₀ ((xs ++ ys) ++ zs)
assoc-q++₀ [] ys zs = ≈₀-refl (ys ++ zs)
assoc-q++₀ (x ∷ xs) ys zs = cons-cong refl (assoc-q++₀ xs ys zs)

swap-rel : (x y : A) (xs : List A) → (x ∷ y ∷ xs) ≈₀ (y ∷ x ∷ xs)
swap-rel x y xs = comm-rel (≈₀-refl (y ∷ xs)) (≈₀-refl (x ∷ xs))

-- need ≈₀-trans
-- cons-++₀ : (x : A) (xs : List A) → (x ∷ xs) ≈₀ (xs ++ L.[ x ])
-- cons-++₀ x [] = ≈₀-refl L.[ x ]
-- cons-++₀ x (y ∷ xs) = {!!}
