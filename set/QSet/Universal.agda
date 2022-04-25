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

q[_] : A → QSet A
q[_] = Q.[_] ∘ L.[_]

∷-cong₀ : {x : A} {xs ys : List A} → xs ≈₀ ys → (x ∷ xs) ≈₀ (x ∷ ys)
∷-cong₀ r = cons-cong refl r

_q∷_ : A → QSet A → QSet A
x q∷ xs = Q.rec squash/ (λ xs → Q.[ x ∷ xs ]) (λ a b r → eq/ (x ∷ a) (x ∷ b) (P.map ∷-cong₀ r)) xs

++-cong₀ : {as bs cs ds : List A} → as ≈₀ cs → bs ≈₀ ds → (as ++ bs) ≈₀ (cs ++ ds)
++-cong₀ nil-refl r = r
++-cong₀ (cons-cong p q) r = cons-cong p (++-cong₀ q r)
++-cong₀ (comm-rel p q) r = comm-rel (++-cong₀ p r) (++-cong₀ q (≈₀-refl _))
++-cong₀ (trans-rel p q) r = trans-rel (++-cong₀ p r) (++-cong₀ q (≈₀-refl _))

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

assoc-q++₀ : (xs ys zs : List A) → xs ++ (ys ++ zs) ≈₀ (xs ++ ys) ++ zs
assoc-q++₀ [] ys zs = ≈₀-refl (ys ++ zs)
assoc-q++₀ (x ∷ xs) ys zs = cons-cong refl (assoc-q++₀ xs ys zs)

assoc-q++ : (xs ys zs : QSet A) → xs q++ (ys q++ zs) ≡ (xs q++ ys) q++ zs
assoc-q++ =
  elimProp (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → squash/ _ _))) λ xs →
    elimProp (λ _ → isPropΠ λ _ → squash/ _ _) λ ys →
      elimProp (λ _ → squash/ _ _) λ zs →
        eq/ _ _ ∣ assoc-q++₀ xs ys zs ∣

swap-rel : (x y : A) (xs : List A) → x ∷ y ∷ xs ≈₀ y ∷ x ∷ xs
swap-rel x y xs = comm-rel (≈₀-refl (y ∷ xs)) (≈₀-refl (x ∷ xs))

cons-++₀ : (x : A) (xs : List A) → x ∷ xs ≈₀ xs ++ L.[ x ]
cons-++₀ x [] = ≈₀-refl L.[ x ]
cons-++₀ x (y ∷ xs) = trans-rel (swap-rel x y xs) (cons-cong refl (cons-++₀ x xs))

comm-++₀ : (xs ys : List A) → xs ++ ys ≈₀ ys ++ xs
comm-++₀ [] ys =
  ≈₀-sym (ys ++ []) ys (unitr-q++₀ ys)
comm-++₀ (x ∷ xs) ys =
  trans-rel (trans-rel (cons-cong refl (comm-++₀ xs ys))
                       (++-cong₀ (cons-++₀ x ys) (≈₀-refl xs)))
            (≈₀-sym (ys ++ x ∷ xs) ((ys ++ L.[ x ]) ++ xs) (assoc-q++₀ ys L.[ x ] xs))

comm-q++ : (xs ys : QSet A) → xs q++ ys ≡ ys q++ xs
comm-q++ =
  elimProp (λ _ → isPropΠ (λ _ → squash/ _ _)) λ xs →
    elimProp (λ _ → squash/ _ _) λ ys →
      eq/ _ _ ∣ comm-++₀ xs ys ∣

open import set.CMon using (CMon; CMonHom; CMonHom≡)

QSetCMon : (A : Type ℓ) → CMon (QSet A)
QSetCMon A = record
              { e = Q.[ [] ]
              ; _⊗_ = _q++_
              ; comm-⊗ = comm-q++
              ; assoc-⊗ = assoc-q++
              ; unit-⊗ = unitl-q++
              ; isSetM = squash/
              }

module univ {M : Type ℓ₁} (C : CMon M) (f : A → M) where

  open CMon C

  comm-rule : {a b as bs cs : M} → as ≡ b ⊗ cs → a ⊗ cs ≡ bs → a ⊗ as ≡ b ⊗ bs
  comm-rule {a} {b} {cs = cs} p q = cong (a ⊗_) p ∙ (assoc-⊗ a b cs ∙ cong (_⊗ cs) (comm-⊗ a b) ∙ assoc-⊗ b a cs ⁻¹) ∙ cong (b ⊗_) q

  f♯ : QSet A → M
  f♯ = Q.rec isSetM g g-≈
    where
      g : List A → M
      g [] = e
      g (x ∷ xs) = f x ⊗ g xs

      g-≈₀ : (xs ys : List A) → xs ≈₀ ys → g xs ≡ g ys
      g-≈₀ .[] .[] nil-refl = refl
      g-≈₀ (x ∷ xs) (y ∷ ys) (cons-cong p q) = cong₂ _⊗_ (cong f p) (g-≈₀ _ _ q)
      g-≈₀ (x ∷ xs) (y ∷ ys) (comm-rel {cs = zs} p q) =
        let r : g xs ≡ f y ⊗ g zs ; r = g-≈₀ xs (y ∷ zs) p
            s : f x ⊗ g zs ≡ g ys ; s = g-≈₀ (x ∷ zs) ys q
        in comm-rule r s
      g-≈₀ xs ys (trans-rel p q) = g-≈₀ _ _ p ∙ g-≈₀ _ _ q

      g-≈ : (xs ys : List A) → xs ≈ ys → g xs ≡ g ys
      g-≈ xs ys = P.rec (isSetM _ _) (g-≈₀ xs ys)
