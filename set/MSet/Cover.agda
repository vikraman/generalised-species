{-# OPTIONS --cubical --exact-split #-}

module set.MSet.Cover where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum as S
open import Cubical.Data.Empty as E
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Relation.Binary
open import Cubical.Functions.Logic as L

open import set.Prelude
open import set.MSet
open import set.MSet.Universal
open import set.MSet.Length
open import set.MSet.Paths
open import set.MSet.Nat

private
  variable
    ℓ : Level
    A B : Type ℓ
    a b x y : A
    xs ys as bs cs : MSet A

infix 3 _≈₀_ _≈_ 

data _≈₀_ {ℓ} {A : Type ℓ} : MSet A → MSet A → Type ℓ where
  nil-refl : [] ≈₀ []
  cons-cong : ∀ {a as bs}
            → (as ≈₀ bs)
            → (a :: as) ≈₀ (a :: bs)
  comm-rel : ∀ {a b as bs cs}
           → (p : as ≈₀ (b :: cs)) → (q : (a :: cs) ≈₀ bs)
           → (a :: as) ≈₀ (b :: bs)

_≈_ : MSet A → MSet A → Type _
xs ≈ ys = ∥ xs ≈₀ ys ∥

≈-refl : (xs : MSet A) → xs ≈ xs
≈-refl = elimProp.f squash ∣ nil-refl ∣ (λ x → P.map cons-cong)

encode : (xs ys : MSet A) → xs ≡ ys → xs ≈ ys
encode xs ys = J (λ ys p → xs ≈ ys) (≈-refl xs)

decode₀ : (xs ys : MSet A) → xs ≈₀ ys → xs ≡ ys
decode₀ _ _ nil-refl = refl
decode₀ _ _ (cons-cong p) = cong (_ ::_) (decode₀ _ _ p)
decode₀ _ _ (comm-rel p q) = commrel (decode₀ _ _ p) (decode₀ _ _ q)

decode : (xs ys : MSet A) → xs ≈ ys → xs ≡ ys
decode xs ys = P.rec (trunc xs ys) (decode₀ xs ys)

≈-equiv-≡ : {xs ys : MSet A} → (xs ≈ ys) ≃ (xs ≡ ys)
≈-equiv-≡ {xs = xs} {ys = ys} = propBiimpl→Equiv squash (trunc xs ys) (decode xs ys) (encode xs ys)

module _ {ℓ} {A : Type ℓ} where
  open BinaryRelation {A = MSet A} _≈_

  ≈₀-sym : (xs ys : MSet A) → xs ≈₀ ys → ys ≈₀ xs
  ≈₀-sym .[] .[] nil-refl = nil-refl
  ≈₀-sym .(_ :: _) .(_ :: _) (cons-cong p) = cons-cong (≈₀-sym _ _ p)
  ≈₀-sym .(_ :: _) .(_ :: _) (comm-rel p q) = comm-rel (≈₀-sym _ _ q) (≈₀-sym _ _ p)

  ≈-sym : isSym
  ≈-sym as bs = P.map (≈₀-sym as bs)

  ≈-trans : isTrans
  ≈-trans as bs cs p q = encode as cs (decode as bs p ∙ decode bs cs q)

  ≈-isEquivRel : isEquivRel
  ≈-isEquivRel = equivRel ≈-refl ≈-sym ≈-trans

module thm61 {A : Type ℓ} {ϕ : isSet A}
             (bialg : (as bs cs ds : MSet A) → (as ++ bs) ≡ (cs ++ ds)
                   → Σ (MSet A × MSet A × MSet A × MSet A)
                        λ { (xs1 , xs2 , ys1 , ys2) → (as ≡ xs1 ++ xs2) × (bs ≡ ys1 ++ ys2)
                                                     × (xs1 ++ ys1 ≡ cs) × (xs2 ++ ys2 ≡ ds) }) where

  goal : (a b : A) (as bs : MSet A) → hProp ℓ
  goal a b as bs =
     ((((a ≡ b) , ϕ a b) ⊓ ((as ≡ bs) , trunc as bs))
    ⊔ (∃[ cs ∶ MSet A ] ((as ≡ b :: cs) , trunc as (b :: cs))
                      ⊓ ((a :: cs ≡ bs) , trunc (a :: cs) bs)))

  goal-nil : (a b : A) (bs : MSet A) → [ a ] ≡ b :: bs → goal a b [] bs .fst
  goal-nil a b bs p =
    let q = ++-sing-out {xs = [ b ]} {ys = bs} {a = a} (sym p)
    in S.rec (λ { (α , β) → L.inl ([-]-inj {ϕ = ϕ} (sym α) , sym β) })
             (λ { (α , β) → E.rec (snotz (cong length α)) })
             q

  lem1 : (a b : A) (as : MSet A) → a :: as ≡ [ b ] → (a ≡ b) × (as ≡ [])
  lem1 a b as p =
    let q = ++-sing-out {xs = [ a ]} {ys = as} {a = b} p
    in S.rec (λ { (α , β)→ [-]-inj {ϕ = ϕ} α , β })
             (λ { (α , β) → E.rec (snotz (cong length α)) })
             q

  lem2 : (a b : A) (as cs : MSet A)
      → Σ (MSet A) (λ xs → (a :: xs ≡ [ b ]) × (as ≡ xs ++ cs))
      → (a ≡ b) × (as ≡ cs)
  lem2 a b as cs (xs , p , q) =
    let (ϕ , ψ) = lem1 a b xs p in (ϕ , q ∙ cong (_++ cs) ψ)

  lem4 : (a : A) (as bs cs : MSet A)
      → (a :: as) ≡ (bs ++ cs)
      → Σ (MSet A) (λ xs → (a :: xs ≡ bs) × (as ≡ xs ++ cs))
       ⊎ Σ (MSet A) (λ ys → (as ≡ bs ++ ys) × (a :: ys ≡ cs))
  lem4 a as bs cs p =
    let ((xs1 , xs2 , ys1 , ys2) , (ϕ1 , ϕ2 , ϕ3 , ϕ4)) = bialg [ a ] as bs cs p
        q : ((xs1 ≡ [ a ]) × (xs2 ≡ [])) ⊎ ((xs1 ≡ []) × (xs2 ≡ [ a ]))
        q = ++-sing-out {xs = xs1} {ys = xs2} {a = a} (sym ϕ1)
    in S.rec (λ { (ϕ , ψ) → S.inl (ys1 , cong (_++ ys1) (sym ϕ) ∙ ϕ3 , ϕ2 ∙ cong (λ z → ys1 ++ (z ++ ys2)) (sym ψ) ∙ cong (ys1 ++_) ϕ4) })
             (λ { (ϕ , ψ) → S.inr (ys2 , ϕ2 ∙ cong (λ z → (z ++ ys1) ++ ys2) (sym ϕ) ∙ cong (_++ ys2) ϕ3 , cong (_++ ys2) (sym ψ) ∙ ϕ4) })
             q

  thm61 : (a b : A) (as bs : MSet A) → (a :: as) ≡ (b :: bs) → goal a b as bs .fst
  thm61 a b as bs p =
    let q = lem4 a as [ b ] bs p
    in S.rec (λ α → L.inl (lem2 a b as bs α)) (λ β → L.inr P.∣ β ∣) q
