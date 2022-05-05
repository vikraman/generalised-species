{-# OPTIONS --cubical --exact-split --termination-depth=2 --allow-unsolved-metas #-}

module set.Perm2 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetTruncation as S
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.Data.Vec as V
open import Cubical.Data.Nat as N
import Cubical.Data.Nat.Order as N
open import Cubical.Data.FinData as D renaming (Fin to FinData)
open import Cubical.Data.Fin as F
open import Cubical.HITs.SetQuotients as Q

open import set.NSet
open import set.Prelude

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ
    n m o : ℕ

infix 3 _≈₀_ _≈_ _≅_

data _≈₀_ {ℓ} {A : Type ℓ} : {n : ℕ} → Vec A n → Vec A n → Type ℓ where
  nil-refl : [] ≈₀ []
  cons-cong : ∀ {a b : A} {n : ℕ} {as bs : Vec A n}
            → (p : a ≡ b) → (q : as ≈₀ bs)
            → (a ∷ as) ≈₀ (b ∷ bs)
  comm-rel : ∀ {a b} {n : ℕ} {as bs : Vec A (suc n)} {cs : Vec A n}
           → (p : as ≈₀ (b ∷ cs)) → (q : (a ∷ cs) ≈₀ bs)
           → (a ∷ as) ≈₀ (b ∷ bs)

_≈_ : Vec A n → Vec A n → Type _
xs ≈ ys = ∥ xs ≈₀ ys ∥

≈₀-refl : (xs : Vec A n) → xs ≈₀ xs
≈₀-refl [] = nil-refl
≈₀-refl (x ∷ xs) = cons-cong refl (≈₀-refl xs)

≈-refl : (xs : Vec A n) → xs ≈ xs
≈-refl = ∣_∣ ∘ ≈₀-refl

≈₀-sym : (xs ys : Vec A n) → xs ≈₀ ys → ys ≈₀ xs
≈₀-sym .[] .[] nil-refl = nil-refl
≈₀-sym (x ∷ xs) (y ∷ ys) (cons-cong p q) = cons-cong (p ⁻¹) (≈₀-sym xs ys q)
≈₀-sym (x ∷ xs) (y ∷ ys) (comm-rel {cs = cs} p q) = comm-rel (≈₀-sym (x ∷ cs) ys q) (≈₀-sym xs (y ∷ cs) p)

≈-sym : (xs ys : Vec A n) → xs ≈ ys → ys ≈ xs
≈-sym xs ys = P.map (≈₀-sym xs ys)

cons-inj₁ : {x y : A} {xs ys : Vec A n} → x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj₁ p = cong head p

cons-inj₂ : {x y : A} {xs ys : Vec A n} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ p = cong tail p

open import set.Perm3

isContrPerm1 : isContr (Perm 1 1)
isContrPerm1 = isOfHLevel≃ 0 F.isContrFin1 F.isContrFin1

isContrPermData1 : isContr (PermData 1 1)
isContrPermData1 = isOfHLevel≃ 0 D.isContrFin1 D.isContrFin1

L : ∀ {ℓ} → Type ℓ → Type ℓ
L A = Σ ℕ (D.FinVec A)
-- L A = Σ ℕ (λ n → Fin n → A)

flookup : ∀ {n} {A : Type ℓ} → Fin n → Vec A n → A
flookup {n = .zero} (i , ϕ) [] = E.rec (N.¬-<-zero ϕ)
flookup {n = .(suc _)} (zero , ϕ) (x ∷ xs) = x
flookup {n = .(suc _)} (suc i , ϕ) (x ∷ xs) = flookup (i , N.pred-≤-pred ϕ) xs

V→L : {n : ℕ} → Vec A n → L A
-- V→L {n = n} xs = n , λ i → flookup i xs
V→L {n = n} xs = n , Vec→FinVec xs

L→V : (xs : L A) → Vec A (xs .fst)
L→V xs = FinVec→Vec (xs .snd)

infix 3 _▹_
_▹_ : A → L A → L A
x ▹ (n , f) = suc n , λ { zero → x ; (suc n) → f n }

_≅_ : ∀ {ℓ} {A : Type ℓ} → (_ _ : L A) → Type ℓ
(n , f) ≅ (m , g) = Σ (PermData n m) λ p → f ≡ g ∘ –> p

≅-refl : (xs : L A) → xs ≅ xs
≅-refl xs = idEquiv _ , refl

≅-sym : (xs ys : L A) → xs ≅ ys → ys ≅ xs
≅-sym (n , f) (m , g) (p , ϕ) =
  invEquiv p , sym (∘-idˡ g) ∙ cong (g ∘_) (sym (sec p))
             ∙ sym (∘-assoc g (–> p) (<– p)) ∙ cong (_∘ <– p) (sym ϕ)

≅-trans : (xs ys zs : L A) → xs ≅ ys → ys ≅ zs → xs ≅ zs
≅-trans (n , f) (m , g) (o , h) (p , ϕ) (q , ψ) =
  compEquiv p q , ϕ ∙ cong (_∘ –> p) ψ

infixr 3 _■_
_■_ : {xs ys zs : L A} → xs ≅ ys → ys ≅ zs → xs ≅ zs
_■_ {xs = xs} {ys} {zs} = ≅-trans xs ys zs

≅-cong-▹ : {x y : A} {xs ys : L A} → x ≡ y → xs ≅ ys → (x ▹ xs) ≅ (y ▹ ys)
≅-cong-▹ {x = x} {y} {(n , f)} {(m , g)} p (q , ϕ) =
  dsuc q , funExt λ { zero → p ; (suc n) → happly ϕ n }

≅-cong-∷ : {x y : A} {xs ys : Vec A n} → x ≡ y → V→L xs ≅ V→L ys → V→L (x ∷ xs) ≅ V→L (y ∷ ys)
≅-cong-∷ {x = x} {y} {xs} {ys} p (q , ϕ) =
  dsuc q , funExt λ { zero → p ; (suc n) → happly ϕ n }

≅-swap : (x y : A) (xs : Vec A n) → V→L (x ∷ y ∷ xs) ≅ V→L (y ∷ x ∷ xs)
≅-swap {n = n} x y xs = dswap {n = n} , funExt (λ { zero → refl ; (suc zero) → refl ; (suc (suc n)) → refl })

bij : (as bs : Vec A n) → as ≈₀ bs → V→L as ≅ V→L bs
bij .[] .[] nil-refl =
  ≅-refl (V→L [])
bij (a ∷ as) (b ∷ bs) (cons-cong p q) =
  ≅-cong-∷ p (bij as bs q)
bij (a ∷ as) (b ∷ bs) (comm-rel {cs = cs} p q) =
  ≅-trans _ _ (V→L (b ∷ bs))
    (≅-cong-∷ refl (bij as (b ∷ cs) p))
    (≅-trans _ _ (V→L (b ∷ bs))
      (≅-swap a b cs)
      (≅-cong-∷ refl (bij (a ∷ cs) bs q)))

infix 3 _<_
_<_ : FinData n → FinData n → Type₀
i < j = (D.toℕ i) N.< (D.toℕ j)

lt? : (i j : FinData n) → Dec (i < j)
lt? i j = N.<Dec (D.toℕ i) (D.toℕ j)

lt≠ : {i j : FinData n} → (i < j) → ¬ (i ≡ j)
lt≠ {i = i} {j = j} ϕ ψ = N.<→≢ ϕ (cong D.toℕ ψ)

del : (i : FinData (suc n)) → (f : FinData (suc n) → A) → (FinData n → A)
del i f j with lt? i (suc j)
... | yes ϕ = f (suc j)
... | no ¬ϕ = f (weakenFin j)

cons : A → (f : FinData n → A) → (FinData (suc n) → A)
cons x f zero = x
cons x f (suc i) = f i

del-cons : (x : A) (f : FinData n → A) → del zero (cons x f) ≡ f
del-cons x f = refl

cons-inj : {x y : A} {f g : FinData n → A} → cons x f ≡ cons y g → x ≡ y → f ≡ g
cons-inj {x = x} {y} {f} {g} ϕ ψ = sym (del-cons x f) ∙ cong (del zero) ϕ ∙ del-cons y g

cons-del : {x : A} {f : FinData (suc n) → A}
        → x ≡ f zero
        → cons x (del zero f) ≡ f
cons-del ϕ = funExt λ { zero → ϕ ; (suc n) → refl }

tree : (n : ℕ) (f g : FinData n → A)
    → (n , f) ≅ (n , g)
    → (L→V (n , f)) ≈₀ (L→V (n , g))
tree zero f g (p , ϕ) =
  nil-refl
tree (suc zero) f g (p , ϕ) =
  let ψ = cong –> (isContrPermData1 .snd p)
  in cons-cong (happly ϕ zero ∙ cong g (happly (sym ψ) zero)) nil-refl
tree (suc (suc n)) f g (p , ϕ) with biEq? (–> p zero) zero
... | eq ψ =
  cons-cong (happly ϕ zero ∙ cong g ψ)
            (tree (suc n) (f ∘ suc) (g ∘ suc)
              (dpred p ψ , cong (_∘ suc) ϕ
                         ∙ cong (g ∘_)
                           (funExt (λ i → sym (suc-predFin (–>-inj-neg p ψ D.snotz))))))
... | ¬eq ψ =
  let h = del zero (del (–> p zero) g)
      δ = happly ϕ zero
  in comm-rel {cs = L→V (n , h)}
       (tree (suc n)
         (del zero f) (cons (g zero) h)
         (ddel zero p ,
           cons-inj {x = f zero} {y = f zero} {f = del zero f} {g = del (–> p zero) (g ∘ –> p)}
             (cons-del {f = f} refl ∙ ϕ ∙ sym (cons-del {x = g (–> p zero)} refl) ∙ cong (λ z → cons z (del zero (g ∘ –> p))) (sym δ) ∙ TODO) refl
           ∙ TODO))
       (tree (suc n)
         (cons (f zero) h) (del zero g)
         (ddel zero p , TODO))
