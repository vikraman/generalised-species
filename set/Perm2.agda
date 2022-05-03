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
open import Cubical.Data.FinData as F
import Cubical.Data.Fin as F
import Cubical.Data.Fin.LehmerCode as F
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

Perm : ℕ → ℕ → Type ℓ-zero
Perm n m = Iso (Fin n) (Fin m) -- Fin n ≃ Fin n

perm : (f : Fin n → Fin m) (g : Fin m → Fin n) (f-g : ∀ x → f (g x) ≡ x) (g-f : ∀ x → g (f x) ≡ x) → Perm n m
perm = iso

–> : Perm n m → Fin n → Fin m
–> = Iso.fun

<– : Perm n m → Fin m → Fin n
<– = Iso.inv

sec : (p : Perm n m) → –> p ∘ <– p ≡ idfun _
sec p = funExt (Iso.rightInv p)

ret : (p : Perm n m) → <– p ∘ –> p ≡ idfun _
ret p = funExt (Iso.leftInv p)

pid : Perm n n
pid = perm (idfun _) (idfun _) (λ _ → refl) (λ _ → refl)

module _ {n m : ℕ} where
  psuc : Perm n m → Perm (suc n) (suc m)
  psuc p = perm f g f-g g-f
    where f : Fin (suc n) → Fin (suc m)
          f zero = zero
          f (suc n) = suc (–> p n)
          g : Fin (suc m) → Fin (suc n)
          g zero = zero
          g (suc m) = suc (<– p m)
          f-g : (x : Fin (suc m)) → f (g x) ≡ x
          f-g zero = refl
          f-g (suc x) = cong suc (happly (sec p) x)
          g-f : (x : Fin (suc n)) → g (f x) ≡ x
          g-f zero = refl
          g-f (suc x) = cong suc (happly (ret p) x)

module _ {n : ℕ} where
  pswap : Perm (suc (suc n)) (suc (suc n))
  pswap = perm f f f-f f-f
    where f : Fin (suc (suc n)) → Fin (suc (suc n))
          f zero = suc zero
          f (suc zero) = zero
          f (suc (suc x)) = suc (suc x)
          f-f : (x : Fin (suc (suc n))) → f (f x) ≡ x
          f-f zero = refl
          f-f (suc zero) = refl
          f-f (suc (suc x)) = refl

suc-predFin : {i : Fin (suc (suc n))} → ¬ (i ≡ zero) → suc (predFin i) ≡ i
suc-predFin {i = zero} ϕ = E.rec (ϕ refl)
suc-predFin {i = suc i} ϕ = refl

predFin-weakenFin : {i : Fin (suc (suc n))} → predFin (weakenFin i) ≡ i
predFin-weakenFin {i = zero} = refl
predFin-weakenFin {i = suc zero} = {!!}
predFin-weakenFin {i = suc (suc i)} = {!!}

–>-inj-neg : (p : Perm (suc n) (suc n)) → (–> p zero ≡ zero) → {i : Fin (suc n)} → ¬ (i ≡ zero) → ¬ (–> p i ≡ zero)
–>-inj-neg p ϕ {i} ψ χ = ψ (isoFunInjective p i zero (χ ∙ sym ϕ))

<–-inj-neg : (p : Perm (suc n) (suc n)) → (<– p zero ≡ zero) → {i : Fin (suc n)} → ¬ (i ≡ zero) → ¬ (<– p i ≡ zero)
<–-inj-neg p ϕ {i} ψ χ = ψ (isoInvInjective p i zero (χ ∙ sym ϕ))

–>-<– : (p : Perm n n) {i j : Fin n} → –> p i ≡ j → <– p j ≡ i
–>-<– p {i} ϕ = cong (<– p) (sym ϕ) ∙ happly (ret p) i

module _ {n : ℕ} where
  ppred : (p : Perm (suc (suc n)) (suc (suc n))) → (–> p zero ≡ zero) → Perm (suc n) (suc n)
  ppred p ϕ = iso f g f-g g-f
    where
      f : _
      f i = predFin (–> p (suc i))
      g : _
      g i = predFin (<– p (suc i))
      f-g : _
      f-g i = cong (predFin ∘ –> p) (suc-predFin (<–-inj-neg p (–>-<– p ϕ) F.snotz))
            ∙ cong predFin (happly (sec p) (suc i))
      g-f : _
      g-f i = cong (predFin ∘ <– p) (suc-predFin (–>-inj-neg p ϕ F.snotz))
            ∙ cong predFin (happly (ret p) (suc i))

isContrPerm1 : isContr (Perm 1 1)
fst isContrPerm1 = pid
snd isContrPerm1 p =
  Iso≡Set isSetFin isSetFin pid p
    (λ { zero → isContrFin1 .snd (–> p zero) })
    (λ { zero → isContrFin1 .snd (<– p zero) })

L : ∀ {ℓ} → Type ℓ → Type ℓ
L A = Σ ℕ (FinVec A)

V→L : {n : ℕ} → Vec A n → L A
V→L {n = n} xs = n , Vec→FinVec xs

L→V : (xs : L A) → Vec A (xs .fst)
L→V xs = FinVec→Vec (xs .snd)

infix 3 _▹_
_▹_ : A → L A → L A
x ▹ (n , f) = suc n , λ { zero → x ; (suc n) → f n }

_≅_ : ∀ {ℓ} {A : Type ℓ} → (_ _ : L A) → Type ℓ
(n , f) ≅ (m , g) = Σ (Iso (Fin n) (Fin m)) λ p → f ≡ g ∘ –> p

≅-refl : (xs : L A) → xs ≅ xs
≅-refl xs = pid , refl

≅-sym : (xs ys : L A) → xs ≅ ys → ys ≅ xs
≅-sym (n , f) (m , g) (p , ϕ) =
  invIso p , sym (∘-idˡ g) ∙ cong (g ∘_) (sym (sec p))
           ∙ sym (∘-assoc g (–> p) (<– p)) ∙ cong (_∘ <– p) (sym ϕ)

≅-trans : (xs ys zs : L A) → xs ≅ ys → ys ≅ zs → xs ≅ zs
≅-trans (n , f) (m , g) (o , h) (p , ϕ) (q , ψ) =
  compIso p q , ϕ ∙ cong (_∘ –> p) ψ

infixr 3 _■_
_■_ : {xs ys zs : L A} → xs ≅ ys → ys ≅ zs → xs ≅ zs
_■_ {xs = xs} {ys} {zs} = ≅-trans xs ys zs

-- ≅-cong-▹ : {x y : A} {xs ys : L A} → x ≡ y → xs ≅ ys → (x ▹ xs) ≅ (y ▹ ys)
-- ≅-cong-▹ {x = x} {y} {(n , f)} {(m , g)} p (q , ϕ) =
--   psuc q , funExt λ { zero → p ; (suc n) → happly ϕ n }

≅-cong-∷ : {x y : A} {xs ys : Vec A n} → x ≡ y → V→L xs ≅ V→L ys → V→L (x ∷ xs) ≅ V→L (y ∷ ys)
≅-cong-∷ {x = x} {y} {xs} {ys} p (q , ϕ) =
  psuc q , funExt λ { zero → p ; (suc n) → happly ϕ n }

swap : (x y : A) (xs : Vec A n) → V→L (x ∷ y ∷ xs) ≅ V→L (y ∷ x ∷ xs)
swap {n = n} x y xs = pswap {n = n} , funExt (λ { zero → refl ; (suc zero) → refl ; (suc (suc n)) → refl })

bij : (xs ys : Vec A n) → xs ≈₀ ys → V→L xs ≅ V→L ys
bij .[] .[] nil-refl =
  ≅-refl (V→L [])
bij (x ∷ xs) (y ∷ ys) (cons-cong p q) =
  ≅-cong-∷ p (bij xs ys q)
bij (x ∷ xs) (y ∷ ys) (comm-rel {cs = cs} p q) =
  ≅-trans _ _ (V→L (y ∷ ys))
    (≅-cong-∷ refl (bij xs (y ∷ cs) p))
    (≅-trans _ _ (V→L (y ∷ ys))
      (swap x y cs)
      (≅-cong-∷ refl (bij (x ∷ cs) ys q)))

infix 3 _<_
_<_ : Fin n → Fin n → Type₀
i < j = (toℕ i) N.< (toℕ j)

lt? : (i j : Fin n) → Dec (i < j)
lt? i j = N.<Dec (toℕ i) (toℕ j)

lt≠ : {i j : Fin n} → (i < j) → ¬ (i ≡ j)
lt≠ {i = i} {j = j} ϕ ψ = N.<→≢ ϕ (cong toℕ ψ)

del : (i : Fin (suc n)) → (f : Fin (suc n) → A) → (Fin n → A)
del i f j with lt? i (suc j)
... | yes ϕ = f (suc j)
... | no ¬ϕ = f (weakenFin j)

cons : A → (f : Fin n → A) → (Fin (suc n) → A)
cons x f zero = x
cons x f (suc i) = f i

del-cons : (x : A) (f : Fin n → A) → del zero (cons x f) ≡ f
del-cons x f = refl

cons-inj : {x y : A} {f g : Fin n → A} → cons x f ≡ cons y g → x ≡ y → f ≡ g
cons-inj {x = x} {y} {f} {g} ϕ ψ = sym (del-cons x f) ∙ cong (del zero) ϕ ∙ del-cons y g

cons-del : {x : A} {f : Fin (suc n) → A}
        → x ≡ f zero
        → cons x (del zero f) ≡ f
cons-del ϕ = funExt λ { zero → ϕ ; (suc n) → refl }

del-∘ : {i : Fin (suc n)} {f : Fin (suc n) → Fin (suc n)} {g : Fin (suc n) → A}
     → ∀ j → del i (g ∘ f) j ≡ del (f i) g j
del-∘ {i = i} {f} {g} j with lt? i (suc j) | lt? (f i) (suc j)
... | yes ϕ | yes ψ = {!!} -- i < suc j ∧ f i < suc j
... | yes ϕ | no ¬ψ = {!!}
... | no ¬ϕ | yes ψ = {!!}
... | no ¬ϕ | no ¬ψ = {!!}

xx : (i : Fin (suc n)) → ¬ (i ≡ zero) → Fin n
xx zero ϕ = E.rec (ϕ refl)
xx (suc i) ϕ = i

xx-wk : (i : Fin (suc (suc n))) → (ϕ : ¬ (i ≡ zero)) → xx i ϕ ≡ predFin i
xx-wk zero ϕ = E.rec (ϕ refl)
xx-wk (suc i) ϕ = refl

-- module _ {n : ℕ} where
--   pdel : (p : Perm (suc (suc n)) (suc (suc n))) → ¬ (–> p zero ≡ zero) → Perm (suc n) (suc n)
--   pdel p ϕ = iso f g f-g g-f
--     where
--       f : _
--       f i = del {A = Fin (suc n)} (zero) (predFin ∘ –> p) i
--       g : _
--       g i with lt? (–> p zero) (weakenFin i)
--       ... | yes ψ = let z = <– p (suc i) in predFin z
--       ... | no ¬ψ = let z = <– p (suc {!!}) in {!!}
--       f-g : _
--       f-g i with lt? (–> p zero) (suc i)
--       ... | yes ψ = {!!}
--       ... | no ¬ψ = {!!}
--       -- cong (predFin ∘ –> p) (suc-predFin {i = <– p (suc i)} {!!}) ∙ {!!}
--       -- ... | yes ψ = cong (predFin ∘ –> p) (suc-predFin {i = <– p (suc i)} λ δ → lt≠ ψ (cong (–> p) (sym δ) ∙ happly (sec p) (suc i)))
--       --             ∙ cong predFin (happly (sec p) (suc i))
--       -- ... | no ¬ψ = {!!}
--       g-f : _
--       g-f i = {!!}

tree : (n : ℕ) (f g : Fin n → A)
    → (n , f) ≅ (n , g)
    → (L→V (n , f)) ≈₀ (L→V (n , g))
tree zero f g (p , ϕ) =
  nil-refl
tree (suc zero) f g (p , ϕ) =
  let ψ = cong –> (isContrPerm1 .snd p)
  in cons-cong (happly ϕ zero ∙ cong g (happly (sym ψ) zero)) nil-refl
tree (suc (suc n)) f g (p , ϕ) with biEq? (–> p zero) zero
... | eq ψ =
  cons-cong (happly ϕ zero ∙ cong g ψ)
            (tree (suc n) (f ∘ suc) (g ∘ suc)
              (ppred p ψ , cong (_∘ suc) ϕ
                         ∙ cong (g ∘_) (funExt (λ i → sym (suc-predFin (–>-inj-neg p ψ F.snotz))))))
... | ¬eq ψ =
  let h = del zero (del (–> p zero) g)
      δ = happly ϕ zero
  in comm-rel {cs = L→V (n , h)}
       (tree (suc n)
         (del zero f) (cons (g zero) h)
         (pid , cons-inj {x = f zero} {y = f zero} {f = del zero f} {g = del (–> p zero) (g ∘ –> p)}
                         (cons-del {f = f} refl ∙ ϕ ∙ sym (cons-del {x = g (–> p zero)} refl) ∙ cong (λ z → cons z (del zero (g ∘ –> p))) (sym δ) ∙ {!!}) refl
                ∙ {!!}))
       (tree (suc n)
         (cons (f zero) h) (del zero g)
         {!!})

-- p(0) ≠ 0
-- f(0) = g(p(0))
-- del 0 f = ? = del (p 0) g
-- cons (f 0) (del 0 f) = f = g = cons (g (p 0)) (del (p 0) g) = cons (f 0) (del (p 0) g)
-- f\0 = g(0) :: g\0\p(0) = g\p(0) ∎
-- f(0) :: g\0\p(0) = g\0 ∎
