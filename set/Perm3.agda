{-# OPTIONS --cubical --exact-split --termination-depth=2 --allow-unsolved-metas #-}

module set.Perm3 where

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
open import Cubical.Data.Fin as F
open import Cubical.Data.Fin.LehmerCode as F
open import Cubical.Data.FinData as D renaming (Fin to FinData)
open import Cubical.HITs.SetQuotients as Q

open import set.NSet
open import set.Prelude

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ
    n m o : ℕ

Perm : ℕ → ℕ → Type ℓ-zero
Perm n m = Fin n ≃ Fin m

perm : (f : Fin n → Fin m) (g : Fin m → Fin n)
    → (f-g : ∀ x → f (g x) ≡ x) (g-f : ∀ x → g (f x) ≡ x)
    → Perm n m
perm f g f-g g-f = isoToEquiv (iso f g f-g g-f)

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) where

  –> : A → B
  –> = equivFun e

  <– : B → A
  <– = (equivFun ∘ invEquiv) e

  sec : –> ∘ <– ≡ idfun _
  sec = funExt (secEq e)

  ret : <– ∘ –> ≡ idfun _
  ret = funExt (retEq e)

  –>-inj : ∀ x y → –> x ≡ –> y → x ≡ y
  –>-inj x y p = sym (secEq (invEquiv e) x) ∙ cong <– p ∙ retEq e y

  <–-inj : ∀ x y → <– x ≡ <– y → x ≡ y
  <–-inj x y p = sym (secEq e x) ∙ cong –> p ∙ retEq (invEquiv e) y

pid : Perm n n
pid = idEquiv (Fin _)

fpred : Fin (suc (suc n)) → Fin (suc n)
fpred (zero , ϕ) = fzero
fpred (suc i , ϕ) = i , N.pred-≤-pred ϕ

fsuc-fpred : (i : Fin (suc (suc n))) → ¬ (i ≡ fzero) → fsuc (fpred i) ≡ i
fsuc-fpred (zero , ϕ) ψ = E.rec (ψ (Fin-fst-≡ refl))
fsuc-fpred (suc i , ϕ) ψ = Fin-fst-≡ refl

fpred-fsuc-β : (i : Fin (suc n)) → (fpred (fsuc i)) ≡ i
fpred-fsuc-β i = Fin-fst-≡ refl

fsucmap : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
fsucmap f (zero , ϕ) = fzero
fsucmap f (suc i , ϕ) = fsuc (f (i , N.pred-≤-pred ϕ))

fsucmap-fsuc-β : {f : Fin n → Fin m} → (j@(i , ϕ) : Fin n) → fsucmap f (fsuc j) ≡ fsuc (f j)
fsucmap-fsuc-β {f = f} i = cong fsuc (ham f refl)
  where ham : (f : Fin n → A) → {i j : Fin n} → (i .fst ≡ j .fst) → f i ≡ f j
        ham f ϕ = cong f (Fin-fst-≡ ϕ)

fsucmap-eqv : (e : Fin n ≃ Fin m) → Fin (suc n) ≃ Fin (suc m)
fsucmap-eqv e = isoToEquiv (iso f g f-g g-f)
  where f = fsucmap (–> e)
        g = fsucmap (<– e)
        f-g : _
        f-g (zero , ϕ) = Fin-fst-≡ refl
        f-g (suc i , ϕ) = fsucmap-fsuc-β {f = –> e} (<– e (i , N.pred-≤-pred ϕ))
                        ∙ cong fsuc (secEq e (i , N.pred-≤-pred ϕ))
                        ∙ Fin-fst-≡ refl
        g-f : _
        g-f (zero , ϕ) = Fin-fst-≡ refl
        g-f (suc i , ϕ) = fsucmap-fsuc-β {f = <– e} (–> e (i , N.pred-≤-pred ϕ))
                        ∙ cong fsuc (retEq e (i , N.pred-≤-pred ϕ))
                        ∙ Fin-fst-≡ refl

fsucmap-equiv : {f : Fin n → Fin m} → isEquiv f → isEquiv (fsucmap f)
fsucmap-equiv {f = f} ϕ = fsucmap-eqv (f , ϕ) .snd

fweaken : Fin n → Fin (suc n)
fweaken = inject< N.≤-refl

module _ {n m : ℕ} where
  psuc : Perm n m → Perm (suc n) (suc m)
  psuc = fsucmap-eqv

module _ {n : ℕ} where
  pswap : Perm (suc (suc n)) (suc (suc n))
  pswap = perm f f f-f f-f
    where f : _
          f (zero , ϕ) = 1 , N.suc-≤-suc (N.suc-≤-suc N.zero-≤)
          f (suc zero , ϕ) = 0 , N.suc-≤-suc N.zero-≤
          f (suc (suc i) , ϕ) = suc (suc i) , ϕ
          f-f : _
          f-f (zero , ϕ) = Fin-fst-≡ refl
          f-f (suc zero , ϕ) = Fin-fst-≡ refl
          f-f (suc (suc i) , ϕ) = refl

-- deletes i and p(i) from p
module _ (i : Fin (suc n)) (p : Perm (suc n) (suc m)) where

  q : FinExcept i ≃ FinExcept (–> p i)
  q = isoToEquiv (iso f g f-g g-f)
    where f : _
          f (j , ϕ) = –> p j , λ ψ → ϕ (–>-inj p i j ψ)
          g : _
          g (j , ϕ) = <– p j , λ ψ → ϕ (<–-inj p (–> p i) j (retEq p i ∙ ψ))
          f-g : _
          f-g (j , ϕ) = Σ≡Prop (λ _ → isPropΠ (λ _ → isProp⊥)) (secEq p j)
          g-f : _
          g-f (j , ϕ) = Σ≡Prop (λ _ → isPropΠ (λ _ → isProp⊥)) (retEq p j)

  pdel : Perm n m
  pdel = compEquiv (invEquiv (punchOutEquiv {i = i}))
                   (compEquiv q (punchOutEquiv {i = –> p i}))

module _ (p : Perm (suc (suc n)) (suc (suc m))) where

  pdel-zero-β : –> (pdel fzero p) fzero ≡ fpred (–> p fone)
  pdel-zero-β = {!refl!}


PermData : ℕ → ℕ → Type ℓ-zero
PermData n m = FinData n ≃ FinData m

Perm→PermData : {n m : ℕ} → Perm n m → PermData n m
Perm→PermData {n} {m} p = compEquiv (FinData≃Fin n) (compEquiv p (invEquiv (FinData≃Fin m)))

PermData→Perm : {n m : ℕ} → PermData n m → Perm n m
PermData→Perm {n} {m} p = compEquiv (invEquiv (FinData≃Fin n)) (compEquiv p (FinData≃Fin m))

did : PermData n n
did = idEquiv _

module _ {n m : ℕ} where
  dsuc : PermData n m → PermData (suc n) (suc m)
  dsuc p = isoToEquiv (iso f g f-g g-f)
    where f : _
          f zero = zero
          f (suc n) = suc (–> p n)
          g : _
          g zero = zero
          g (suc m) = suc (<– p m)
          f-g : _
          f-g zero = refl
          f-g (suc x) = cong suc (happly (sec p) x)
          g-f : _
          g-f zero = refl
          g-f (suc x) = cong suc (happly (ret p) x)

module _ {n : ℕ} where
  dswap : PermData (suc (suc n)) (suc (suc n))
  dswap = isoToEquiv (iso f f f-f f-f)
    where f : _
          f zero = suc zero
          f (suc zero) = zero
          f (suc (suc x)) = suc (suc x)
          f-f : _
          f-f zero = refl
          f-f (suc zero) = refl
          f-f (suc (suc x)) = refl

suc-predFin : {i : FinData (suc (suc n))} → ¬ (i ≡ zero) → suc (predFin i) ≡ i
suc-predFin {i = zero} ϕ = E.rec (ϕ refl)
suc-predFin {i = suc i} ϕ = refl

–>-inj-neg : (p : PermData (suc n) (suc n)) → (–> p zero ≡ zero) → {i : FinData (suc n)} → ¬ (i ≡ zero) → ¬ (–> p i ≡ zero)
–>-inj-neg p ϕ {i} ψ χ = ψ (–>-inj p i zero (χ ∙ sym ϕ))

<–-inj-neg : (p : PermData (suc n) (suc n)) → (<– p zero ≡ zero) → {i : FinData (suc n)} → ¬ (i ≡ zero) → ¬ (<– p i ≡ zero)
<–-inj-neg p ϕ {i} ψ χ = ψ (<–-inj p i zero (χ ∙ sym ϕ))

–>-<– : (p : PermData n n) {i j : FinData n} → –> p i ≡ j → <– p j ≡ i
–>-<– p {i} ϕ = cong (<– p) (sym ϕ) ∙ happly (ret p) i

module _ {n : ℕ} where
  dpred : (p : PermData (suc (suc n)) (suc (suc n))) → (–> p zero ≡ zero) → PermData (suc n) (suc n)
  dpred p ϕ = isoToEquiv (iso f g f-g g-f)
    where
      f : _
      f i = predFin (–> p (suc i))
      g : _
      g i = predFin (<– p (suc i))
      f-g : _
      f-g i = cong (predFin ∘ –> p) (suc-predFin (<–-inj-neg p (–>-<– p ϕ) D.snotz))
            ∙ cong predFin (happly (sec p) (suc i))
      g-f : _
      g-f i = cong (predFin ∘ <– p) (suc-predFin (–>-inj-neg p ϕ D.snotz))
            ∙ cong predFin (happly (ret p) (suc i))

module _ (i : FinData (suc n)) (p : PermData (suc n) (suc m)) where

  ddel : PermData n m
  ddel =
    let j = FinData→Fin (suc n) i
        q = PermData→Perm p
        r = pdel j q
        s = Perm→PermData r
    in s

_ : ddel zero (dsuc {n = 2} (did {n = 2})) ≡ did {n = 2}
_ = equivEq (funExt λ { zero → refl ; (suc zero) → refl })

_ : ddel zero (dswap {n = 1}) ≡ did {n = 2}
_ = equivEq (funExt λ { zero → refl ; (suc zero) → refl })

module _ (p : PermData (suc (suc n)) (suc (suc m))) where

  ddel-zero-β : –> (ddel zero p) zero ≡ predFin (–> p one)
  ddel-zero-β = TODO

biEq-rec : {i j : FinData n} → (i ≡ j → A) → (¬ i ≡ j → A) → biEq i j → A
biEq-rec f g (eq ϕ) = f ϕ
biEq-rec f g (¬eq ϕ) = g ϕ

biEq-rec-cst-η : {i j : FinData n} {ϕ : biEq i j} → (a : A) → biEq-rec (λ _ → a) (λ _ → a) ϕ ≡ a
biEq-rec-cst-η {ϕ = eq ϕ} a = refl
biEq-rec-cst-η {ϕ = ¬eq ϕ} a = refl

biEq?-refl : (i : FinData n) → biEq? i i ≡ eq refl
biEq?-refl zero = refl
biEq?-refl (suc i) with D.discreteFin i i
... | yes p = let q = D.isSetFin i i p refl in cong eq λ j k → suc (q j k)
... | no ¬p = E.rec (¬p refl)

module _ (p : PermData (suc (suc n)) (suc (suc n))) where

  ddel0 : PermData (suc n) (suc n)
  ddel0 = isoToEquiv (iso f g f-g g-f)
    where
      f : _
      f zero = predFin (–> p zero)
      f (suc i) = suc i
      g : _
      g i = biEq-rec (λ _ → zero) (λ _ → i) (biEq? i (predFin (–> p zero)))

      f-g : _
      f-g zero = cong f (biEq-rec-cst-η {ϕ = biEq? zero (predFin (–> p zero))} zero) ∙ {!!}
      f-g (suc i) = {!!}

      g-suc : {i : FinData n} → g (suc i) ≡ suc i
      g-suc = {!!}

      g-f : ∀ i → g (f i) ≡ i
      g-f zero = cong (biEq-rec _ _) (biEq?-refl (predFin (–> p zero)))
      g-f (suc i) = {!!}
