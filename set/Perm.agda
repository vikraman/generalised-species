{-# OPTIONS --cubical --exact-split --termination-depth=2 #-}

module set.Perm where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetTruncation as S
open import Cubical.Relation.Binary
open import Cubical.Data.Vec as V
open import Cubical.Data.Nat as N
open import Cubical.Data.FinData as F
open import Cubical.HITs.SetQuotients as Q

open import set.NSet
open import set.Prelude

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ
    n : ℕ

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

≈₀-trans : (xs ys zs : Vec A n) → xs ≈₀ ys → ys ≈₀ zs → xs ≈₀ zs
≈₀-trans xs ys zs = TODO

≈-trans : (xs ys zs : Vec A n) → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans xs ys zs = P.map2 (≈₀-trans xs ys zs)

cons-inj₁ : {x y : A} {xs ys : Vec A n} → x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj₁ p = cong head p

cons-inj₂ : {x y : A} {xs ys : Vec A n} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ p = cong tail p

Perm : ℕ → Type ℓ-zero
Perm n = Iso (Fin n) (Fin n) -- Fin n ≃ Fin n

perm : (f g : Fin n → Fin n) (f-g : ∀ x → f (g x) ≡ x) (g-f : ∀ x → g (f x) ≡ x) → Perm n
perm = iso

–> : Perm n → Fin n → Fin n
–> = Iso.fun

<– : Perm n → Fin n → Fin n
<– = Iso.inv

sec : (p : Perm n) → –> p ∘ <– p ≡ idfun _
sec p = funExt (Iso.rightInv p)

ret : (p : Perm n) → <– p ∘ –> p ≡ idfun _
ret p = funExt (Iso.leftInv p)

pid : Perm n
pid = perm (idfun _) (idfun _) (λ _ → refl) (λ _ → refl)

module _ {n : ℕ} where
  psuc : Perm n → Perm (suc n)
  psuc p = perm f g f-g g-f
    where f : Fin (suc n) → Fin (suc n)
          f zero = zero
          f (suc n) = suc (–> p n)
          g : Fin (suc n) → Fin (suc n)
          g zero = zero
          g (suc n) = suc (<– p n)
          f-g : (x : Fin (suc n)) → f (g x) ≡ x
          f-g zero = refl
          f-g (suc x) = cong suc (happly (sec p) x)
          g-f : (x : Fin (suc n)) → g (f x) ≡ x
          g-f zero = refl
          g-f (suc x) = cong suc (happly (ret p) x)

module _ {n : ℕ} where
  pswap : Perm (suc (suc n))
  pswap = perm f f f-f f-f
    where f : Fin (suc (suc n)) → Fin (suc (suc n))
          f zero = suc zero
          f (suc zero) = zero
          f (suc (suc x)) = suc (suc x)
          f-f : (x : Fin (suc (suc n))) → f (f x) ≡ x
          f-f zero = refl
          f-f (suc zero) = refl
          f-f (suc (suc x)) = refl

isContrPerm1 : isContr (Perm 1)
fst isContrPerm1 = pid
snd isContrPerm1 p =
  Iso≡Set isSetFin isSetFin pid p
    (λ { zero → isContrFin1 .snd (–> p zero) })
    (λ { zero → isContrFin1 .snd (<– p zero) })

app : (f : Fin n → Fin n) (xs : Vec A n) → Vec A n
app f xs = FinVec→Vec (Vec→FinVec xs ∘ f)

app-idf : (xs : Vec A n) → app (–> pid) xs ≡ xs
app-idf xs = Vec→FinVec→Vec xs

app-∘ : (f g : Fin n → Fin n) (xs : Vec A n) → app (g ∘ f) xs ≡ app f (app g xs)
app-∘ f g xs =
  cong (λ z → FinVec→Vec (z ∘ f))
       (sym (FinVec→Vec→FinVec (Vec→FinVec xs ∘ g)))

app-psuc-β : (p : Perm n) {x : A} {xs : Vec A n} → app (–> (psuc p)) (x ∷ xs) ≡ x ∷ app (–> p) xs
app-psuc-β p = refl

app-pswap-β : {x y : A} {xs : Vec A n} → app (–> pswap) (x ∷ y ∷ xs) ≡ y ∷ x ∷ xs
app-pswap-β {x = x} {y} {xs} = cong (λ xs → y ∷ x ∷ xs) (Vec→FinVec→Vec xs)

_≅_ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Vec A n → Vec A n → Type ℓ
xs ≅ ys = Σ (Perm _) λ p → app (–> p) xs ≡ ys

≅-refl : (xs : Vec A n) → xs ≅ xs
≅-refl xs = pid , Vec→FinVec→Vec xs

≅-sym : (xs ys : Vec A n) → xs ≅ ys → ys ≅ xs
≅-sym xs ys (p , ϕ) = invIso p , ψ
  where ψ : app (<– p) ys ≡ xs
        ψ = cong (app (<– p)) (ϕ ⁻¹)
          ∙ app-∘ (<– p) (–> p) xs ⁻¹
          ∙ cong (λ z → app z xs) (sec p)
          ∙ app-idf xs

≅-trans : (xs ys zs : Vec A n) → xs ≅ ys → ys ≅ zs → xs ≅ zs
≅-trans xs ys zs (p , ϕ) (q , ψ) = compIso q p , χ
  where χ : app (–> p ∘ –> q) xs ≡ zs
        χ = app-∘ (–> q) (–> p) xs
          ∙ cong (app (–> q)) ϕ
          ∙ ψ

infixr 3 _■_
_■_ : {xs ys zs : Vec A n} → xs ≅ ys → ys ≅ zs → xs ≅ zs
_■_ = ≅-trans _ _ _

≅-cong-∷ : {x y : A} {xs ys : Vec A n} → x ≡ y → xs ≅ ys → x ∷ xs ≅ y ∷ ys
≅-cong-∷ {x = x} {ys = ys} p (q , ϕ) =
     psuc q , app-psuc-β q ∙ cong (x ∷_) ϕ
  ■ subst (λ z → x ∷ ys ≅ z ∷ ys) p (≅-refl (x ∷ ys))

bij : (xs ys : Vec A n) → xs ≈₀ ys → xs ≅ ys
bij .[] .[] nil-refl =
  ≅-refl []
bij (x ∷ xs) (y ∷ ys) (cons-cong p q) =
  ≅-cong-∷ p (bij xs ys q)
bij (x ∷ xs) (y ∷ ys) (comm-rel {cs = cs} p q) =
     ≅-cong-∷ refl (bij xs (y ∷ cs) p)
  ■ pswap , app-pswap-β
  ■ ≅-cong-∷ refl (bij (x ∷ cs) ys q)

ppred : (p : Perm (suc (suc n))) → (–> p zero ≡ zero) → Perm (suc n)
ppred p ϕ = iso f g f-g g-f
  where
    f : _
    f i = predFin (–> p (suc i))
    g : _
    g i = predFin (<– p (suc i))
    f-g : _
    f-g zero = TODO
    f-g (suc i) = TODO
    g-f : _
    g-f zero = TODO
    g-f (suc i) = TODO

pdel : Fin (suc n) → Perm (suc n)
pdel = TODO

tree : (n : ℕ) (xs ys : Vec A n) → xs ≅ ys → xs ≈₀ ys
tree zero [] [] p =
  ≈₀-refl []
tree (suc zero) (x ∷ []) (y ∷ []) (p , ϕ) =
  let ψ = cong –> (isContrPerm1 .snd p)
      δ = cong (λ f → app f (x ∷ [])) (ψ ⁻¹)
  in cons-cong (cons-inj₁ (δ ⁻¹ ∙ ϕ)) nil-refl
tree (suc (suc n)) (x ∷ xs) (y ∷ ys) (p , ϕ) with biEq? (–> p zero) zero
... | eq ψ =
  let η : lookup (–> p zero) (x ∷ xs) ≡ x
      η = cong (λ z → lookup z (x ∷ xs)) ψ
      ε : xs ≅ ys
      ε = ppred p ψ , cons-inj₂ (cong (λ z → z ∷ _) (sym η) ∙ TODO)
  in TODO
... | ¬eq ψ =
  TODO
