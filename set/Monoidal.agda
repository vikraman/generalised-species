{-# OPTIONS --cubical --exact-split --safe #-}

module set.Monoidal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.MSet
open import set.MSet.Universal

private
  variable
    ℓ : Level

open import set.CMon using (CMon ; CMonHom ; CMonHom∘)
open CMon

CMon× : {A B : Type ℓ} → CMon A → CMon B → CMon (A × B)
e (CMon× A B) = e A , e B
_⊗_ (CMon× A B) = λ { (a , b) (c , d) → (_⊗_ A) a c , (_⊗_ B) b d }
unit-⊗ (CMon× A B) (a , b) i = unit-⊗ A a i , unit-⊗ B b i
comm-⊗ (CMon× A B) (a , b) (c , d) i = comm-⊗ A a c i , comm-⊗ B b d i
assoc-⊗ (CMon× A B) (a , b) (c , d) (e , f) i = assoc-⊗ A a c e i , assoc-⊗ B b d f i
isSetM (CMon× A B) = isOfHLevelΣ 2 (isSetM A) λ _ → isSetM B

f-η : {A B : Type ℓ} → (A ⊎ B) → MSet A × MSet B
f-η (inl a) = [ a ] , []
f-η (inr b) = [] , [ b ]

f : {A B : Type ℓ} → MSet (A ⊎ B) → MSet A × MSet B
f = univ.f♯ (CMon× (MSetCMon _) (MSetCMon _)) f-η

f-:: : {A B : Type ℓ} (x : A ⊎ B) (xs : MSet (A ⊎ B)) → f (x :: xs) ≡ (_⊗_ (CMon× (MSetCMon A) (MSetCMon B))) (f-η x) (f xs)
f-:: = univ.f♯-cons (CMon× (MSetCMon _) (MSetCMon _)) f-η

f-++ : {A B : Type ℓ} (xs ys : MSet (A ⊎ B)) → f (xs ++ ys) ≡ (_⊗_ (CMon× (MSetCMon A) (MSetCMon B))) (f xs) (f ys)
f-++ = univ.f♯-++ (CMon× (MSetCMon _) (MSetCMon _)) f-η

mmap : {A B : Type ℓ} → (A → B) → MSet A → MSet B
mmap f = univ.f♯ (MSetCMon _) ([_] ∘ f)

mmap-:: : {A B : Type ℓ} → (f : A → B) (x : A) (xs : MSet A) → mmap f (x :: xs) ≡ f x :: mmap f xs
mmap-:: f = univ.f♯-cons (MSetCMon _) ([_] ∘ f)

mmap-++ : {A B : Type ℓ} → (f : A → B) (xs ys : MSet A) → mmap f (xs ++ ys) ≡ mmap f xs ++ mmap f ys
mmap-++ f = univ.f♯-++ (MSetCMon _) ([_] ∘ f)

g : {A B : Type ℓ} → MSet A × MSet B → MSet (A ⊎ B)
g (as , bs) = mmap inl as ++ mmap inr bs

g-⊗ : {A B : Type ℓ} → (xs ys : MSet A × MSet B) → g ((_⊗_ (CMon× (MSetCMon A) (MSetCMon B))) xs ys) ≡ g xs ++ g ys
g-⊗ (as , bs) (cs , ds) =
    g (as ++ cs , bs ++ ds)
  ≡⟨ cong (_++ mmap inr (bs ++ ds)) (mmap-++ inl as cs) ⟩
    (mmap inl as ++ mmap inl cs) ++ (mmap inr (bs ++ ds))
  ≡⟨ cong ((mmap inl as ++ mmap inl cs) ++_) (mmap-++ inr bs ds) ⟩
    (mmap inl as ++ mmap inl cs) ++ (mmap inr bs ++ mmap inr ds)
  ≡⟨ assoc-++ (mmap inl as ++ mmap inl cs) (mmap inr bs) (mmap inr ds) ⟩
    ((mmap inl as ++ mmap inl cs) ++ mmap inr bs) ++ mmap inr ds
  ≡⟨ cong (_++ mmap inr ds) (sym (assoc-++ (mmap inl as) (mmap inl cs) (mmap inr bs))) ⟩
    (mmap inl as ++ (mmap inl cs ++ mmap inr bs)) ++ mmap inr ds
  ≡⟨ cong (λ z → (mmap inl as ++ z) ++ mmap inr ds) (comm-++ (mmap inl cs) (mmap inr bs)) ⟩
    (mmap inl as ++ (mmap inr bs ++ mmap inl cs)) ++ mmap inr ds
  ≡⟨ cong (_++ mmap inr ds) (assoc-++ (mmap inl as) (mmap inr bs) (mmap inl cs)) ⟩
    ((mmap inl as ++ mmap inr bs) ++ mmap inl cs) ++ mmap inr ds
  ≡⟨ sym (assoc-++ (mmap inl as ++ mmap inr bs) (mmap inl cs) (mmap inr ds)) ⟩
    (mmap inl as ++ mmap inr bs) ++ (mmap inl cs ++ mmap inr ds)
  ≡⟨ refl ⟩
    g (as , bs) ++ g (cs , ds)
  ∎

f-mmap-inl : {A B : Type ℓ} (as : MSet A) → f {A = A} {B} (mmap inl as) ≡ (as , [])
f-mmap-inl = elimProp.f (isSet× trunc trunc _ _) refl λ x {xs} p → h x xs p
  where h : ∀ x xs → (p : f (mmap inl xs) ≡ (xs , [])) → f (mmap inl (x :: xs)) ≡ (x :: xs , [])
        h x xs p = f (mmap inl (x :: xs))
                 ≡⟨ cong f (mmap-:: inl x xs) ⟩
                   f (inl x :: mmap inl xs)
                 ≡⟨ f-:: (inl x) (mmap inl xs) ⟩
                   (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η (inl x)) (f (mmap inl xs))
                 ≡⟨ cong ((_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η (inl x))) p ⟩
                   (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η (inl x)) (xs , [])
                 ≡⟨ refl ⟩
                   (x :: xs , [])
                 ∎

f-mmap-inr : {A B : Type ℓ} (bs : MSet B) → f {A = A} {B} (mmap inr bs) ≡ ([] , bs)
f-mmap-inr = elimProp.f (isSet× trunc trunc _ _) refl λ x {xs} p → h x xs p
  where h : ∀ x xs → (p : f (mmap inr xs) ≡ ([] , xs)) → f (mmap inr (x :: xs)) ≡ ([] , x :: xs)
        h x xs p = f (mmap inr (x :: xs))
                 ≡⟨ cong f (mmap-:: inr x xs) ⟩
                   f (inr x :: mmap inr xs)
                 ≡⟨ f-:: (inr x) (mmap inr xs) ⟩
                   (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η (inr x)) (f (mmap inr xs))
                 ≡⟨ cong ((_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η (inr x))) p ⟩
                   (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η (inr x)) ([] , xs)
                 ≡⟨ refl ⟩
                   ([] , x :: xs)
                 ∎

f-g : {A B : Type ℓ} (as : MSet A) (bs : MSet B) → f (g (as , bs)) ≡ (as , bs)
f-g as bs = f (g (as , bs))
          ≡⟨ f-++ (mmap inl as) (mmap inr bs) ⟩
            (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f (mmap inl as)) (f (mmap inr bs))
          ≡⟨ (λ i → (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-mmap-inl as i) (f-mmap-inr bs i)) ⟩
            (_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (as , []) ([] , bs)
          ≡⟨ refl ⟩
            (as ++ [] , [] ++ bs)
          ≡⟨ (λ i → unitr-⊗ (MSetCMon _) as i , bs) ⟩
            (as , bs)
          ∎

g-f-η : {A B : Type ℓ} (x : A ⊎ B) → g (f-η x) ≡ [ x ]
g-f-η (inl a) = refl
g-f-η (inr b) = refl

g-f' : {A B : Type ℓ} (xs : MSet (A ⊎ B)) → g (f xs) ≡ xs
g-f' = elimProp.f (trunc _ _) refl λ x {xs} p → h x xs p
  where h : ∀ x xs → g (f xs) ≡ xs → g (f (x :: xs)) ≡ x :: xs
        h x xs p = g (f (x :: xs))
                 ≡⟨ cong g (f-:: x xs) ⟩
                   g ((_⊗_ (CMon× (MSetCMon _) (MSetCMon _))) (f-η x) (f xs))
                 ≡⟨ g-⊗ (f-η x) (f xs) ⟩
                   g (f-η x) ++ g (f xs)
                 ≡⟨ (λ i → (g-f-η x i ++ p i)) ⟩
                   x :: xs
                 ∎

g-f : {A B : Type ℓ} (xs : MSet (A ⊎ B)) → g (f xs) ≡ xs
g-f {A = A} {B} = univ-htpy (CMonHom∘ (MSetCMon (A ⊎ B)) (CMon× (MSetCMon A) (MSetCMon B)) (MSetCMon (A ⊎ B)) gHom fHom) p
  where p : (x : A ⊎ B) → g (f [ x ]) ≡ [ x ]
        p (inl a) = refl
        p (inr b) = refl
        fHom : CMonHom (MSetCMon (A ⊎ B)) (CMon× (MSetCMon A) (MSetCMon B))
        fHom = f , refl , f-++
        gHom : CMonHom (CMon× (MSetCMon A) (MSetCMon B)) (MSetCMon (A ⊎ B))
        gHom = g , refl , g-⊗
