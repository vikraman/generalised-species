{-# OPTIONS --cubical --exact-split --safe #-}

module set.Comm where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Agda.Primitive

open import set.MSet
open import set.MSet.Paths
open import set.MSet.Universal

private
  variable
    ℓ : Level
    A B : Type ℓ

σ : MSet A × B → MSet (A × B)
σ (as , b) = mmap (λ a → (a , b)) as

σ♯ : MSet (MSet A × B) → MSet (A × B)
σ♯ = univ.f♯ (MSetCMon _) σ

τ : A × MSet B → MSet (A × B)
τ (a , bs) = mmap (λ b → (a , b)) bs

τ♯ : MSet (A × MSet B) → MSet (A × B)
τ♯ = univ.f♯ (MSetCMon _) τ

comm-htpy-nil : (as : MSet A) → τ♯ {B = B} (σ (as , [])) ≡ σ♯ (τ (as , []))
comm-htpy-nil =
  elimProp.f {B = λ as → τ♯ (σ (as , [])) ≡ σ♯ (τ (as , []))}
             (λ {as} → trunc (τ♯ (σ (as , []))) (σ♯ (τ (as , []))))
             refl
             (λ a {as} p → p)

τ-cons : (a : A) (b : B) (bs : MSet B) → τ (a , b :: bs) ≡ (a , b) :: τ (a , bs)
τ-cons a b bs = mmap-cons b bs λ b → (a , b)

σ♯-cons : (as : MSet A) (b : B) (ps : MSet (MSet A × B)) → σ♯ ((as , b) :: ps) ≡ σ (as , b) ++ σ♯ ps
σ♯-cons as b ps = univ.f♯-cons (MSetCMon _) σ (as , b) ps

σ-cons : (a : A) (as : MSet A) (b : B) → σ (a :: as , b) ≡ (a , b) :: σ (as , b)
σ-cons a as bs = mmap-cons a as λ a → (a , bs)

τ♯-cons : (a : A) (bs : MSet B) (ps : MSet (A × MSet B)) → τ♯ ((a , bs) :: ps) ≡ τ (a , bs) ++ τ♯ ps
τ♯-cons a bs ps = univ.f♯-cons (MSetCMon _) τ (a , bs) ps

comm-htpy-cons : (b : B) (bs : MSet B)
              → (f : (as : MSet A) → τ♯ (σ (as , bs)) ≡ σ♯ (τ (as , bs)))
              → (as : MSet A) → τ♯ {B = B} (σ (as , b :: bs)) ≡ σ♯ (τ (as , b :: bs))
comm-htpy-cons b bs f =
  elimProp.f {B = λ as → τ♯ (σ (as , b :: bs)) ≡ σ♯ (τ (as , b :: bs))}
             (λ {as} → trunc (τ♯ (σ (as , b :: bs))) (σ♯ (τ (as , b :: bs))))
             (f [])
             (λ a {as} p →
                 τ♯ (σ (a :: as , b :: bs))
               ≡⟨ cong τ♯ (σ-cons a as (b :: bs)) ⟩
                 τ♯ ((a , b :: bs) :: σ (as , b :: bs))
               ≡⟨ τ♯-cons a (b :: bs) (σ (as , b :: bs)) ⟩
                 τ (a , b :: bs) ++ τ♯ (σ (as , b :: bs))
               ≡⟨ cong₂ _++_ (τ-cons a b bs) p ⟩
                 (a , b) :: τ (a , bs) ++ σ♯ (τ (as , b :: bs))
               ≡⟨ cong (λ xs → (a , b) :: τ (a , bs) ++ σ♯ xs) (τ-cons as b bs) ⟩
                 (a , b) :: τ (a , bs) ++ σ♯ ((as , b) :: τ (as , bs))
               ≡⟨ cong (λ xs → (a , b) :: τ (a , bs) ++ xs) (σ♯-cons as b (τ (as , bs))) ⟩
                 (a , b) :: τ (a , bs) ++ (σ (as , b) ++ σ♯ (τ (as , bs)))
               ≡⟨ cong ((a , b) ::_) (assoc-++ (τ (a , bs)) (σ (as , b)) (σ♯ (τ (as , bs)))
                                    ∙ cong (_++ σ♯ (τ (as , bs))) (comm-++ (τ (a , bs)) (σ (as , b)))
                                    ∙ sym (assoc-++ (σ (as , b)) (τ (a , bs)) (σ♯ (τ (as , bs))))) ⟩
                 (a , b) :: σ (as , b) ++ (τ (a , bs) ++ σ♯ (τ (as , bs)))
               ≡⟨ cong (λ xs → (a , b) :: σ (as , b) ++ (τ (a , bs) ++ xs)) (sym (f as)) ⟩
                 (a , b) :: σ (as , b)  ++ (τ (a , bs) ++ τ♯ (σ (as , bs)))
               ≡⟨ cong (λ xs → (a , b) :: σ (as , b) ++ xs) (sym (τ♯-cons a bs (σ (as , bs)))) ⟩
                 (a , b) :: σ (as , b)  ++ τ♯ ((a , bs) :: σ (as , bs))
               ≡⟨ cong (λ xs → (a , b) :: σ (as , b) ++ τ♯ xs) (sym (σ-cons a as bs)) ⟩
                 (a , b) :: σ (as , b)  ++ τ♯ (σ (a :: as , bs))
               ≡⟨ cong (λ xs → (a , b) :: σ (as , b) ++ xs) (f (a :: as)) ⟩
                 (a , b) :: σ (as , b) ++ σ♯ (τ (a :: as , bs))
               ≡⟨ cong (λ xs → xs ++ σ♯ (τ (a :: as , bs))) (sym (σ-cons a as b)) ⟩
                  σ (a :: as , b) ++ σ♯ (τ (a :: as , bs))
               ≡⟨ sym (σ♯-cons (a :: as) b (τ (a :: as , bs))) ⟩
                 σ♯ ((a :: as , b) :: τ (a :: as , bs))
               ≡⟨ cong σ♯ (sym (τ-cons (a :: as) b bs)) ⟩
                 σ♯ (τ (a :: as , b :: bs))
               ∎)

comm-htpy : (bs : MSet B) → (as : MSet A) → τ♯ (σ (as , bs)) ≡ σ♯ (τ (as , bs))
comm-htpy =
  elimProp.f {B = λ bs → (as : MSet _) → τ♯ (σ (as , bs)) ≡ σ♯ (τ (as , bs))}
             (λ {bs} → isPropΠ (λ as → trunc (τ♯ (σ (as , bs))) (σ♯ (τ (as , bs)))))
             comm-htpy-nil
             (λ b {bs} f → comm-htpy-cons b bs f)

comm : τ♯ {A = A} {B = B} ∘ σ ≡ σ♯ ∘ τ
comm = funExt λ (as , bs) → comm-htpy bs as
