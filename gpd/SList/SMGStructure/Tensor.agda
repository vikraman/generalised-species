{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SMGStructure.Tensor where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG

module _ {i} {A : Type i} where

  abstract
    one-paths-level : {xs ys : SList A} → is-set (xs == ys)
    one-paths-level = has-level-apply trunc _ _
    two-paths-level : {xs ys : SList A} {p q : xs == ys} → is-prop (p == q)
    two-paths-level = has-level-apply one-paths-level _ _

  module app where

    f-nil : SList A → SList A
    f-nil ys = ys

    f-cons : A → (SList A → SList A) → SList A → SList A
    f-cons x f ys = x :: f ys

    f-swap : (x y : A) (f : SList A → SList A) → f-cons x (f-cons y f) == f-cons y (f-cons x f)
    f-swap x y f = λ= λ ys → swap x y (f ys)

    f-swap² : (x y : A) → A → (f : SList A → SList A) → f-swap x y f ∙ f-swap y x f == idp
    f-swap² x y z f =
      let h1 = λ ys → swap x y (f ys)
          h2 = λ ys → swap y x (f ys)
      in λ=-∙' h1 h2 ∙ ap λ= (λ= λ ys → swap² x y (f ys)) ∙ λ=-idp

    f-⬡ : (x y z : A) (f : SList A → SList A)
        → f-swap x y (f-cons z f) ∙ ap (f-cons y) (f-swap x z f) ∙ f-swap y z (f-cons x f)
        == ap (f-cons x) (f-swap y z f) ∙ f-swap x z (f-cons y f) ∙ ap (f-cons z) (f-swap x y f)
    f-⬡ x y z f =
        f-swap x y (f-cons z f) ∙ ap (f-cons y) (f-swap x z f) ∙ f-swap y z (f-cons x f)
      =⟨ f-swap x y (f-cons z f) ∙ₗ (λ=-ap (λ _ → y ::_) (λ ys → swap x z (f ys)) ∙ᵣ f-swap y z (f-cons x f)) ⟩
        f-swap x y (f-cons z f) ∙ λ= (λ ys → ap (y ::_) (swap x z (f ys))) ∙ f-swap y z (f-cons x f)
      =⟨ λ=-∙∙' (λ ys → swap x y (z :: f ys)) (λ ys → ap (y ::_) (swap x z (f ys))) (λ ys → swap y z (x :: f ys)) ⟩
        λ= (λ ys → swap x y (z :: f ys) ∙ ap (y ::_) (swap x z (f ys)) ∙ swap y z (x :: f ys))
      =⟨ ap λ= (λ= λ ys → ⬡ x y z (f ys)) ⟩
        λ= (λ ys → ap (x ::_) (swap y z (f ys)) ∙ swap x z (y :: f ys) ∙ ap (z ::_) (swap x y (f ys)))
      =⟨ ! (λ=-∙∙' (λ ys → ap (x ::_) (swap y z (f ys))) (λ ys → swap x z (y :: f ys)) (λ ys → ap (z ::_) (swap x y (f ys)))) ⟩
        λ= (λ ys → ap (x ::_) (swap y z (f ys))) ∙ (f-swap x z (f-cons y f) ∙ λ= (λ ys → ap (z ::_) (swap x y (f ys))))
      =⟨ (! (λ=-ap (λ _ → x ::_) (λ ys → swap y z (f ys)))) ⋆2 (f-swap x z (f-cons y f) ∙ₗ ! (λ=-ap (λ _ → z ::_) (λ ys → swap x y (f ys)))) ⟩
        ap (f-cons x) (f-swap y z f) ∙ (f-swap x z (f-cons y f) ∙ ap (f-cons z) (f-swap x y f))
      =∎

    private
      module F = SListRec f-nil f-cons f-swap f-swap² f-⬡ (Π-level λ _ → trunc)

    f : SList A → SList A → SList A
    f = F.f

    f-swap-β : {x y : A} {xs : SList A} → ap f (swap x y xs) == λ= (λ ys → swap x y (f xs ys))
    f-swap-β = F.f-swap-β

  infixr 40 _++_
  _++_ : SList A → SList A → SList A
  _++_ = app.f

  swap-nat : {x y : A} {xs ys : SList A} (p : xs == ys)
           → swap x y xs ∙ ap (y ::_) (ap (x ::_) p) == ap (x ::_) (ap (y ::_) p) ∙ swap x y ys
  swap-nat {x = x} {y} {xs} idp = ∙-unit-r (swap x y xs)

  swap-nat' : {x y : A} {xs ys : SList A} (p : xs == ys)
            → ap (x ::_) (ap (y ::_) p) ∙' swap x y ys == swap x y xs ∙ ap (y ::_) (ap (x ::_) p)
  swap-nat' {x = x} {y} {xs} idp = ∙'-unit-l (swap x y xs) ∙ ! (∙-unit-r (swap x y xs))

  swap-inv : {x y : A} {xs : SList A} → swap x y xs == ! (swap y x xs)
  swap-inv {x = x} {y} {xs} = inv-∙ (swap x y xs) (swap y x xs) (swap² x y xs)

  ++-swap-β : {x y : A} {xs : SList A}
            → ap _++_ (swap x y xs) == λ= (λ ys → swap x y (xs ++ ys))
  ++-swap-β = app.f-swap-β

  abstract
    ++-r-swap-β : {x y : A} {xs : SList A} (ys : SList A)
                → ap (_++ ys) (swap x y xs) == swap x y (xs ++ ys)
    ++-r-swap-β {x = x} {y} {xs} ys =
        ap (_++ ys) (swap x y xs)
      =⟨ ap-∘ (λ f → f ys) _++_ (swap x y xs)  ⟩
        ap (λ f → f ys) (ap _++_ (swap x y xs))
      =⟨ ap (ap (λ f → f ys)) ++-swap-β ⟩
        ap (λ f → f ys) (λ= (λ ys → swap x y (xs ++ ys)))
      =⟨ idp ⟩
        app= (λ= (λ ys → swap x y (xs ++ ys))) ys
      =⟨ app=-β (λ ys → swap x y (xs ++ ys)) ys ⟩
        swap x y (xs ++ ys)
      =∎

  ↓-=-swap-in : ∀ {j} {P : SList A → Type j}
              → (f g : (xs : SList A) → P xs)
              → {x y : A} {xs : SList A}
              → {u : f (x :: y :: xs) == g (x :: y :: xs)} {v : f (y :: x :: xs) == g (y :: x :: xs)}
              → u ◃ apd g (swap x y xs) == apd f (swap x y xs) ▹ v
              → u == v [ (λ ys → f ys == g ys) ↓ swap x y xs ]
  ↓-=-swap-in {P = P} f g {x} {y} {xs} = ↓-=-in

  ↓-='-swap-in : ∀ {j} {P : Type j}
               → (f g : SList A → P)
               → {x y : A} {xs : SList A}
               → {u : f (x :: y :: xs) == g (x :: y :: xs)} {v : f (y :: x :: xs) == g (y :: x :: xs)}
               → u ∙' ap g (swap x y xs) == ap f (swap x y xs) ∙ v
               → u == v [ (λ ys → f ys == g ys) ↓ swap x y xs ]
  ↓-='-swap-in {P = P} f g {x} {y} {xs} = ↓-='-in
