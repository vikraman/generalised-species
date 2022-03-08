{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SMGStructure where

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

  module ++-α (xs ys zs : SList A) where

    f-swap : (x y : A) {xs : SList A} (p : (xs ++ ys) ++ zs == xs ++ ys ++ zs)
           → (ap (x ::_) (ap (y ::_) p)) == (ap (y ::_) (ap (x ::_) p)) [ (λ xs → (xs ++ ys) ++ zs == xs ++ (ys ++ zs)) ↓ swap x y xs ]
    f-swap x y {xs} p =
      ↓-='-swap-in (λ xs → (xs ++ ys) ++ zs) (λ xs → xs ++ (ys ++ zs))
        ((ap (x ::_) (ap (y ::_) p) ∙'ₗ ++-r-swap-β (ys ++ zs))
        ∙ swap-nat' p
        ∙ (! (ap ((_++ zs) ∘ (_++ ys)) (swap x y xs)
          =⟨ ap-∘ (_++ zs) (_++ ys) (swap x y xs) ⟩
             ap (_++ zs) (ap (_++ ys) (swap x y xs))
          =⟨ ap (ap (_++ zs)) (++-r-swap-β ys) ⟩
             ap (_++ zs) (swap x y (xs ++ ys))
          =⟨ ++-r-swap-β zs ⟩
             swap x y ((xs ++ ys) ++ zs) =∎)
          ∙ᵣ ap (y ::_) (ap (x ::_) p)) )

    f : (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
    f =
      SListRecPaths.rec ⦃ trunc ⦄
        (λ xs → (xs ++ ys) ++ zs) (λ xs → xs ++ (ys ++ zs))
        idp (λ x p → ap (x ::_) p) f-swap
        xs

  module ++-Λ (xs : SList A) where

    f-swap : (x y : A) {xs : SList A} (p : nil ++ xs == xs)
          → (ap (x ::_) (ap (y ::_) p)) == (ap (y ::_) (ap (x ::_) p)) [ (λ ys → nil ++ ys == ys) ↓ swap x y xs ]
    f-swap x y {xs} p = 
      ↓-='-swap-in (nil ++_) (idf _)
        ((ap (x ::_) (ap (y ::_) p) ∙'ₗ (ap-idf (swap x y xs)))
        ∙ swap-nat' p 
        ∙ (! (ap-idf (swap x y (nil ++ xs))) ∙ᵣ ap (y ::_) (ap (x ::_) p)) )

    f : nil ++ xs == xs
    f = idp
      -- SListRecPaths.rec ⦃ trunc ⦄
      --   (nil ++_) (idf _) idp (λ x p → ap (x ::_) p) f-swap xs

  module ++-ρ (xs : SList A) where

    f-swap : (x y : A) {xs : SList A} (p : xs ++ nil == xs)
           → (ap (x ::_) (ap (y ::_) p)) == (ap (y ::_) (ap (x ::_) p)) [ (λ ys → ys ++ nil == ys) ↓ swap x y xs ]
    f-swap x y {xs} p =
      ↓-='-swap-in (_++ nil) (idf _)
        ((ap (_::_ x) (ap (_::_ y) p) ∙'ₗ (ap-idf (swap x y xs)))
        ∙ swap-nat' p
        ∙ (! (++-r-swap-β nil) ∙ᵣ ap (y ::_) (ap (x ::_) p)) )

    f : xs ++ nil == xs
    f =
      SListRecPaths.rec ⦃ trunc ⦄
        (_++ nil) (idf _) idp (λ x p → ap (x ::_) p) f-swap xs

  module ++-β (xs ys : SList A) where

    -- g-::-nil-swap : (x y z : A) {xs : SList A} (p : x :: xs == xs ++ [ x ])
    --               → (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs ∙ ap (z ::_) p)) == (swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs ∙ ap (y ::_) p)) [ (λ xs → x :: xs == xs ++ [ x ]) ↓ swap y z xs ]
    -- g-::-nil-swap x y z {xs} p =
    --   ↓-='-swap-in (x ::_) (_++ [ x ])
    --     ((swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs ∙ ap (z ::_) p)) ∙' ap (_++ [ x ]) (swap y z xs)
    --     =⟨ (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs ∙ ap (z ::_) p)) ∙'ₗ (++-r-swap-β [ x ]) ⟩
    --      (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs ∙ ap (z ::_) p)) ∙' swap y z (xs ++ [ x ])
    --     =⟨ (swap x y (z :: xs) ∙ₗ ap-∙ (y ::_) (swap x z xs) (ap (z ::_) p)) ∙'ᵣ swap y z (xs ++ [ x ]) ⟩
    --      (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ ap (y ::_) (ap (z ::_) p)) ∙' swap y z (xs ++ [ x ])
    --     =⟨ ∙∙∙'-assoc (swap x y (z :: xs)) (ap (y ::_ ) (swap x z xs)) (ap (y ::_) (ap (z ::_) p)) (swap y z (xs ++ [ x ])) ⟩
    --       swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ (ap (y ::_) (ap (z ::_) p) ∙' swap y z (xs ++ [ x ]))
    --     =⟨ swap x y (z :: xs) ∙ₗ (ap (y ::_) (swap x z xs) ∙ₗ swap-nat' p) ⟩
    --       swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs) ∙ ap (z ::_) (ap (y ::_) p)
    --     =⟨ ! (∙∙-assoc (swap x y (z :: xs)) (ap (y ::_) (swap x z xs)) (swap y z (x :: xs)) (ap (z ::_) (ap (y ::_) p))) ⟩
    --       (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)) ∙ ap (z ::_) (ap (y ::_) p)
    --     =⟨ ⬡ x y z xs ∙ᵣ ap (z ::_ ) (ap (y ::_) p) ⟩
    --       (ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_ ) (swap x y xs)) ∙ ap (z ::_ ) (ap (y ::_) p)
    --     =⟨ ∙∙-assoc (ap (x ::_) (swap y z xs)) (swap x z (y :: xs)) (ap (z ::_ ) (swap x y xs)) (ap (z ::_ ) (ap (y ::_) p)) ⟩
    --       ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_ ) (swap x y xs) ∙ ap (z ::_ ) (ap (y ::_) p)
    --     =⟨ ap (x ::_) (swap y z xs) ∙ₗ (swap x z (y :: xs) ∙ₗ ∙-ap (z ::_) (swap x y xs) (ap (y ::_) p)) ⟩
    --       ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_ ) (swap x y xs ∙ ap (y ::_) p)
    --     =∎)

    -- g-::-nil : (x : A) (ys : SList A) → x :: ys == ys ++ [ x ]
    -- g-::-nil x =
    --   SListRecPaths.rec ⦃ trunc ⦄
    --     (x ::_) (_++ [ x ])
    --     idp (λ y {ys} p → swap x y ys ∙ ap (y ::_) p)
    --     (λ y z {xs} p → g-::-nil-swap x y z p)

    -- g-:: : (x : A) {xs : SList A} (ys : SList A)
    --     → (p : xs ++ ys == ys ++ xs)
    --     → (x :: xs) ++ ys == ys ++ (x :: xs)
    -- g-:: x {xs} ys p =
    --   ap (x ::_) p ∙ ap (_++ xs) (g-::-nil x ys) ∙ ++-α.f ys [ x ] xs

    -- g-::-swap : (x y : A) {xs : SList A} (ys : SList A)
    --          → (p : xs ++ ys == ys ++ xs)
    --          → (g-:: x ys (g-:: y ys p)) == (g-:: y ys (g-:: x ys p)) [ (λ xs → xs ++ ys == ys ++ xs) ↓ swap x y xs ]
    -- g-::-swap x y {xs} ys p =
    --   ↓-='-swap-in (_++ ys) (ys ++_)
    --     ( g-:: x ys (g-:: y ys p) ∙' ap (ys ++_) (swap x y xs)
    --     =⟨ idp ⟩
    --       (ap (x ::_) (g-:: y ys p) ∙ ap (_++ y :: xs) (g-::-nil x ys) ∙ ++-α.f ys [ x ] (y :: xs)) ∙' ap (ys ++_) (swap x y xs)
    --     =⟨ TODO ⟩
    --       swap x y (xs ++ ys) ∙ (ap (y ::_) (g-:: x ys p) ∙ ap (_++ x :: xs) (g-::-nil y ys) ∙ ++-α.f ys [ y ] (x :: xs))
    --     =⟨ idp ⟩
    --       swap x y (xs ++ ys) ∙ g-:: y ys (g-:: x ys p)
    --     =⟨ ! (++-r-swap-β ys) ∙ᵣ g-:: y ys (g-:: x ys p) ⟩
    --       ap (_++ ys) (swap x y xs) ∙ g-:: y ys (g-:: x ys p)
    --     =∎)

    f-::-swap : (x y z : A) {xs : SList A} (ys : SList A)
              → (p : x :: xs ++ ys == xs ++ x :: ys)
              → (swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys) ∙ ap (z ::_) p)) == (swap x z ((y :: xs) ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys) ∙ ap (y ::_) p)) [ (λ zs → x :: zs ++ ys == zs ++ x :: ys) ↓ swap y z xs ]
    f-::-swap x y z {xs} ys p =
      ↓-='-swap-in (λ zs → x :: zs ++ ys) (λ zs → zs ++ x :: ys)
        ( (swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys) ∙ ap (z ::_) p)) ∙' ap (_++ x :: ys) (swap y z xs)
        =⟨ (swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys) ∙ ap (z ::_) p)) ∙'ₗ ++-r-swap-β (x :: ys) ⟩
          (swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys) ∙ ap (z ::_) p)) ∙' swap y z (xs ++ x :: ys)
        =⟨ (swap x y ((z :: xs) ++ ys) ∙ₗ ap-∙ (y ::_) (swap x z (xs ++ ys)) (ap (z ::_) p)) ∙'ᵣ swap y z (xs ++ x :: ys) ⟩
          (swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys)) ∙ ap (y ::_) (ap (z ::_) p)) ∙' swap y z (xs ++ x :: ys)
        =⟨ ∙∙∙'-assoc (swap x y ((z :: xs) ++ ys)) (ap (y ::_) (swap x z (xs ++ ys))) (ap (y ::_) (ap (z ::_) p)) (swap y z (xs ++ x :: ys)) ⟩
          swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys)) ∙ (ap (y ::_) (ap (z ::_) p) ∙' swap y z (xs ++ x :: ys))
        =⟨ swap x y ((z :: xs) ++ ys) ∙ₗ (ap (y ::_) (swap x z (xs ++ ys)) ∙ₗ swap-nat' p) ⟩
          swap x y ((z :: xs) ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys)) ∙ swap y z (x :: xs ++ ys) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ! (∙∙-assoc (swap x y ((z :: xs) ++ ys)) (ap (y ::_) (swap x z (xs ++ ys))) (swap y z (x :: xs ++ ys)) (ap (z ::_) (ap (y ::_) p))) ⟩
          (swap x y (z :: xs ++ ys) ∙ ap (y ::_) (swap x z (xs ++ ys)) ∙ swap y z (x :: xs ++ ys)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ⬡ x y z (xs ++ ys) ∙ᵣ ap (z ::_) (ap (y ::_) p) ⟩
          (ap (x ::_) (swap y z (xs ++ ys)) ∙ swap x z (y :: xs ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys))) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ∙∙-assoc (ap (x ::_) (swap y z (xs ++ ys))) (swap x z (y :: xs ++ ys)) (ap (z ::_) (swap x y (xs ++ ys))) (ap (z ::_) (ap (y ::_) p)) ⟩
          ap (x ::_) (swap y z (xs ++ ys)) ∙ swap x z (y :: xs ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ap (ap (x ::_)) (! (++-r-swap-β ys)) ∙ᵣ swap x z (y :: xs ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys)) ∙ ap (z ::_) (ap (y ::_) p) ⟩
          ap (x ::_) (ap (_++ ys) (swap y z xs)) ∙ swap x z ((y :: xs) ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ∘-ap (x ::_) (_++ ys) (swap y z xs) ∙ᵣ swap x z ((y :: xs) ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys)) ∙ ap (z ::_) (ap (y ::_) p) ⟩
          ap (λ zs → x :: zs ++ ys) (swap y z xs) ∙ swap x z ((y :: xs) ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ap (λ zs → x :: zs ++ ys) (swap y z xs) ∙ₗ (swap x z ((y :: xs) ++ ys) ∙ₗ ∙-ap (z ::_) (swap x y (xs ++ ys)) (ap (y ::_) p)) ⟩
          ap (λ zs → x :: zs ++ ys) (swap y z xs) ∙ swap x z ((y :: xs) ++ ys) ∙ ap (z ::_) (swap x y (xs ++ ys) ∙ ap (y ::_) p)
        =∎)

    f-:: : (x : A) {xs : SList A} (ys : SList A)
        → (x :: xs) ++ ys == xs ++ (x :: ys)
    f-:: x {xs} ys =
      SListRecPaths.rec ⦃ trunc ⦄
        (λ xs → x :: xs ++ ys) (λ xs → xs ++ (x :: ys))
        idp
        (λ y {xs} p → swap x y (xs ++ ys) ∙ ap (y ::_) p)
        (λ y z {xs} p → f-::-swap x y z ys p)
        xs

    f-::-swap-β : (x : A) {xs : SList A} (ys : SList A) (y z : A)
                → apd (λ xs → f-:: x {xs} ys) (swap y z xs) == f-::-swap x y z {xs} ys (f-:: x {xs} ys)
    f-::-swap-β x {xs} ys y z =
      SListRecPaths.rec-swap-β ⦃ trunc ⦄
        (λ xs → x :: xs ++ ys) (λ xs → xs ++ (x :: ys))
        idp
        (λ y {xs} p → swap x y (xs ++ ys) ∙ ap (y ::_) p)
        (λ y z {xs} p → f-::-swap x y z ys p)
        {y} {z} {xs}

    f-swap-aux : (x y : A) {xs : SList A} (ys : SList A)
              → ap (x ::_) (f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs)
              == swap x y (ys ++ xs) ∙ ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs)
    f-swap-aux x y {xs} ys =
      SListRec2Paths.rec ⦃ trunc ⦄
        (λ ys → x :: (y :: ys) ++ xs)
        (λ ys → ys ++ y :: x :: xs)
        (λ ys → ap (x ::_) (f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs))
        (λ ys → swap x y (ys ++ xs) ∙ ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs))
        ( ap (x ::_) (f-:: y {nil} xs) ∙ f-:: x {nil} (y :: xs) ∙' ap (nil ++_) (swap x y xs)
        =⟨ idp ⟩
          idp ∙' ap (idf _) (swap x y xs)
        =⟨ ∙'-unit-l (ap (idf _) (swap x y xs)) ⟩
          ap (idf _) (swap x y xs)
        =⟨ ap-idf (swap x y xs) ⟩
          swap x y xs
        =⟨ ! (∙-unit-r (swap x y xs)) ⟩
          swap x y xs ∙ idp
        =⟨ idp ⟩
          swap x y (nil ++ xs) ∙ ap (y ::_) (f-:: x {nil} xs) ∙ f-:: y {nil} (x :: xs)
        =∎)
        (λ z {ys} p →
          ap (x ::_) (f-:: y {z :: ys} xs) ∙ f-:: x {z :: ys} (y :: xs) ∙' ap ((z :: ys) ++_) (swap x y xs)
        =⟨ idp ⟩
          ap (x ::_) (swap y z (ys ++ xs) ∙ ap (z ::_) (f-:: y {ys} xs)) ∙ (swap x z (ys ++ y :: xs) ∙ ap (z ::_) (f-:: x {ys} (y :: xs))) ∙' ap ((z :: ys) ++_) (swap x y xs)
        =⟨ ap-∙ (x ::_) (swap y z (ys ++ xs)) (ap (z ::_) (f-:: y {ys} xs)) ∙ᵣ (swap x z (ys ++ y :: xs) ∙ ap (z ::_) (f-:: x {ys} (y :: xs))) ∙' ap ((z :: ys) ++_) (swap x y xs) ⟩
          (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ (swap x z (ys ++ y :: xs) ∙ ap (z ::_) (f-:: x {ys} (y :: xs))) ∙' ap ((z :: ys) ++_) (swap x y xs)
        =⟨ (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ₗ ∙∙'-assoc (swap x z (ys ++ y :: xs)) (ap (z ::_) (f-:: x {ys} (y :: xs))) (ap ((z :: ys) ++_) (swap x y xs)) ⟩
          (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ (swap x z (ys ++ y :: xs) ∙ (ap (z ::_) (f-:: x {ys} (y :: xs)) ∙' ap ((z :: ys) ++_) (swap x y xs)))
        =⟨ (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ₗ (swap x z (ys ++ y :: xs) ∙ₗ (ap (z ::_) (f-:: x {ys} (y :: xs)) ∙'ₗ ap-∘ (z ::_) (ys ++_) (swap x y xs))) ⟩
          (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ (swap x z (ys ++ y :: xs) ∙ (ap (z ::_) (f-:: x {ys} (y :: xs)) ∙' ap (z ::_) (ap (ys ++_) (swap x y xs))))
        =⟨ (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ₗ (swap x z (ys ++ y :: xs) ∙ₗ ∙'-ap (z ::_) (f-:: x {ys} (y :: xs)) (ap (ys ++_) (swap x y xs))) ⟩
          (ap (x ::_) (swap y z (ys ++ xs)) ∙ ap (x ::_) (ap (z ::_) (f-:: y {ys} xs))) ∙ (swap x z (ys ++ y :: xs) ∙ (ap (z ::_) (f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs))))
        =⟨ TODO ⟩
          ap (x ::_) (swap y z (ys ++ xs)) ∙ (ap (x ::_) (ap (z ::_) (f-:: y {ys} xs)) ∙ swap x z (ys ++ y :: xs)) ∙ (ap (z ::_) (f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs)))
        =⟨ TODO ⟩
          ap (x ::_) (swap y z (ys ++ xs)) ∙ (swap x z (y :: ys ++ xs) ∙ ap (z ::_) (ap (x ::_) (f-:: y {ys} xs))) ∙ (ap (z ::_) (f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs)))
        =⟨ TODO ⟩
          ap (x ::_) (swap y z (ys ++ xs)) ∙ (swap x z (y :: ys ++ xs)) ∙ ap (z ::_) (ap (x ::_) (f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs))
        =⟨ ap (x ::_) (swap y z (ys ++ xs)) ∙ₗ (swap x z (y :: ys ++ xs) ∙ₗ ap (ap (z ::_)) p) ⟩
          ap (x ::_) (swap y z (ys ++ xs)) ∙ swap x z (y :: ys ++ xs) ∙ ap (z ::_) (swap x y (ys ++ xs) ∙ ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs))
        =⟨ TODO ⟩
          ap (x ::_) (swap y z (ys ++ xs)) ∙ swap x z (y :: ys ++ xs) ∙ ap (z ::_) (swap x y (ys ++ xs)) ∙ ap (z ::_) (ap (y ::_) (f-:: x {ys} xs)) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ TODO ⟩
          (ap (x ::_) (swap y z (ys ++ xs)) ∙ swap x z (y :: ys ++ xs) ∙ ap (z ::_) (swap x y (ys ++ xs))) ∙ ap (z ::_) (ap (y ::_) (f-:: x {ys} xs)) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ ! (⬡ x y z (ys ++ xs)) ∙ᵣ (ap (z ::_) (ap (y ::_) (f-:: x {ys} xs)) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))) ⟩
          (swap x y (z :: ys ++ xs) ∙ ap (y ::_) (swap x z (ys ++ xs)) ∙ swap y z (x :: ys ++ xs)) ∙ ap (z ::_) (ap (y ::_) (f-:: x {ys} xs)) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ TODO ⟩
          swap x y (z :: ys ++ xs) ∙ ap (y ::_) (swap x z (ys ++ xs)) ∙ (swap y z (x :: ys ++ xs) ∙ ap (z ::_) (ap (y ::_) (f-:: x {ys} xs))) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ TODO ⟩
          swap x y (z :: ys ++ xs) ∙ ap (y ::_) (swap x z (ys ++ xs)) ∙ (ap (y ::_) (ap (z ::_) (f-:: x {ys} xs)) ∙ swap y z (ys ++ x :: xs)) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ TODO ⟩
          swap x y (z :: ys ++ xs) ∙ (ap (y ::_) (swap x z (ys ++ xs)) ∙ ap (y ::_) (ap (z ::_) (f-:: x {ys} xs))) ∙ swap y z (ys ++ x :: xs) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ swap x y (z :: ys ++ xs) ∙ₗ (! (ap-∙ (y ::_) (swap x z (ys ++ xs)) (ap (z ::_) (f-:: x {ys} xs))) ∙ᵣ swap y z (ys ++ x :: xs) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))) ⟩
          swap x y (z :: ys ++ xs) ∙ ap (y ::_) (swap x z (ys ++ xs) ∙ ap (z ::_) (f-:: x {ys} xs)) ∙ swap y z (ys ++ x :: xs) ∙ ap (z ::_) (f-:: y {ys} (x :: xs))
        =⟨ idp ⟩
          swap x y (z :: ys ++ xs) ∙ ap (y ::_) (f-:: x {z :: ys} xs) ∙ f-:: y {z :: ys} (x :: xs)
          =∎)
        ys

    f-swap : (x y : A) {xs : SList A} (ys : SList A)
           → (p : xs ++ ys == ys ++ xs)
           → (ap (x ::_) (ap (y ::_) p ∙ f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs)) == (ap (y ::_) (ap (x ::_) p ∙ f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs)) [ (λ zs → zs ++ ys == ys ++ zs) ↓ swap x y xs ]
    f-swap x y {xs} ys p =
      ↓-='-swap-in (_++ ys) (ys ++_)
        ( (ap (x ::_) (ap (y ::_) p ∙ f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs)) ∙' ap (ys ++_) (swap x y xs)
        =⟨ (ap-∙ (x ::_) (ap (y ::_) p) (f-:: y {ys} xs) ∙ᵣ f-:: x {ys} (y :: xs)) ∙'ᵣ ap (ys ++_) (swap x y xs) ⟩
          ((ap (x ::_) (ap (y ::_) p) ∙ ap (x ::_) (f-:: y {ys} xs)) ∙ f-:: x {ys} (y :: xs)) ∙' ap (ys ++_) (swap x y xs)
        =⟨ ∙-assoc (ap (x ::_) (ap (y ::_) p)) (ap (x ::_) (f-:: y {ys} xs)) (f-:: x {ys} (y :: xs)) ∙'ᵣ ap (ys ++_) (swap x y xs) ⟩
          (ap (x ::_) (ap (y ::_) p) ∙ ap (x ::_) (f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs)) ∙' ap (ys ++_) (swap x y xs)
        =⟨ ∙∙∙'-assoc (ap (x ::_) (ap (y ::_) p)) (ap (x ::_) (f-:: y {ys} xs)) (f-:: x {ys} (y :: xs)) (ap (ys ++_) (swap x y xs)) ⟩
          ap (x ::_) (ap (y ::_) p) ∙ ap (x ::_) (f-:: y {ys} xs) ∙ f-:: x {ys} (y :: xs) ∙' ap (ys ++_) (swap x y xs)
        =⟨ ap (x ::_) (ap (y ::_) p) ∙ₗ f-swap-aux x y {xs} ys ⟩
          ap (x ::_) (ap (y ::_) p) ∙ swap x y (ys ++ xs) ∙ ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs)
        =⟨ ! (∙-assoc (ap (x ::_) (ap (y ::_) p)) (swap x y (ys ++ xs)) (ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs))) ⟩
          (ap (x ::_) (ap (y ::_) p) ∙ swap x y (ys ++ xs)) ∙ ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs)
        =⟨ ! (swap-nat p) ∙ᵣ ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs) ⟩
          (swap x y (xs ++ ys) ∙ ap (y ::_) (ap (x ::_) p)) ∙ (ap (y ::_) (f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs))
        =⟨ ! (∙-assoc (swap x y (xs ++ ys) ∙ ap (y ::_) (ap (x ::_) p)) (ap (y ::_) (f-:: x {ys} xs)) (f-:: y {ys} (x :: xs))) ⟩
          ((swap x y (xs ++ ys) ∙ ap (y ::_) (ap (x ::_) p)) ∙ ap (y ::_) (f-:: x {ys} xs)) ∙ f-:: y {ys} (x :: xs)
        =⟨ ∙-assoc (swap x y (xs ++ ys)) (ap (y ::_) (ap (x ::_) p)) (ap (y ::_) (f-:: x {ys} xs)) ∙ᵣ f-:: y {ys} (x :: xs) ⟩
          (swap x y (xs ++ ys) ∙ (ap (y ::_) (ap (x ::_) p) ∙ ap (y ::_) (f-:: x {ys} xs))) ∙ f-:: y {ys} (x :: xs)
        =⟨ ∙-assoc (swap x y (xs ++ ys)) (ap (y ::_) (ap (x ::_) p) ∙ ap (y ::_) (f-:: x {ys} xs)) (f-:: y {ys} (x :: xs)) ⟩
          swap x y (xs ++ ys) ∙ (ap (y ::_) (ap (x ::_) p) ∙ ap (y ::_) (f-:: x {ys} xs)) ∙ f-:: y {ys} (x :: xs)
        =⟨ ! (++-r-swap-β ys) ∙ᵣ ((ap (y ::_) (ap (x ::_) p) ∙ ap (y ::_) (f-:: x {ys} xs)) ∙ f-:: y {ys} (x :: xs)) ⟩
           ap (_++ ys) (swap x y xs) ∙ (ap (y ::_) (ap (x ::_) p) ∙ ap (y ::_) (f-:: x {ys} xs)) ∙ f-:: y {ys} (x :: xs)
        =⟨ ap (_++ ys) (swap x y xs) ∙ₗ (∙-ap (y ::_) (ap (x ::_) p) (f-:: x {ys} xs) ∙ᵣ f-:: y {ys} (x :: xs)) ⟩
          ap (_++ ys) (swap x y xs) ∙ ap (y ::_) (ap (x ::_) p ∙ f-:: x {ys} xs) ∙ f-:: y {ys} (x :: xs)
        =∎)

    f : xs ++ ys == ys ++ xs
    f =
      SListRecPaths.rec ⦃ trunc ⦄
        (_++ ys) (ys ++_)
        (! (++-ρ.f ys))
        (λ x {xs} p → ap (x ::_) p ∙ f-:: x {ys} xs)
        (λ x y {xs} p → f-swap x y {xs} ys p)
        xs

  module ++-▽ (xs ys : SList A) where

    f : ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs)
    f =
      SListRec2Paths.rec ⦃ trunc ⦄
        (λ xs → (xs ++ nil) ++ ys)
        (λ xs → xs ++ ys)
        (λ xs → ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys))
        (λ xs → ap (_++ ys) (++-ρ.f xs))
        idp
        (λ x {xs} p →
            ap (x ::_) (++-α.f xs nil ys) ∙ idp
          =⟨ ∙-unit-r (ap (x ::_) (++-α.f xs nil ys)) ⟩
            ap (x ::_) (++-α.f xs nil ys)
          =⟨ ap (ap (x ::_)) (! (∙-unit-r (++-α.f xs nil ys))) ⟩
            ap (x ::_) (++-α.f xs nil ys ∙ idp)
          =⟨ ap (ap (x ::_)) p ⟩
            ap (x ::_) (ap (_++ ys) (++-ρ.f xs))
          =⟨ TODO ⟩
            ap (λ xs → x :: xs ++ ys) (++-ρ.f xs)
          =⟨ TODO ⟩
            ap (_++ ys) (ap (x ::_) (++-ρ.f xs))
          =∎)
        xs

  -- module ++-⬠ (ws xs ys zs : SList A) where

  --   f : ++-α.f (ws ++ xs) ys zs ∙ ++-α.f ws xs (ys ++ zs)
  --     == ap (_++ zs) (++-α.f ws xs ys) ∙ ++-α.f ws (xs ++ ys) zs ∙ ap (ws ++_) (++-α.f xs ys zs)
  --   f = TODO

  -- module ++-⬡ (xs ys zs : SList A) where

  --   f : ++-α.f xs ys zs ∙ ++-β.f xs (ys ++ zs) ∙ ++-α.f ys zs xs
  --     == ap (_++ zs) (++-β.f xs ys) ∙ ++-α.f ys xs zs ∙ ap (ys ++_) (++-β.f xs zs)
  --   f = TODO

  -- -- FIXME: this takes too long to typecheck
  -- instance
  --   SList-SMGStructure : SMGStructure (SList A) ⦃ ? ⦄
  --   SMGStructure.I SList-SMGStructure = nil
  --   SMGStructure._⊗_ SList-SMGStructure = _++_
  --   SMGStructure.α SList-SMGStructure X Y Z = ++-α.f X Y Z
  --   SMGStructure.Λ SList-SMGStructure X = ++-Λ.f X
  --   SMGStructure.ρ SList-SMGStructure X = ++-ρ.f X
  --   SMGStructure.β SList-SMGStructure X Y = ++-β.f X Y
  --   SMGStructure.▽ SList-SMGStructure X Y = ++-▽.f X Y
  --   SMGStructure.⬠ SList-SMGStructure W X Y Z = ++-⬠.f W X Y Z
  --   SMGStructure.⬡ SList-SMGStructure X Y Z = ++-⬡.f X Y Z
  --   SMGStructure.β² SList-SMGStructure X Y = ++-β².f X Y
