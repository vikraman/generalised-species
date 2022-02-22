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
    f =
      SListRecPaths.rec ⦃ trunc ⦄
        (nil ++_) (idf _) idp (λ x p → ap (x ::_) p) f-swap xs

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

    f-::-nil-swap : (x y z : A) {xs : SList A} (p : x :: xs == xs ++ [ x ])
                  → (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs ∙ ap (z ::_) p)) == (swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs ∙ ap (y ::_) p)) [ (λ xs → x :: xs == xs ++ [ x ]) ↓ swap y z xs ]
    f-::-nil-swap x y z {xs} p =
      ↓-='-swap-in (x ::_) (_++ [ x ])
        ((swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs ∙ ap (z ::_) p)) ∙' ap (_++ [ x ]) (swap y z xs)
        =⟨ ap (_∙' ap (_++ [ x ]) (swap y z xs)) (ap (swap x y (z :: xs) ∙_) (ap-∙ (y ::_) (swap x z xs) (ap (z ::_) p))) ⟩
          (swap x y (z :: xs) ∙ (ap (y ::_) (swap x z xs) ∙ ap (y ::_) (ap (z ::_) p))) ∙' ap (_++ [ x ]) (swap y z xs)
        =⟨ ap (_∙' ap (_++ [ x ]) (swap y z xs)) (! (∙-assoc (swap x y (z :: xs)) (ap (y ::_) (swap x z xs)) (ap (y ::_) (ap (z ::_) p)))) ⟩
          ((swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) ∙ ap (y ::_) (ap (z ::_) p)) ∙' ap (_++ [ x ]) (swap y z xs)
        =⟨ ∙∙'-assoc (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) (ap (y ::_) (ap (z ::_) p)) (ap (_++ [ x ]) (swap y z xs)) ⟩
          (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) ∙ (ap (y ::_) (ap (z ::_) p) ∙' ap (_++ [ x ]) (swap y z xs))
        =⟨ ap ((swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) ∙_) TODO ⟩
          (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) ∙ (swap y z (x :: xs) ∙ ap (z ::_) (ap (y ::_) p))
        =⟨ ! (∙-assoc (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) (swap y z (x :: xs)) (ap (z ::_) (ap (y ::_) p))) ⟩
          ((swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs)) ∙ swap y z (x :: xs)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ TODO ⟩
          (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ ap (_∙ ap (z ::_) (ap (y ::_) p)) (⬡ x y z xs) ⟩
          (ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (_::_ z) (swap x y xs)) ∙ ap (z ::_) (ap (y ::_) p)
        =⟨ TODO ⟩
          ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (_::_ z) (swap x y xs ∙ ap (_::_ y) p) =∎)

    f-::-nil : (x : A) (ys : SList A) → x :: ys == ys ++ [ x ]
    f-::-nil x =
      SListRecPaths.rec ⦃ trunc ⦄
        (x ::_) (_++ [ x ])
        idp (λ y {ys} p → swap x y ys ∙ ap (y ::_) p)
        (λ y z {xs} p → f-::-nil-swap x y z p)

    f-:: : (x : A) {xs : SList A} (ys : SList A)
        → (x :: xs) ++ ys == ys ++ (x :: xs)
    f-:: x {xs} ys =
      SListRecPaths.rec ⦃ trunc ⦄
        (λ xs → x :: xs ++ ys) (λ xs → ys ++ (x :: xs))
        (f-::-nil x ys) TODO {!TODO!}
        xs

    f : xs ++ ys == ys ++ xs
    f =
      SListRecPaths.rec ⦃ trunc ⦄
        (_++ ys) (ys ++_)
        (! (++-ρ.f ys))
        (λ x {xs} p → TODO) -- ap (x ::_) p ∙ ap (_++ xs) (f-:: x ys) ∙ ++-α.f ys [ x ] xs)
        (λ x y {xs} p → TODO)
        xs

      -- SListElimSet.f {P = λ zs → zs ++ ys == ys ++ zs} ⦃ one-paths-level ⦄
      --   (! (++-ρ.f ys))
      --   (λ x {xs} p → ap (x ::_) p ∙ ap (_++ xs) (++-:: x ys) ∙ ++-α.f ys [ x ] xs)
      --   (λ x y {xs} p → TODO)
      --   xs

  -- module ++-▽ (xs ys : SList A) where

  --   f-nil-ys : ++-α.f nil nil ys ∙ ap (nil ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f nil)
  --   f-nil-ys =
  --     SListElimProp.f {P = λ ws → ap (nil ++_) (++-Λ.f ws) == idp}  ⦃ two-paths-level ⦄
  --       idp
  --       (λ x {xs} p →
  --         ap (nil ++_) (++-Λ.f (x :: xs)) =⟨ idp ⟩
  --         ap (nil ++_) (ap (x ::_) (++-Λ.f xs)) =⟨ ∘-ap (nil ++_) (x ::_) (++-Λ.f xs) ⟩
  --         ap (λ zs → nil ++ x :: zs) (++-Λ.f xs) =⟨ idp ⟩
  --         ap (x ::_) (++-Λ.f xs) =⟨ ap-∘ (x ::_) (nil ++_) (++-Λ.f xs) ⟩
  --         ap (x ::_) (ap (nil ++_) (++-Λ.f xs)) =⟨ ap (ap (x ::_)) p ⟩
  --         ap (x ::_) idp =∎)
  --       ys

  --   f-::-ys : (x : A) {xs : SList A}
  --           → ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs)
  --           → ++-α.f (x :: xs) nil ys ∙ ap ((x :: xs) ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f (x :: xs))
  --   f-::-ys x {xs} p =
  --     SListElimProp.f {P = λ ws → ++-α.f (x :: xs) nil ws ∙ ap ((x :: xs) ++_) (++-Λ.f ws) == ap (_++ ws) (++-ρ.f (x :: xs))} ⦃ two-paths-level ⦄
  --       (++-α.f (x :: xs) nil nil ∙ idp =⟨ TODO ⟩
  --        ap (_++ nil) (++-ρ.f (x :: xs)) =∎)
  --       TODO
  --       ys

  --   f : ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs)
  --   f =
  --     SListElimProp.f {P = λ zs → ++-α.f zs nil ys ∙ ap (zs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f zs)} ⦃ two-paths-level ⦄
  --       f-nil-ys
  --       f-::-ys
  --       xs

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
