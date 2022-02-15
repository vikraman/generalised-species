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

  swap-inv : {x y : A} {xs : SList A} → swap x y xs == ! (swap y x xs)
  swap-inv {x = x} {y} {xs} = inv-∙ (swap x y xs) (swap y x xs) (swap² x y xs)

  ++-swap-β : {x y : A} {xs : SList A}
            → ap _++_ (swap x y xs) == λ= (λ ys → swap x y (xs ++ ys))
  ++-swap-β = app.f-swap-β

  ++-r-swap-β : {x y : A} {xs ys : SList A}
              → ap (_++ ys) (swap x y xs) == swap x y (xs ++ ys)
  ++-r-swap-β {x = x} {y} {xs} {ys} = TODO

  -- module ++-α (xs ys zs : SList A) where
  --   f : (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
  --   f =
  --     SListElimSet.f {P = λ xs* → (xs* ++ ys) ++ zs == xs* ++ (ys ++ zs)} ⦃ one-paths-level ⦄
  --       idp (λ x {xs*} p → ap (x ::_) p)
  --       (λ x y {xs*} p → TODO)
  --       xs

  -- module ++-Λ (xs : SList A) where
  --   f : nil ++ xs == xs
  --   f =
  --     SListElimSet.f {P = λ ys → nil ++ ys == ys} ⦃ one-paths-level ⦄
  --       idp (λ x {xs} p → ap (x ::_) p)
  --       (λ x y {xs} p → TODO)
  --       xs

  -- module ++-ρ (xs : SList A) where
  --   f : xs ++ nil == xs
  --   f =
  --     SListElimSet.f {P = λ ys → ys ++ nil == ys} ⦃ one-paths-level ⦄
  --       idp (λ x {xs} p → ap (x ::_) p)
  --       (λ x y {xs} p → TODO)
  --       xs

  -- module ++-β (xs ys : SList A) where

  --   ++-:: : (x : A) (xs : SList A) → x :: xs == xs ++ [ x ]
  --   ++-:: x =
  --     SListElimSet.f {P = λ ys → x :: ys == ys ++ [ x ]} ⦃ one-paths-level ⦄
  --       idp
  --       (λ y {ys} p → swap x y ys ∙ ap (y ::_) p)
  --       (λ y z {xs} xs* → TODO)

  --   f : xs ++ ys == ys ++ xs
  --   f =
  --     SListElimSet.f {P = λ zs → zs ++ ys == ys ++ zs} ⦃ one-paths-level ⦄
  --       (! (++-ρ.f ys))
  --       (λ x {xs} p → ap (x ::_) p ∙ ap (_++ xs) (++-:: x ys) ∙ ++-α.f ys [ x ] xs)
  --       (λ x y {xs} p → TODO)
  --       xs

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

  -- FIXME: this takes too long to typecheck
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
