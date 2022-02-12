{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SMGStructure where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG

module _ {i} (A : Type i) where

  private
    one-paths-level : {xs ys : SList A} → is-set (xs == ys)
    one-paths-level = has-level-apply trunc _ _
    two-paths-level : {xs ys : SList A} {p q : xs == ys} → is-prop (p == q)
    two-paths-level = has-level-apply one-paths-level _ _

  app : SList A → SList A → SList A
  app =
    SListRec.f (λ ys → ys) (λ x f ys → x :: f ys)
               (λ x y f → λ= (λ ys → swap x y (f ys)))
               (λ x y z f →
                 let h1 = λ ys → swap x y (f ys)
                     h2 = λ ys → swap y x (f ys)
                 in ↯ (∙-λ=-seq h1 h2)
                  ∙ ap λ= (λ= λ ys → swap² x y (f ys))
                  ∙ λ=-idp)
               (λ x y z f → TODO)
               ⟨⟩

  infixr 40 _++_
  _++_ : SList A → SList A → SList A
  _++_ = app

  module ++-α (xs ys zs : SList A) where
    f : (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
    f =
      SListElimSet.f {P = λ xs* → (xs* ++ ys) ++ zs == xs* ++ (ys ++ zs)} ⦃ one-paths-level ⦄
        idp (λ x {xs*} p → ap (x ::_) p)
        (λ x y {xs*} p → TODO)
        xs

  module ++-Λ (xs : SList A) where
    f : nil ++ xs == xs
    f =
      SListElimSet.f {P = λ ys → nil ++ ys == ys} ⦃ one-paths-level ⦄
        idp (λ x {xs} p → ap (x ::_) p)
        (λ x y {xs} p → TODO)
        xs

  module ++-ρ (xs : SList A) where
    f : xs ++ nil == xs
    f =
      SListElimSet.f {P = λ ys → ys ++ nil == ys} ⦃ one-paths-level ⦄
        idp (λ x {xs} p → ap (x ::_) p)
        (λ x y {xs} p → TODO)
        xs

  module ++-β (xs ys : SList A) where

    ++-:: : (x : A) (xs : SList A) → x :: xs == xs ++ [ x ]
    ++-:: x =
      SListElimSet.f {P = λ ys → x :: ys == ys ++ [ x ]} ⦃ one-paths-level ⦄
        idp
        (λ y {ys} p → swap x y ys ∙ ap (y ::_) p)
        (λ y z {xs} xs* → TODO)

    f : xs ++ ys == ys ++ xs
    f =
      SListElimSet.f {P = λ zs → zs ++ ys == ys ++ zs} ⦃ one-paths-level ⦄
        (! (++-ρ.f ys))
        (λ x {xs} p → ap (x ::_) p ∙ ap (_++ xs) (++-:: x ys) ∙ ++-α.f ys [ x ] xs)
        (λ x y {xs} p → TODO)
        xs

  module ++-▽ (xs ys : SList A) where

    f-nil-ys : ++-α.f nil nil ys ∙ ap (nil ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f nil)
    f-nil-ys =
      SListElimProp.f {P = λ ws → ap (nil ++_) (++-Λ.f ws) == idp}  ⦃ two-paths-level ⦄
        idp
        (λ x {xs} p →
          ap (nil ++_) (++-Λ.f (x :: xs)) =⟨ idp ⟩
          ap (nil ++_) (ap (x ::_) (++-Λ.f xs)) =⟨ ∘-ap (nil ++_) (x ::_) (++-Λ.f xs) ⟩
          ap (λ zs → nil ++ x :: zs) (++-Λ.f xs) =⟨ idp ⟩
          ap (x ::_) (++-Λ.f xs) =⟨ ap-∘ (x ::_) (nil ++_) (++-Λ.f xs) ⟩
          ap (x ::_) (ap (nil ++_) (++-Λ.f xs)) =⟨ ap (ap (x ::_)) p ⟩
          ap (x ::_) idp =∎)
        ys

    f-::-ys : (x : A) {xs : SList A}
            → ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs)
            → ++-α.f (x :: xs) nil ys ∙ ap ((x :: xs) ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f (x :: xs))
    f-::-ys x {xs} p =
      SListElimProp.f {P = λ ws → ++-α.f (x :: xs) nil ws ∙ ap ((x :: xs) ++_) (++-Λ.f ws) == ap (_++ ws) (++-ρ.f (x :: xs))} ⦃ two-paths-level ⦄
        (++-α.f (x :: xs) nil nil ∙ idp =⟨ TODO ⟩
         ap (_++ nil) (++-ρ.f (x :: xs)) =∎)
        TODO
        ys

    f : ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs)
    f =
      SListElimProp.f {P = λ zs → ++-α.f zs nil ys ∙ ap (zs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f zs)} ⦃ two-paths-level ⦄
        f-nil-ys
        f-::-ys
        xs

  module ++-⬠ (ws xs ys zs : SList A) where

    f : ++-α.f (ws ++ xs) ys zs ∙ ++-α.f ws xs (ys ++ zs)
      == ap (_++ zs) (++-α.f ws xs ys) ∙ ++-α.f ws (xs ++ ys) zs ∙ ap (ws ++_) (++-α.f xs ys zs)
    f = TODO

  module ++-⬡ (xs ys zs : SList A) where

    f : ++-α.f xs ys zs ∙ ++-β.f xs (ys ++ zs) ∙ ++-α.f ys zs xs
      == ap (_++ zs) (++-β.f xs ys) ∙ ++-α.f ys xs zs ∙ ap (ys ++_) (++-β.f xs zs)
    f = TODO

  module ++-β² (xs ys : SList A) where

    f : ++-β.f xs ys ∙ ++-β.f ys xs == idp
    f = TODO

  instance
    SList-SMGStructure : SMGStructure (SList A)
    SMGStructure.I SList-SMGStructure = nil
    SMGStructure._⊗_ SList-SMGStructure = _++_
    SMGStructure.α SList-SMGStructure X Y Z = ++-α.f X Y Z
    SMGStructure.Λ SList-SMGStructure X = ++-Λ.f X
    SMGStructure.ρ SList-SMGStructure X = ++-ρ.f X
    SMGStructure.β SList-SMGStructure X Y = ++-β.f X Y
    SMGStructure.▽ SList-SMGStructure X Y = ++-▽.f X Y
    SMGStructure.⬠ SList-SMGStructure W X Y Z = ++-⬠.f W X Y Z
    SMGStructure.⬡ SList-SMGStructure X Y Z = ++-⬡.f X Y Z
    SMGStructure.β² SList-SMGStructure X Y = ++-β².f X Y
