{-# OPTIONS --without-K --exact-split --rewriting #-}

module gpd.SList.SMGStructure.2Paths where

open import gpd.Prelude
open import gpd.SList as SList
open import gpd.SMG
open import gpd.SList.SMGStructure.Tensor
open import gpd.SList.SMGStructure.1Paths

module _ {i} {A : Type i} where

  module ++-▽ (xs ys : SList A) where

    abstract
      f-:: : (x : A) {xs : SList A}
          → (p : ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs))
          → ++-α.f (x :: xs) nil ys ∙ ap ((x :: xs) ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f (x :: xs))
      f-:: x {xs} p =
          ap (x ::_) (++-α.f xs nil ys) ∙ idp
        =⟨ ∙-unit-r (ap (x ::_) (++-α.f xs nil ys)) ⟩
          ap (x ::_) (++-α.f xs nil ys)
        =⟨ ap (ap (x ::_)) (! (∙-unit-r (++-α.f xs nil ys))) ⟩
          ap (x ::_) (++-α.f xs nil ys ∙ idp)
        =⟨ ap (ap (x ::_)) p ⟩
          ap (x ::_) (ap (_++ ys) (++-ρ.f xs))
        =⟨ ∘-ap (x ::_) (_++ ys) (++-ρ.f xs) ⟩
          ap (λ xs → x :: xs ++ ys) (++-ρ.f xs)
        =⟨ ap-∘ (_++ ys) (x ::_) (++-ρ.f xs) ⟩
          ap (_++ ys) (ap (x ::_) (++-ρ.f xs))
        =∎

    f : ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys) == ap (_++ ys) (++-ρ.f xs)
    f =
      SListRec2Paths.rec ⦃ trunc ⦄
        (λ xs → (xs ++ nil) ++ ys)
        (λ xs → xs ++ ys)
        (λ xs → ++-α.f xs nil ys ∙ ap (xs ++_) (++-Λ.f ys))
        (λ xs → ap (_++ ys) (++-ρ.f xs))
        idp
        f-::
        xs

  module ++-⬠ (ws xs ys zs : SList A) where

    abstract
      f-nil : ++-α.f (nil ++ xs) ys zs ∙ ++-α.f nil xs (ys ++ zs)
           == ap (_++ zs) (++-α.f nil xs ys) ∙ ++-α.f nil (xs ++ ys) zs ∙ ap (nil ++_) (++-α.f xs ys zs)
      f-nil =
          ++-α.f xs ys zs ∙ idp
        =⟨ ∙-unit-r (++-α.f xs ys zs) ⟩
          ++-α.f xs ys zs
        =⟨ ! (ap-idf ((++-α.f xs ys zs))) ⟩
          ap (nil ++_) (++-α.f xs ys zs)
        =∎

      f-:: : (x : A) {ws : SList A}
          → (p : ++-α.f (ws ++ xs) ys zs ∙ ++-α.f ws xs (ys ++ zs)
          == ap (_++ zs) (++-α.f ws xs ys) ∙ ++-α.f ws (xs ++ ys) zs ∙ ap (ws ++_) (++-α.f xs ys zs))
          → ap (x ::_) (++-α.f (ws ++ xs) ys zs) ∙ ap (x ::_) (++-α.f ws xs (ys ++ zs))
          == ap (_++ zs) (ap (x ::_) (++-α.f ws xs ys)) ∙ ap (x ::_) (++-α.f ws (xs ++ ys) zs) ∙ ap ((x :: ws) ++_) (++-α.f xs ys zs)
      f-:: x {ws} p =
          ap (x ::_) (++-α.f (ws ++ xs) ys zs) ∙ ap (x ::_) (++-α.f ws xs (ys ++ zs))
        =⟨ ∙-ap (x ::_) (++-α.f (ws ++ xs) ys zs) (++-α.f ws xs (ys ++ zs)) ⟩
          ap (x ::_) (++-α.f (ws ++ xs) ys zs ∙ ++-α.f ws xs (ys ++ zs))
        =⟨ ap (ap (x ::_)) p ⟩
          ap (x ::_) (ap (_++ zs) (++-α.f ws xs ys) ∙ ++-α.f ws (xs ++ ys) zs ∙ ap (ws ++_) (++-α.f xs ys zs))
        =⟨ ap-∙∙ (x ::_) (ap (_++ zs) (++-α.f ws xs ys)) (++-α.f ws (xs ++ ys) zs) (ap (ws ++_) (++-α.f xs ys zs)) ⟩
          ap (x ::_) (ap (_++ zs) (++-α.f ws xs ys)) ∙ ap (x ::_) (++-α.f ws (xs ++ ys) zs) ∙ ap (x ::_) (ap (ws ++_) (++-α.f xs ys zs))
        =⟨ (∘-ap (x ::_) (_++ zs) (++-α.f ws xs ys) ∙ ap-∘ (_++ zs) (x ::_) (++-α.f ws xs ys)) ∙2 (ap (x ::_) (++-α.f ws (xs ++ ys) zs) ∙ₗ ∘-ap (x ::_) (ws ++_) (++-α.f xs ys zs)) ⟩
          ap (_++ zs) (ap (x ::_) (++-α.f ws xs ys)) ∙ ap (x ::_) (++-α.f ws (xs ++ ys) zs) ∙ ap ((x :: ws) ++_) (++-α.f xs ys zs)
        =∎

    f : ++-α.f (ws ++ xs) ys zs ∙ ++-α.f ws xs (ys ++ zs)
     == ap (_++ zs) (++-α.f ws xs ys) ∙ ++-α.f ws (xs ++ ys) zs ∙ ap (ws ++_) (++-α.f xs ys zs)
    f =
      SListRec2Paths.rec ⦃ trunc ⦄
        (λ ws → ((ws ++ xs) ++ ys) ++ zs)
        (λ ws → ws ++ xs ++ ys ++ zs)
        (λ ws → ++-α.f (ws ++ xs) ys zs ∙ ++-α.f ws xs (ys ++ zs))
        (λ ws → ap (_++ zs) (++-α.f ws xs ys) ∙ ++-α.f ws (xs ++ ys) zs ∙ ap (ws ++_) (++-α.f xs ys zs))
        f-nil
        f-::
        ws

  module ++-⬡ (xs ys zs : SList A) where

    abstract
      f-nil : ++-β.f nil (ys ++ zs) ∙ ++-α.f ys zs nil
           == ap (_++ zs) (++-β.f nil ys) ∙ ++-α.f ys nil zs ∙ ap (ys ++_) (++-β.f nil zs)
      f-nil =
        SListRec2Paths.rec ⦃ trunc ⦄
          (λ ys → (nil ++ ys) ++ zs)
          (λ ys → ys ++ (zs ++ nil))
          (λ ys → ++-β.f nil (ys ++ zs) ∙ ++-α.f ys zs nil)
          (λ ys → ap (_++ zs) (++-β.f nil ys) ∙ ++-α.f ys nil zs ∙ ap (ys ++_) (++-β.f nil zs))
          (∙-unit-r (++-β.f nil zs) ∙ ! (ap-idf (++-β.f nil zs)))
          (λ x {ys} p →
            ! (ap (x ::_) (++-ρ.f (ys ++ zs))) ∙ ap (x ::_) (++-α.f ys zs nil)
          =⟨ TODO ⟩
            ap (_++ zs) (! (ap (x ::_) (++-ρ.f ys))) ∙ ap (x ::_) (++-α.f ys nil zs) ∙ ap ((x :: ys) ++_) (! (++-ρ.f zs))
          =∎)
          ys

    f : ++-α.f xs ys zs ∙ ++-β.f xs (ys ++ zs) ∙ ++-α.f ys zs xs
     == ap (_++ zs) (++-β.f xs ys) ∙ ++-α.f ys xs zs ∙ ap (ys ++_) (++-β.f xs zs)
    f =
      SListRec2Paths.rec ⦃ trunc ⦄
        (λ xs → (xs ++ ys) ++ zs)
        (λ xs → ys ++ (zs ++ xs))
        (λ xs → ++-α.f xs ys zs ∙ ++-β.f xs (ys ++ zs) ∙ ++-α.f ys zs xs)
        (λ xs → ap (_++ zs) (++-β.f xs ys) ∙ ++-α.f ys xs zs ∙ ap (ys ++_) (++-β.f xs zs))
        f-nil
        TODO
        xs
