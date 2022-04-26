{-# OPTIONS --cubical #-}

module set.CCoMon where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as T
open import Agda.Primitive

open import set.Prelude
open import set.hRel
-- open import set.CMon using (CMon)
open import set.Day using (module day)

private
  variable
    ℓ : Level
    A B : Type ℓ

record CMon {ℓ} (C : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    e : II {ℓ} ⇸ C
    m : (C ⊗ C) ⇸ C
    isSetC : isSet C

  CSet : hSet ℓ
  CSet = C , isSetC

  field
    unit-l : m ⊚ ⊗[ idr CSet , e ] ≡ ρ CSet
    unit-r : m ⊚ ⊗[ e , idr CSet ] ≡ Λ CSet
    assocr : m ⊚ ⊗[ m , idr CSet ] ≡ m ⊚ ⊗[ idr CSet , m ] ⊚ α CSet CSet CSet
    comm : m ⊚ β CSet CSet ≡ m

record CCoMon {ℓ} (C : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    k : C ⇸ II {ℓ}
    w : C ⇸ (C ⊗ C)
    isSetC : isSet C

  CSet : hSet ℓ
  CSet = C , isSetC

  field
    counit-l : ⊗[ idr CSet , k ] ⊚ w ≡ ρ⁻¹ CSet
    counit-r : ⊗[ k , idr CSet ] ⊚ w ≡ Λ⁻¹ CSet
    coassoc : ⊗[ w , idr CSet ] ⊚ w ≡ α⁻¹ CSet CSet CSet ⊚ ⊗[ idr CSet , w ] ⊚ w
    cocomm : β CSet CSet ⊚ w ≡ w

open import set.MSet
open import set.MSet.Universal as M using (_++_ ; MSetCMon)
open import set.Power as P

-- module _ {ℓ} {A : Type ℓ} (C : CMon A) where

--   module C = CMon C
--   open C

--   _∗ : (B → A) → (B ⇸ A)
--   _∗ = _# {BSet = A , isSetM}

--   ∇ : CCoMon A
--   CCoMon.k ∇ = (const e ∗) †
--   CCoMon.w ∇ = ((uncurry C._⊗_) ∗) †
--   CCoMon.isSetC ∇ = isSetM
--   CCoMon.counit-l ∇ =
--     funExt λ a → funExt λ { (b , tt*) →
--       ⇔toPath (rec (isSet× isSetM isSetUnit* (a , tt*) (b , tt*))
--                  λ { ((x , y) , (ϕ , ψ) , δ) → ≡-× (δ ⁻¹ ∙ cong₂ C._⊗_ ϕ (ψ ⁻¹) ∙ unitr-⊗ b) refl })
--                (λ p → ∣ (a , e) , (cong fst p , refl) , unitr-⊗ a ∣) }
--   CCoMon.counit-r ∇ =
--     funExt λ a → funExt λ { (tt* , b) →
--       ⇔toPath (rec (isSet× isSetUnit* isSetM (tt* , a) (tt* , b))
--                    λ { ((x , y) , (ϕ , ψ) , δ) → ≡-× refl (δ ⁻¹ ∙ cong₂ C._⊗_ (ϕ ⁻¹) ψ ∙ comm-⊗ e b ∙ unitr-⊗ b) })
--                (λ p → ∣ (e , a) , (refl , cong snd p) , comm-⊗ e a ∙ unitr-⊗ a ∣) }
--   CCoMon.coassoc ∇ =
--     funExt λ a → funExt λ { ((b , c) , d) →
--       ⇔toPath (T.map (λ { ((x , y) , (ϕ , ψ) , δ) → (b , (c , d)) , refl , ∣ (x , y) , (TODO , TODO) , TODO ∣ }))
--                (T.map λ { ((x , (y , z)) , ϕ , δ) → (TODO , TODO) , (TODO , TODO) , TODO }) }
--   CCoMon.cocomm ∇ =
--     funExt λ a → funExt λ { (b , c) →
--       ⇔toPath (rec (isSetM (b C.⊗ c) a) λ { ((x , y) , ϕ , ψ) → cong₂ C._⊗_ (cong fst (ϕ ⁻¹)) (cong snd (ϕ ⁻¹)) ∙ comm-⊗ y x ∙ ψ })
--                (λ p → ∣ (c , b) , refl , comm-⊗ c b ∙ p ∣) }

-- MSetCCoMon : CCoMon (MSet A)
-- MSetCCoMon = ∇ (MSetCMon _)

-- module univ {M : Type _} (C : CMon M) (f : M ⇸ A) where

--   f♯ : M ⇸ MSet A
--   f♯ = M.univ.f♯ (day.ℙMCMon {{C}}) (f †) †

-- open univ
