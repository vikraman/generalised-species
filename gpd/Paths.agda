{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import lib.Base
open import lib.Function
open import lib.PathOver
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.Funext

module gpd.Paths where

_■_ : ∀ {i} {j}
    → {A : Type i} {P : A → Type j}
    → {x y z : A} {u : P x} {v : P y} {w : P z}
    → {p : x == y} {q : y == z}
    → u == v [ P ↓ p ] → v == w [ P ↓ q ] → u == w [ P ↓ (p ∙ q) ]
_■_ {p = idp} {idp} s t = s ∙ t

$ : ∀ {i} {j}
  → {A : Type i} {P : A → Type j}
  → {x y : A} {u : P x} {v : P y}
  → {f : A → A} (g : {x : A} → P x → P (f x))
  → {p : x == y}
  → u == v [ P ↓ p ] → g u == g v [ P ↓ ap f p ]
$ {P = P} {f = f} g {p} s = ↓-ap-in P f (ap↓ g s)

λ=-idp : ∀ {i} {j} {A : Type i} {P : A → Type j} {f : Π A P}
       → λ= {f = f} {g = f} (λ x → idp {a = f x}) == idp
λ=-idp {f = f} = ! (λ=-η idp)

λ=-∙' : ∀ {i} {j} {A : Type i} {P : A → Type j} {f g h : Π A P} (α : f ∼ g) (β : g ∼ h)
       → λ= α ∙ λ= β == λ= (λ x → α x ∙ β x)
λ=-∙' {f = f} {g = g} α β =
    λ=-η (λ= α ∙ λ= β)
  ∙ ap λ= (λ= λ x → ap-∙ (λ γ → γ x) (λ= α) (λ= β)
                    ∙ ap2 _∙_ (app=-β α x) (app=-β β x))

λ=-∙∙' : ∀ {i} {j} {A : Type i} {P : A → Type j} {e f g h : Π A P} (α : e ∼ f) (β : f ∼ g) (γ : g ∼ h)
       → λ= α ∙ λ= β ∙ λ= γ == λ= (λ x → α x ∙ β x ∙ γ x)
λ=-∙∙' {f = f} {g = g} {h = h} α β γ =
    λ=-η (λ= α ∙ λ= β ∙ λ= γ)
  ∙ ap λ= (λ= λ x → ap-∙∙ (λ δ → δ x) (λ= α) (λ= β) (λ= γ)
                    ∙ ap3 (λ p q r → p ∙ q ∙ r) (app=-β α x) (app=-β β x) (app=-β γ x))

inv-∙ : ∀ {i} {A : Type i} {x y : A} (p : x == y) (q : y == x) → p ∙ q == idp → p == ! q
inv-∙ p idp α = ! (∙-unit-r p) ∙ α

module _ {i} {A : Type i} where

  infixr 80 _∙'ᵣ_
  infixl 80 _∙'ₗ_

  _∙'ᵣ_ : {x y z : A} {p p' : x == y} (α : p == p') (q : y == z)
        → p ∙' q == p' ∙' q
  _∙'ᵣ_ {p = p} {p' = p'} α idp = α

  _∙'ₗ_ : {x y z : A} {q q' : y == z} (p : x == y) (β : q == q')
        → p ∙' q == p ∙' q'
  _∙'ₗ_ {q = q} {q' = q'} idp β = ∙'-unit-l q ∙ β ∙ ! (∙'-unit-l q')

  ∙∙-assoc : {x y z w v : A} (p : x == y) (q : y == z) (r : z == w) (s : w == v)
           → (p ∙ q ∙ r) ∙ s == p ∙ (q ∙ (r ∙ s))
  ∙∙-assoc p q r s = (! (∙-assoc p q r) ∙ᵣ s) ∙ ∙-assoc (p ∙ q) r s ∙ ∙-assoc p q (r ∙ s)

  ∙∙∙'-assoc : {x y z w v : A} (p : x == y) (q : y == z) (r : z == w) (s : w == v)
            → (p ∙ q ∙ r) ∙' s == p ∙ (q ∙ (r ∙' s))
  ∙∙∙'-assoc p q r s = ∙∙'-assoc p (q ∙ r) s ∙ (p ∙ₗ ∙∙'-assoc q r s)
