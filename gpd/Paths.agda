{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import lib.Base
open import lib.Function
open import lib.PathOver
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.Funext hiding (λ=-∙)

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
$ g {idp} s = ap g s

λ=-idp : ∀ {i} {j} {A : Type i} {P : A → Type j} {f : Π A P}
       → λ= {f = f} {g = f} (λ x → idp {a = f x}) == idp
λ=-idp {f = f} = ! (λ=-η idp)

λ=-∙' : ∀ {i} {j} {A : Type i} {P : A → Type j} {f g h : Π A P} (α : f ∼ g) (β : g ∼ h)
       → λ= α ∙ λ= β == λ= (λ x → α x ∙ β x)
λ=-∙' {f = f} {g = g} α β =
    λ=-η (λ= α ∙ λ= β)
  ∙ ap λ= (λ= λ x → ap-∙ (λ γ → γ x) (λ= α) (λ= β) ∙ ap2 _∙_ (app=-β α x) (app=-β β x))