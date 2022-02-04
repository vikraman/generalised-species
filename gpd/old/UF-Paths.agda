{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

module gpd.UF-Paths where

-- pathover

PathOver : {A : 𝓤 ̇} (P : A → 𝓤 ̇) {x y : A} → (p : x ≡ y) → P x → P y → 𝓤 ̇
PathOver P p u v = transport P p u ≡ v

syntax PathOver P p u v = u ≡ v [ P ↓ p ]

■ : {A : 𝓤 ̇} {P : A → 𝓤 ̇ }
  → {x y z : A} {u : P x} {v : P y} {w : P z}
  → (p : x ≡ y) (q : y ≡ z)
  → u ≡ v [ P ↓ p ] → v ≡ w [ P ↓ q ] → u ≡ w [ P ↓ (p ∙ q) ]
■ refl refl s t = s ∙ t

$ : {A : 𝓤 ̇} {P : A → 𝓤 ̇}
  → {x y : A} {u : P x} {v : P y}
  → (f : A → A) (g : {x : A} → P x → P (f x))
  → (p : x ≡ y)
  → u ≡ v [ P ↓ p ] → g u ≡ g v [ P ↓ ap f p ]
$ f g refl s = ap g s

-- pathover constant fibrations

↓-cst-in : {A P : 𝓤 ̇} {x y : A} (p : x ≡ y)
         → {u v : P} (s : u ≡ v)
         → u ≡ v [ (λ _ → P) ↓ p ]
↓-cst-in refl s = s

↓-cst-in2 : {A P : 𝓤 ̇} {x y : A} {p q : x ≡ y}
          → {u v : P} {s t : u ≡ v}
          → (z : p ≡ q) (w : s ≡ t)
          → ↓-cst-in p s ≡ ↓-cst-in q t [ (λ w → u ≡ v [ (λ _ → P) ↓ w ]) ↓ z ]
↓-cst-in2 refl w = ap (↓-cst-in _) w

↓-cst-in-∙ : {A P : 𝓤 ̇} {x y z : A} (p : x ≡ y) (q : y ≡ z)
           → {u v w : P} (s : u ≡ v) (t : v ≡ w)
           → ↓-cst-in (p ∙ q) (s ∙ t) ≡ ■ p q (↓-cst-in p s) (↓-cst-in q t)
↓-cst-in-∙ refl refl s t = refl

■-cst : {A P : 𝓤 ̇} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → {u v w : P} (s : u ≡ v) (t : v ≡ w)
      → ■ p q (↓-cst-in p s) (↓-cst-in q t) ≡ ↓-cst-in (p ∙ q) (s ∙ t)
■-cst refl refl s t = refl

-- whiskering

_∙ᵣ_ : {A : 𝓤 ̇} {x y z : A} {p q : x ≡ y}
     → (α : p ≡ q) (r : y ≡ z)
     → p ∙ r ≡ q ∙ r
α ∙ᵣ refl = α

_∙ₗ_ : {A : 𝓤 ̇} {x y z : A} {q r : y ≡ z}
     → (p : x ≡ y) (β : q ≡ r)
     → p ∙ q ≡ p ∙ r
refl ∙ₗ β = refl-left-neutral ∙ β ∙ refl-left-neutral ⁻¹
