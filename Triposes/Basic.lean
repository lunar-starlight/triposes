import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Monotone.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Types
import Mathlib.Order.Category.HeytAlg

import Triposes.FPCatDSL2

section Tripos

  open CategoryTheory
  open MonoidalCategory

  /- We work over a cartesian closed category -/
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg}

  /- Helper functions to call P on unopped stuff -/
  def P₀ {P : 𝒞ᵒᵖ ⥤ HeytAlg} := P.obj ∘ .op
  def P₁ {P : 𝒞ᵒᵖ ⥤ HeytAlg} {X Y : 𝒞} : (f : X ⟶ Y) → P₀ (P := P) Y ⟶ P₀ (P := P) X := P.map ∘ .op

  class HasExists {X Y : 𝒞} (f : X ⟶ Y) where
    map : P₀ (P := P) X ⟶ P₀ Y
    adjTo   : ∀ {x : P₀ X} {y : P₀ Y}, (map x ≤ y) → (x ≤ P₁ f y)
    adjFrom : ∀ {x : P₀ X} {y : P₀ Y}, (x ≤ P₁ f y) → (map x ≤ y)

  class HasForall {X Y : 𝒞} (f : X ⟶ Y) where
    map : P₀ (P := P) X ⟶ P₀ Y
    adjTo   : ∀ {y : P₀ Y} {x : P₀ X}, (P₁ f y ≤ x) → (y ≤ map x )
    adjFrom : ∀ {y : P₀ Y} {x : P₀ X}, (y ≤ map x) → (P₁ f y ≤ x)

  class HasGeneric where
    𝕊 : 𝒞
    σ : P₀ (P := P) 𝕊
    bracket : ∀ {X : 𝒞} (_ : P₀ X), X ⟶ 𝕊
    σIsGeneric : ∀ {X : 𝒞} (φ : P₀ X), φ = P₁ (bracket φ) σ

  class Tripos (P : 𝒞ᵒᵖ ⥤ HeytAlg) where
    𝔼 : ∀ {X Y : 𝒞} (f : X ⟶ Y), HasExists (P := P) f
    𝔸 : ∀ {X Y : 𝒞} (f : X ⟶ Y), HasForall (P := P) f

    BeckChevalley : ∀ {X Y Z W : 𝒞} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W), IsPullback f g h k → (𝔸 f).map ∘ P₁ g = P₁ h ∘ (𝔸 k).map
