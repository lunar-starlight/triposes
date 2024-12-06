import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
--import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Monotone.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Types
import Mathlib.Order.Category.HeytAlg

universe u

section Defn

class LeftAdjoint {X Y : Type u} [Preorder X] [Preorder Y] (f : X → Y) : Type u where
  map : Y →o X
  adjTo   : ∀ {y : Y} {x : X}, (map y ≤ x) → (y ≤ f x)
  adjFrom : ∀ {y : Y} {x : X}, (y ≤ f x) → (map y ≤ x)

class RightAdjoint {X Y : Type u} [Preorder X] [Preorder Y] (f : X → Y) : Type u where
  map : Y →o X
  adjTo   : ∀ {x : X} {y : Y}, (f x ≤ y) → (x ≤ map y)
  adjFrom : ∀ {x : X} {y : Y}, (x ≤ map y) → (f x ≤ y)

def HeytingHomCoe {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : X →o Y := f

class TypeTripos : Type (u + 1) where
  obj : Type u → HeytAlg.{u}
  --objHA : (X : Type u) → HeytingAlgebra (obj X)
  map : {X Y : Type u} → (f : X → Y) → HeytingHom (obj Y) (obj X)

  𝔼 : {X Y : Type u} → (f : X → Y) → LeftAdjoint (map f)
  --𝔼 : {X Y : Type u} → (f : X → Y) → @LeftAdjoint (obj Y) (obj X) (by infer_instance) (by infer_instance) (map f)
  𝔸 : {X Y : Type u} → (f : X → Y) → RightAdjoint (map f)

  BeckChevalley : ∀ {X Y Z W : Type u} (f : X → Y) (g : X → Z) (h : Y → W) (k : Z → W), @CategoryTheory.IsPullback.{u, u+1} (Type u) CategoryTheory.types X Y Z W f g h k → (𝔸 f).map ∘ map g = map h ∘ (𝔸 k).map

  𝕊 : Type u
  σ : obj 𝕊
  bracket : ∀ {X : Type u} (φ : obj X), X → 𝕊
  σIsGeneric : ∀ {X : Type u} (φ : obj X), φ = map (bracket φ) σ

end Defn

section PER

-- To ni prav, ker to ni prava interpretacija
-- class PartialEquivalenceRelation (X : Type u) (P : TypeTripos) : Type (u + 1) where
--   rel : X → X → P.obj X
--   sym : ∀ {x y : X}, rel x y ≤ rel y x
--   trans : ∀ {x y z : X}, rel x y ⊓ rel y z ≤ rel x z

class PartialEquivalenceRelation (X : Type u) (P : TypeTripos) : Type (u + 1) where
  rel : P.obj (X × X)
  sym : 𝔸 (fun x y => y) (𝔸 (fun y => ()) rel …)
  trans : ∀ {x y z : X}, rel x y ⊓ rel y z ≤ rel x z

class PartialEquivalenceRelationHom {X Y : Type u} {P : TypeTripos} (relX : PartialEquivalenceRelation X P) (relY : PartialEquivalenceRelation Y P) : Type (u + 1) where
  map : P.obj (X×Y)
  congrDom : ∀ {x x' : X} {y : Y}, relX.rel x x' ⊓ map x' y ≤ map x y

end PER
