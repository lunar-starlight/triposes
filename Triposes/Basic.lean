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

def swap {X Y : Type u} : X × Y → Y × X := fun ⟨x, y⟩ => ⟨y, x⟩
def diag {X : Type u} : X → X × X := fun x => ⟨x, x⟩
def proj {X Y : Type u} : X × Y → Y := fun ⟨_, y⟩ => y
def proj' {X Y : Type u} : X × Y → X := fun ⟨x, _⟩ => x
def 𝔸π {P : TypeTripos} {X Y : Type u} := P.𝔸 (P.map (@proj X Y))

def proj₃₁ {X Y Z : Type u} : X × Y × Z → Y × Z := fun ⟨_, y, z⟩ => ⟨y, z⟩
def proj₃₂ {X Y Z : Type u} : X × Y × Z → X × Z := fun ⟨x, _, z⟩ => ⟨x, z⟩
def proj₃₃ {X Y Z : Type u} : X × Y × Z → X × Y := fun ⟨x, y, _⟩ => ⟨x, y⟩


end Defn

section PER

-- To ni prav, ker to ni prava interpretacija
-- class PartialEquivalenceRelation (X : Type u) (P : TypeTripos) : Type (u + 1) where
--   rel : X → X → P.obj X
--   sym : ∀ {x y : X}, rel x y ≤ rel y x
--   trans : ∀ {x y z : X}, rel x y ⊓ rel y z ≤ rel x z
variable {X : Type u} (P : TypeTripos) (rel : P.obj (X × X))
#check P.map proj₃₃ rel

def isTrue {P : TypeTripos} {Z : Type u} (p : P.obj Z) := (P.obj Z).str.top = p
def isTrue' {P : TypeTripos} {Z : Type u} (p : P.obj Z) := (P.obj PUnit).str.top = (P.𝔸 (fun _ => PUnit.unit)).map p

class PartialEquivalenceRelation (X : Type u) (P : TypeTripos) : Type (u + 1) where
  rel : P.obj (X × X)
  sym : isTrue (P.map id rel ⇨ P.map swap rel)
  trans : isTrue (P.map proj₃₃ rel ⊓ P.map proj₃₁ rel ⇨ P.map proj₃₃ rel)

class PartialEquivalenceRelationHom {X Y : Type u} {P : TypeTripos} (relX : PartialEquivalenceRelation X P) (relY : PartialEquivalenceRelation Y P) : Type (u + 1) where
  map : P.obj (X × Y)
  congrDom : isTrue (P.map proj₃₃ relX.rel ⊓ P.map proj₃₁ map ⇨ P.map proj₃₂ map)
  congrCod : isTrue (P.map proj₃₃ map ⊓ P.map proj₃₁ relY.rel ⇨ P.map proj₃₂ map)
  unique : isTrue (P.map proj₃₃ map ⊓ P.map proj₃₂ map ⇨ P.map proj₃₁ relY.rel)
  total : isTrue (P.map diag relX.rel ⇨ (P.𝔼 proj').map map)

end PER
