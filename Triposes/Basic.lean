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
def p₂ {X Y : Type u} : X × Y → Y := fun ⟨_, y⟩ => y
def p₁ {X Y : Type u} : X × Y → X := fun ⟨x, _⟩ => x
def 𝔸π {P : TypeTripos} {X Y : Type u} := P.𝔸 (P.map (@p₂ X Y))

def p₂₃ {X Y Z : Type u} : X × Y × Z → Y × Z := fun ⟨_, y, z⟩ => ⟨y, z⟩
def p₁₃ {X Y Z : Type u} : X × Y × Z → X × Z := fun ⟨x, _, z⟩ => ⟨x, z⟩
def p₁₂ {X Y Z : Type u} : X × Y × Z → X × Y := fun ⟨x, y, _⟩ => ⟨x, y⟩


inductive Vec.{v} (A : Type v) : Nat → Type v where
  | nil : Vec A 0
  | cons : ∀ (a : A) {n : Nat} (as : Vec A n), Vec A (Nat.succ n)

namespace Vec

universe v

@[reducible]
def get {A : Type v} {len : Nat} : (as : Vec A len) → Fin len → A
  | cons a _,  ⟨0, _⟩ => a
  | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩


infixr:67 " :: " => Vec.cons

@[reducible]
def getSubvec {A : Type v} {len : Nat} (as : Vec A len) : (ns : List (Fin len)) → Vec A (ns.length)
  | [] => Vec.nil
  | n :: ns => as.get n :: Vec.getSubvec as ns

@[reducible]
def reduce {A : Type v} {len : Nat} (f : A → A → A) (emp : A) : Vec A len → A
  | nil => emp
  | a :: nil => a
  | a :: b :: as => f a (reduce f emp (b :: as))

-- @[reducible]
-- def prod {len : Nat} : Vec (Type v) len → Type v
--   | nil => PUnit
--   | a :: as => a × (prod as)
@[reducible]
def prod {len : Nat} : Vec (Type v) len → Type v
  | nil => PUnit
  | a :: nil => a
  | a :: b :: as => a × (prod (b :: as))

end Vec

@[reducible]
def tupleGet.{v} {len : Nat} {Xs : Vec (Type v) len} : Xs.prod → (n : Fin len) → Vec.get Xs n :=
fun xs n =>
  match len with
    | 0 => by apply n.elim0
    | Nat.succ len => by
      cases Xs; case cons X Xs =>
      cases Xs
      case nil =>
        cases n; case mk n isLt =>
        simp at isLt
        simp_rw [isLt]
        exact xs
      case cons Y Ys =>
        induction n; case mk n _ =>
        induction n
        case zero =>
          exact xs.1
        case succ =>
          unfold Vec.get
          apply tupleGet
          exact xs.2

@[reducible]
def proj (len : Nat) {Xs : Vec (Type u) len} (ns : List (Fin len)) : Xs.prod → (Xs.getSubvec ns).prod := fun xs =>
  match ns with
  | [] => PUnit.unit
  | [n] => tupleGet xs n
  | n :: m :: ns => ⟨ tupleGet xs n, proj len (m :: ns) xs ⟩

end Defn

section PER

-- To ni prav, ker to ni prava interpretacija
-- class PartialEquivalenceRelation (X : Type u) (P : TypeTripos) : Type (u + 1) where
--   rel : X → X → P.obj X
--   sym : ∀ {x y : X}, rel x y ≤ rel y x
--   trans : ∀ {x y z : X}, rel x y ⊓ rel y z ≤ rel x z
variable {X : Type u} (P : TypeTripos) (rel : P.obj (X × X))
#check P.map p₁₂ rel
#reduce (types := true) (X :: X :: X :: Vec.nil).prod
#reduce (types := true) ((X :: X :: X :: Vec.nil).getSubvec [0, 1]).prod
#check P.map (@proj 3 (X :: X :: X :: Vec.nil) [0, 1]) rel

def isTrue {P : TypeTripos} {Z : Type u} (p : P.obj Z) := (P.obj Z).str.top = p
def isTrue' {P : TypeTripos} {Z : Type u} (p : P.obj Z) := (P.obj PUnit).str.top = (P.𝔸 (fun _ => PUnit.unit)).map p

class PartialEquivalenceRelation (X : Type u) (P : TypeTripos) : Type (u + 1) where
  rel : P.obj (X × X)
  sym : isTrue (P.map (proj 2 [0, 1]) rel ⇨ P.map (proj 2 [1, 0]) rel)
  trans : isTrue (P.map p₁₂ rel ⊓ P.map p₂₃ rel ⇨ P.map p₁₂ rel)

class PartialEquivalenceRelationHom {X Y : Type u} {P : TypeTripos} (relX : PartialEquivalenceRelation X P) (relY : PartialEquivalenceRelation Y P) : Type (u + 1) where
  map : P.obj (X × Y)
  congrDom : isTrue (P.map p₁₂ relX.rel ⊓ P.map p₂₃ map ⇨ P.map p₁₃ map)
  congrCod : isTrue (P.map p₁₂ map ⊓ P.map p₂₃ relY.rel ⇨ P.map p₁₃ map)
  unique : isTrue (P.map p₁₂ map ⊓ P.map p₁₃ map ⇨ P.map p₂₃ relY.rel)
  total : isTrue (P.map diag relX.rel ⇨ (P.𝔼 p₁).map map)

end PER
