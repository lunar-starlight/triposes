import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
-- import Mathlib.Order.SymmDiff
-- import Mathlib.Order.Monotone.Basic
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
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]

  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg}

  -- instance {X Y} [HeytingAlgebra X] [HeytingAlgebra Y] {f : HeytingHom X Y} : Monotone f := by infer_instance
  -- @[coe]
  -- def HeytingHomCoe {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : OrderHom X Y := f
  def HeytingHom.monotone {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : Monotone f := by
    rintro a b a_le_b
    gcongr
    -- exact OrderHomClass.GCongr.mono f a_le_b

  def HeytingHom.map_top' {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : f ⊤ = ⊤ := by simp only [map_top]

  /- Helper functions to call P on unopped stuff -/
  abbrev P₀ := P.obj ∘ .op
  -- def P₁ {X Y : 𝒞} : (f : X ⟶ Y) → P.obj (.op Y) ⟶ P.obj (.op X) := P.map ∘ .op
  def P₁ {X Y : 𝒞} : (f : X ⟶ Y) → P₀ (P := P) Y ⟶ P₀ (P := P) X := P.map ∘ .op
  notation f "*" => P₁ f

  @[simp]
  theorem P₁.map_id {X : 𝒞} : P₁ (P := P) (𝟙 X) = HeytingHom.id _ := by
    unfold P₁
    aesop_cat

  @[simp]
  theorem P₁.map_comp {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} : P₁ (P := P) (f ≫ g) = P₁ g ≫ P₁ f := by
    unfold P₁
    aesop_cat
  @[simp]
  theorem P₁.map_comp_app {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} {z : P₀ (P := P) Z} : P₁ (f ≫ g) z = P₁ f (P₁ g z) := by
    unfold P₁
    aesop_cat

  @[simp]
  theorem P₁.map_himp {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} : P₁ f (y ⇨ y') = P₁ f y ⇨ P₁ f y' := by
    aesop_cat
  @[simp]
  theorem P₁.map_inf {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} : P₁ f (y ⊓ y') = P₁ f y ⊓ P₁ f y' := by
    aesop_cat
  @[simp]
  theorem P₁.map_sup {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} : P₁ f (y ⊔ y') = P₁ f y ⊔ P₁ f y' := by
    aesop_cat

  theorem P.map_comp' {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} {z : P.obj (.op Z)} : P.map (.op f) (P.map (.op g) z) = P.map (.op g ≫ .op f) z := by
    aesop_cat

  @[reducible]
  def isTop {X : 𝒞} (t : P₀ (P := P) X) := t ≥ ⊤

  section Adjoints
    variable {X Y : 𝒞} (f : X ⟶ Y)

    class LeftAdjoint where
      map : OrderHom (P₀ (P := P) X) (P₀ Y)
      adjTo   : ∀ {x : P₀ X} {y : P₀ Y}, (map x ≤ y) → (x ≤ P₁ f y)
      adjFrom : ∀ {x : P₀ X} {y : P₀ Y}, (x ≤ P₁ f y) → (map x ≤ y)

    class RightAdjoint where
      map : OrderHom (P₀ (P := P) X) (P₀ Y)
      adjTo   : ∀ {y : P₀ Y} {x : P₀ X}, (P₁ f y ≤ x) → (y ≤ map x )
      adjFrom : ∀ {y : P₀ Y} {x : P₀ X}, (y ≤ map x) → (P₁ f y ≤ x)

    instance : FunLike (RightAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      coe := fun f => f.map
      coe_injective' := by
        intro 𝔸 𝔸' eq
        cases 𝔸
        cases 𝔸'
        congr
        simp at eq
        exact eq

    instance : TopHomClass (RightAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      map_top := by
        rintro 𝔸
        apply top_unique
        apply 𝔸.adjTo
        simp

    instance : InfHomClass (RightAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      map_inf := by
        rintro 𝔸 a b
        apply le_antisymm
        case a =>
          simp
          constructor
          repeat apply 𝔸.map.monotone; simp
        case a =>
          apply 𝔸.adjTo
          simp only [Function.comp_apply, le_inf_iff]
          constructor
          all_goals apply 𝔸.adjFrom
          · apply inf_le_left
          · apply inf_le_right

    instance : FunLike (LeftAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      coe := fun f => f.map
      coe_injective' := by
        intro 𝔼 𝔼' eq
        cases 𝔼
        cases 𝔼'
        congr
        simp at eq
        exact eq

    instance : BotHomClass (LeftAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      map_bot := by
        rintro 𝔼
        apply bot_unique
        apply 𝔼.adjFrom
        simp

    instance : SupHomClass (LeftAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      map_sup := by
        rintro 𝔼 a b
        apply le_antisymm
        case a =>
          apply 𝔼.adjFrom
          simp only [Function.comp_apply, sup_le_iff]
          constructor
          all_goals apply 𝔼.adjTo
          · apply le_sup_left
          · apply le_sup_right
        case a =>
          simp
          constructor
          repeat apply 𝔼.map.monotone; simp

    lemma RightAdjoint.unit {f : X ⟶ Y} {y : P₀ (P := P) Y} {𝔸 : RightAdjoint f} : y ≤ 𝔸 (P₁ f y) := by
      apply 𝔸.adjTo
      rfl

    lemma RightAdjoint.counit {f : X ⟶ Y} {x : P₀ (P := P) X} {𝔸 : RightAdjoint f} : P₁ f (𝔸 x) ≤ x := by
      apply 𝔸.adjFrom
      rfl

    lemma LeftAdjoint.unit {f : X ⟶ Y} {x : P₀ (P := P) X} {𝔼 : LeftAdjoint f} : x ≤ P₁ f (𝔼 x) := by
      apply 𝔼.adjTo
      rfl

    lemma LeftAdjoint.counit {f : X ⟶ Y} {y : P₀ (P := P) Y} {𝔼 : LeftAdjoint f} : 𝔼 (P₁ f y) ≤ y := by
      apply 𝔼.adjFrom
      rfl

    lemma exists_universal_property {f : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ Y} [𝔸 : RightAdjoint f] [𝔼 : LeftAdjoint f]
      : 𝔸 (x ⇨ P₁ f y) = (𝔼 x) ⇨ y := by
      apply le_antisymm
      case a =>
        apply le_himp_comm.mp
        apply 𝔼.adjFrom
        simp only [Function.comp_apply, map_himp]
        apply le_himp_comm.mp
        apply 𝔸.counit
      case a =>
        apply 𝔸.adjTo
        simp only [Function.comp_apply, map_himp]
        apply himp_le_himp_right
        apply 𝔼.unit

    lemma exists_id_eq_id [𝔼 : LeftAdjoint (P := P) (𝟙 X)] : 𝔼.map = OrderHom.id := by
      apply le_antisymm
      · apply OrderHom.le_def.mpr
        rintro x
        apply 𝔼.adjFrom
        unfold P₁
        aesop_cat
      · apply OrderHom.le_def.mpr
        rintro x
        simp
        trans
        · exact 𝔼.unit
        · unfold P₁
          aesop_cat

    lemma forall_id_eq_id [𝔸 : RightAdjoint (P := P) (𝟙 X)] : 𝔸.map = OrderHom.id := by
      apply le_antisymm
      · apply OrderHom.le_def.mpr
        rintro x
        simp
        trans (P₁ (𝟙 X)) (𝔸 x)
        · unfold P₁
          aesop_cat
        · exact 𝔸.counit
      · apply OrderHom.le_def.mpr
        rintro x
        apply 𝔸.adjTo
        unfold P₁
        aesop_cat

    lemma forall_top_eq_top {f : X ⟶ Y} [𝔸 : RightAdjoint (P := P) f] : 𝔸 ⊤ = ⊤ := by
      apply top_le_iff.mp
      apply 𝔸.adjTo
      simp

  end Adjoints

  class HasGeneric where
    𝕊 : 𝒞
    σ : P₀ (P := P) 𝕊
    bracket : ∀ {X : 𝒞} (_ : P₀ X), X ⟶ 𝕊
    σIsGeneric : ∀ {X : 𝒞} (φ : P₀ X), φ = P₁ (bracket φ) σ

  variable [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  class Tripos (P : 𝒞ᵒᵖ ⥤ HeytAlg) where
    𝔼 : ∀ {X Y : 𝒞} (f : X ⟶ Y), LeftAdjoint (P := P) f
    𝔸 : ∀ {X Y : 𝒞} (f : X ⟶ Y), RightAdjoint (P := P) f

    BeckChevalley𝔼 : ∀ {X Y Z W : 𝒞} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W),
      IsPullback f g h k → (𝔼 f).map ∘ P₁ g = P₁ h ∘ (𝔼 k).map
    BeckChevalley𝔸 : ∀ {X Y Z W : 𝒞} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W),
      IsPullback f g h k → (𝔸 f).map ∘ P₁ g = P₁ h ∘ (𝔸 k).map

-- def eval [ConcreteCategory 𝒞] [T : Tripos P] {X Y : 𝒞} (v : P₀ (P := P) X) (f : P₀ (P := P) (X ⊗ Y)) : P₀ (P := P) Y :=
--   by
    -- have foo : Y ⟶ X := by sorry
    -- have cow := P₁ (P := P) (fp.lift foo (𝟙 Y))
    -- have cow : HeytingHom (P₀ (P := P) (X ⊗ Y)) (P₀ (P := P) Y) := by
    -- have cow := P₁ (fun ⟨x, y⟩ ↦ ⟨v,y⟩) f

  -- def Tripos.All [T : Tripos P] {X Y : 𝒞} : RightAdjoint (P := P) (fp.snd X Y) := T.𝔸 (fp.snd X Y)

  omit fp ccc in lemma Tripos.exists_universal_property' [T : Tripos P] {X Y : 𝒞} {f : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ Y}
    : T.𝔸 f (x ⇨ P₁ f y) = (T.𝔼 f x) ⇨ y := exists_universal_property (𝔸 := T.𝔸 f) (𝔼 := T.𝔼 f)
  omit fp ccc in lemma Tripos.forall_top_eq_top' [T : Tripos P] {X Y : 𝒞} {f : X ⟶ Y}
    : T.𝔸 f ⊤ = ⊤ := forall_top_eq_top (𝔸 := T.𝔸 f)

  class Tripos.TermLE {X Y : 𝒞}  (t : P₀ (P := P) X) (u : P₀ Y) where
    map : Y ⟶ X
    le : P₁ map t ≤ u

  infixr:10 " ⊑ " => Tripos.TermLE

  namespace Tripos.TermLE
    variable {X Y Z : 𝒞} {s : P₀ (P := P) X} {t : P₀ (P := P) Y} {r : P₀ (P := P) Z}
    variable [T : Tripos P]

    def refl : s ⊑ s where
      map := 𝟙 _
      le := by aesop_cat
    def trans (φ : s ⊑ t) (ψ : t ⊑ r) : s ⊑ r where
      map := ψ.map ≫ φ.map
      le := by
        rw [P₁.map_comp_app]
        trans (P₁ ψ.map) t
        · gcongr
          exact φ.le
        · exact ψ.le

    def isTop_le_isTop {φ : s ⊑ t} (H : isTop s) : isTop t := by
      simp at H
      rw [H] at φ
      simp
      apply eq_top_iff.mpr
      trans P₁ (P := P) φ.map ⊤
      · simp
      · exact φ.le

    def forall_le {f : X ⟶ Y} [𝔸 : RightAdjoint f] {x : P₀ (P := P) X} : 𝔸 x ⊑ x where
      map := f
      le := 𝔸.counit

  end Tripos.TermLE

  -- class Tripos.TermEq {X Y : 𝒞} (t : P₀ (P := P) X) (u : P₀ Y) where
  --   iso : X ≅ Y
  --   eq : P₁ iso.hom u = t

  -- infixr:10 " ≡ " => Tripos.TermEq
  -- namespace Tripos.TermEq

  --   def eq' (φ : t ≡ u) : u = P₁ φ.iso.inv t := by
  --     apply Eq.trans
  --     case b => exact P₁ φ.iso.inv (P₁ φ.iso.hom u)
  --     · rw [P₁.map_comp, φ.iso.inv_hom_id, P₁.map_id]
  --     · congr; exact φ.eq

  --   def refl : u ≡ u where
  --     iso := Iso.refl _
  --     eq := by rw [Iso.refl_hom, P₁.map_id]
  --   def symm (φ : t ≡ u) : u ≡ t where
  --     iso := Iso.symm φ.iso
  --     eq := by rw [Iso.symm_hom, ←φ.eq']
  --   def trans (φ : t ≡ u) (ψ : u ≡ v) : t ≡ v where
  --     iso := Iso.trans φ.iso ψ.iso
  --     eq := by rw [Iso.trans_hom, ←P₁.map_comp, ψ.eq ,φ.eq]

  --   def isTop_stable {φ : t ≡ u} (P : isTop t) : isTop u := by
  --     simp at P
  --     rw [P] at φ
  --     rw [φ.eq']
  --     simp
  -- end Tripos.TermEq
end Tripos
