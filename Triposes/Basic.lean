import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
-- import Mathlib.Order.SymmDiff
-- import Mathlib.Order.Monotone.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Types
import Mathlib.Order.Category.HeytAlg

section Tripos

  open CategoryTheory
  open MonoidalCategory

  /- We work over a cartesian closed category -/
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]

  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg}

  -- instance {X Y} [HeytingAlgebra X] [HeytingAlgebra Y] {f : HeytingHom X Y} : Monotone f := by infer_instance
  -- @[coe]
  def HeytingHom.toOrderHom {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : OrderHom X Y := f
  def HeytingHom.monotone {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : Monotone f := by
    rintro a b a_le_b
    gcongr
    -- exact OrderHomClass.GCongr.mono f a_le_b

  def HeytingHom.map_top' {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : f ⊤ = ⊤ := by simp only [map_top]

  /- Helper functions to call P on unopped stuff -/
  abbrev P₀ := P.obj ∘ .op
  -- def P₁ {X Y : 𝒞} : (f : X ⟶ Y) → P.obj (.op Y) ⟶ P.obj (.op X) := P.map ∘ .op
  def P₁ {X Y : 𝒞} : (f : X ⟶ Y) → P₀ (P := P) Y ⟶ P₀ (P := P) X := P.map ∘ .op
  -- notation f "*" => P₁ f

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
  theorem P₁.map_himp {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} : P₁ f (y ⇨ y') = P₁ f y ⇨ P₁ f y' := by aesop_cat
  @[simp]
  theorem P₁.map_inf {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} : P₁ f (y ⊓ y') = P₁ f y ⊓ P₁ f y' := by aesop_cat
  @[simp]
  theorem P₁.map_sup {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} : P₁ f (y ⊔ y') = P₁ f y ⊔ P₁ f y' := by aesop_cat
  @[simp]
  theorem P₁.map_top {X Y : 𝒞} {f : X ⟶ Y} : P₁ (P := P) f ⊤ = ⊤ := by aesop_cat

  theorem P.map_comp' {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} {z : P.obj (.op Z)} : P.map (.op f) (P.map (.op g) z) = P.map (.op g ≫ .op f) z := by
    aesop_cat

  theorem P₁.map_mono {X Y : 𝒞} {f : X ⟶ Y} {y y' : P₀ (P := P) Y} (H : y ≤ y') : P₁ (P := P) f y ≤ P₁ (P := P) f y' := by
    apply OrderHomClass.GCongr.mono _ H

  @[reducible]
  def isTop {X : 𝒞} (t : P₀ (P := P) X) := t ≥ ⊤

  theorem P₁.map_isTop {X Y : 𝒞} {f : X ⟶ Y} {t : P₀ (P := P) Y} : isTop t → isTop (P₁ f t) := by
    rintro H
    simp at H
    rw [H]
    simp

  section Adjoints
    variable {X Y : 𝒞} (f : X ⟶ Y)

    class LeftAdjoint where
      map : OrderHom (P₀ (P := P) X) (P₀ Y)
      adj : ∀ {x : P₀ X} {y : P₀ Y}, (x ≤ P₁ f y) ↔ (map x ≤ y)

    class RightAdjoint where
      map : OrderHom (P₀ (P := P) X) (P₀ Y)
      adj : ∀ {y : P₀ Y} {x : P₀ X}, (P₁ f y ≤ x) ↔ (y ≤ map x )

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
        apply 𝔸.adj.mp
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
          apply 𝔸.adj.mp
          simp only [Function.comp_apply, le_inf_iff]
          constructor
          all_goals apply 𝔸.adj.mpr
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
        apply 𝔼.adj.mp
        simp

    instance : SupHomClass (LeftAdjoint (P := P) f) (P₀ (P := P) X) (P₀ (P := P) Y) where
      map_sup := by
        rintro 𝔼 a b
        apply le_antisymm
        case a =>
          apply 𝔼.adj.mp
          simp only [Function.comp_apply, sup_le_iff]
          constructor
          all_goals apply 𝔼.adj.mpr
          · apply le_sup_left
          · apply le_sup_right
        case a =>
          simp
          constructor
          repeat apply 𝔼.map.monotone; simp

    namespace LeftAdjoint
      variable {f : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ (P := P) Y}
      variable [𝔼 : LeftAdjoint (P := P) f]

      lemma unit : x ≤ P₁ f (𝔼 x) := by
        apply 𝔼.adj.mpr
        rfl

      lemma counit : 𝔼 (P₁ f y) ≤ y := by
        apply 𝔼.adj.mp
        rfl

      lemma id_adj_id [𝔼 : LeftAdjoint (P := P) (𝟙 X)] : 𝔼.map = OrderHom.id := by
        apply le_antisymm
        · apply OrderHom.le_def.mpr
          rintro x
          apply 𝔼.adj.mp
          unfold P₁
          aesop_cat
        · apply OrderHom.le_def.mpr
          rintro x
          simp
          trans
          · exact 𝔼.unit
          · unfold P₁
            aesop_cat

      lemma frob_left : 𝔼 (x ⊓ P₁ f y) = (𝔼 x) ⊓ y := by
        apply le_antisymm
        · apply le_inf
          all_goals apply 𝔼.adj.mp
          · trans
            · apply inf_le_left
            · apply 𝔼.unit
          · apply inf_le_right
        · apply le_himp_iff.mp
          apply 𝔼.adj.mp
          simp
          apply 𝔼.unit

      lemma frob_right : 𝔼 (P₁ f y ⊓ x) = y ⊓ (𝔼 x) := by
        rw [inf_comm, inf_comm y]
        exact 𝔼.frob_left

    end LeftAdjoint

    namespace RightAdjoint
      variable {f : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ (P := P) Y}
      variable [𝔸 : RightAdjoint (P := P) f]

      lemma unit : y ≤ 𝔸 (P₁ f y) := by
        apply 𝔸.adj.mp
        rfl

      lemma counit : P₁ f (𝔸 x) ≤ x := by
        apply 𝔸.adj.mpr
        rfl

      lemma id_adj_id [𝔸 : RightAdjoint (P := P) (𝟙 X)] : 𝔸.map = OrderHom.id := by
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
          apply 𝔸.adj.mp
          unfold P₁
          aesop_cat

      lemma top_eq_top : 𝔸 ⊤ = ⊤ := by
        apply top_le_iff.mp
        apply 𝔸.adj.mp
        simp

    end RightAdjoint

    lemma LeftAdjoint_congr {X Y : 𝒞} {f g : X ⟶ Y} (H: f = g) : LeftAdjoint (P := P) f = LeftAdjoint (P := P) g := congrArg LeftAdjoint H
    lemma RightAdjoint_congr {X Y : 𝒞} {f g : X ⟶ Y} (H : f = g) : RightAdjoint (P := P) f = RightAdjoint (P := P) g := congrArg RightAdjoint H

    lemma frobenius' {f : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ Y} [𝔸 : RightAdjoint f] [𝔼 : LeftAdjoint f]
      : 𝔸 (x ⇨ P₁ f y) = (𝔼 x) ⇨ y := by
      apply le_antisymm
      case a =>
        apply le_himp_comm.mp
        apply 𝔼.adj.mp
        simp only [Function.comp_apply, map_himp]
        apply le_himp_comm.mp
        apply 𝔸.counit
      case a =>
        apply 𝔸.adj.mp
        simp only [Function.comp_apply, map_himp]
        apply himp_le_himp_right
        apply 𝔼.unit

  end Adjoints

  class ChosenGeneric where
    𝕊 : 𝒞
    σ : P₀ (P := P) 𝕊
    bracket : ∀ {X : 𝒞} (_ : P₀ X), X ⟶ 𝕊
    σIsGeneric : ∀ {X : 𝒞} (φ : P₀ X), φ = P₁ (bracket φ) σ

  variable [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  class Tripos (P : 𝒞ᵒᵖ ⥤ HeytAlg) extends ChosenGeneric (P := P) where
    𝔼 : ∀ {X Y : 𝒞} (f : X ⟶ Y), LeftAdjoint (P := P) f
    𝔸 : ∀ {X Y : 𝒞} (f : X ⟶ Y), RightAdjoint (P := P) f

    BeckChevalley𝔼' : ∀ {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W},
      IsPullback f g h k → (𝔼 f).map ∘ P₁ g = P₁ h ∘ (𝔼 k).map
    BeckChevalley𝔸' : ∀ {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W},
      IsPullback f g h k → (𝔸 f).map ∘ P₁ g = P₁ h ∘ (𝔸 k).map

  namespace Tripos
    variable [T : Tripos P]

    section BC
      variable {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}

      def 𝔼_BeckChevalley : IsPullback f g h k → ∀ {z : P₀ Z}, T.𝔼 f (P₁ g z) = P₁ h (T.𝔼 k z) := by
        rintro isPB
        have cow := T.BeckChevalley𝔼' isPB
        apply funext_iff.mp at cow
        rintro z
        apply cow z
      def 𝔸_BeckChevalley : IsPullback f g h k → ∀ {z : P₀ Z}, T.𝔸 f (P₁ g z) = P₁ h (T.𝔸 k z) := by
        rintro isPB
        have cow := T.BeckChevalley𝔸' isPB
        apply funext_iff.mp at cow
        rintro z
        apply cow z
    end BC

    variable {X Y : 𝒞} {f g : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ (P := P) Y}

    def 𝔼_congr (H : f = g) : (T.𝔼 f).map = (T.𝔼 g).map := by aesop
    def 𝔼_congr_app (H : f = g) : T.𝔼 f x = T.𝔼 g x := by aesop
    def 𝔸_congr (H : f = g) : (T.𝔸 f).map = (T.𝔸 g).map := by aesop
    def 𝔸_congr_app (H : f = g) : T.𝔸 f x = T.𝔸 g x := by aesop

    omit fp ccc in lemma frobenius : T.𝔸 f (x ⇨ P₁ f y) = (T.𝔼 f x) ⇨ y := frobenius' (𝔸 := T.𝔸 f) (𝔼 := T.𝔼 f)
    omit fp ccc in lemma 𝔸_top_eq_top : T.𝔸 f ⊤ = ⊤ := (T.𝔸 f).top_eq_top

    omit fp ccc in lemma 𝔼_frob_left  : T.𝔼 f (x ⊓ P₁ f y) = (T.𝔼 f x) ⊓ y := (T.𝔼 f).frob_left
    omit fp ccc in lemma 𝔼_frob_right : T.𝔼 f (P₁ f y ⊓ x) = y ⊓ (T.𝔼 f x) := (T.𝔼 f).frob_right

    class TermLE {X Y : 𝒞} (t : P₀ (P := P) X) (u : P₀ Y) where
      map : Y ⟶ X
      le : P₁ map t ≤ u

    infixr:10 " ⊑ " => Tripos.TermLE

    namespace TermLE
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

      def isTop_le_isTop (H : isTop s) (φ : s ⊑ t) : isTop t := by
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

    end TermLE
  end Tripos

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
