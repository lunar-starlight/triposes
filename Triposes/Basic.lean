import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
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

  /- `HeytingHom` is missing monotonicity -/
  def HeytingHom.monotone {X Y : Type} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) : Monotone f := by
    rintro a b a_le_b
    gcongr

  /- Helper functions to call `P` on unopped stuff -/
  def P₀ (X : 𝒞) := P.obj (.op X)
  def P₁ {X Y : 𝒞} : (f : X ⟶ Y) → P₀ (P := P) Y ⟶ P₀ (P := P) X := P.map ∘ .op

  /- Lean forgets `P₁` is a functor -/
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

  /- Lean forgets `P₁` maps to HeytAlg -/
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

  section Adjoints

    /-- A choice of adjoints for all morphisms -/
    class ChosenLeftAdjoints where
      /-- The underlying map of the adjoint `∃_f` -/
      map : {X Y : 𝒞} → (X ⟶ Y) → OrderHom (P₀ (P := P) X) (P₀ Y)
      /-- The adjunction property `x ≤ f* y ⇔ ∃_f x ≤ y` -/
      adj : ∀ {X Y : 𝒞} {f : X ⟶ Y} {x : P₀ X} {y : P₀ Y}, (x ≤ P₁ f y) ↔ (map f x ≤ y)

    namespace ChosenLeftAdjoints
      variable {X Y : 𝒞} {f : X ⟶ Y}
      variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y}
      variable [𝔼 : ChosenLeftAdjoints (P := P)]

      /-- The unit of the adjunction `∃_f ⊣ f*` -/
      lemma unit : x ≤ P₁ f (𝔼.map f x) := by
        apply 𝔼.adj.mpr
        rfl

      /-- The counit of the adjunction `∃_f ⊣ f*` -/
      lemma counit : 𝔼.map f (P₁ f y) ≤ y := by
        apply 𝔼.adj.mp
        rfl

      /-- The proposition that `∃_𝟙` is the identity morphism -/
      lemma id_adj_id : 𝔼.map (𝟙 X) = OrderHom.id := by
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
          · exact 𝔼.unit (f := 𝟙 X)
          · aesop_cat

      /-- The left frobenius condition -/
      lemma frob_left : 𝔼.map f (x ⊓ P₁ f y) = (𝔼.map f x) ⊓ y := by
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

      /-- The right frobenius condition -/
      lemma frob_right : 𝔼.map f (P₁ f y ⊓ x) = y ⊓ (𝔼.map f x) := by
        rw [inf_comm, inf_comm y]
        exact 𝔼.frob_left

    end ChosenLeftAdjoints

    class ChosenRightAdjoints where
      /-- The underlying map of the adjoint `∀_f` -/
      map : {X Y : 𝒞} → (X ⟶ Y) → OrderHom (P₀ (P := P) X) (P₀ Y)
      /-- The adjunction property `f* x ≤ y ⇔ x ≤ ∀_f y` -/
      adj : ∀ {X Y : 𝒞} {f : X ⟶ Y} {y : P₀ Y} {x : P₀ X}, (P₁ f y ≤ x) ↔ (y ≤ map f x )

    namespace ChosenRightAdjoints
      variable {X Y : 𝒞} {f : X ⟶ Y}
      variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y}
      variable [𝔸 : ChosenRightAdjoints (P := P)]

      /-- The unit of the adjunction `f* ⊣ ∀_f` -/
      lemma unit : y ≤ 𝔸.map f (P₁ f y) := by
        apply 𝔸.adj.mp
        rfl

      /-- The counit of the adjunction `f* ⊣ ∀_f` -/
      lemma counit : P₁ f (𝔸.map f x) ≤ x := by
        apply 𝔸.adj.mpr
        rfl

      /-- The proposition that `∀_𝟙` is the identity morphism -/
      lemma id_adj_id : 𝔸.map (𝟙 X) = OrderHom.id := by
        apply le_antisymm
        · apply OrderHom.le_def.mpr
          rintro x
          simp
          apply le_trans'
          · exact 𝔸.counit (f := 𝟙 X)
          · aesop_cat
        · apply OrderHom.le_def.mpr
          rintro x
          apply 𝔸.adj.mp
          unfold P₁
          aesop_cat

      /-- The proposition that `∀_f` preserves the top element -/
      lemma top_eq_top : 𝔸.map f ⊤ = ⊤ := by
        apply top_le_iff.mp
        apply 𝔸.adj.mp
        simp

    end ChosenRightAdjoints

    /-- The proposition that `∀_f(φ(x) ⇒ ψ) = (∃_f φ(x)) ⇒ ψ` -/
    lemma frobenius' {X Y : 𝒞} {f : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ Y} [𝔸 : ChosenRightAdjoints] [𝔼 : ChosenLeftAdjoints]
      : 𝔸.map f (x ⇨ P₁ f y) = (𝔼.map f x) ⇨ y := by
      apply le_antisymm
      case a =>
        apply le_himp_comm.mp
        apply 𝔼.adj.mp
        rw [map_himp]
        apply le_himp_comm.mp
        apply 𝔸.counit
      case a =>
        apply 𝔸.adj.mp
        rw [map_himp]
        apply himp_le_himp_right
        apply 𝔼.unit

  end Adjoints

  /-- The generic object -/
  class ChosenGeneric where
    𝕊 : 𝒞
    σ : P₀ (P := P) 𝕊
    bracket : ∀ {X : 𝒞} (_ : P₀ X), X ⟶ 𝕊
    σIsGeneric : ∀ {X : 𝒞} (φ : P₀ X), φ = P₁ (bracket φ) σ

  variable [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  -- class Pullback {P X Y Z : 𝒞} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) extends
  --   CommSq fst snd f g : Prop where
  --   isLimit : ∀ {T : 𝒞} {x : T ⟶ X} {y : T ⟶ Y} {_ : x ≫ f = y ≫ g}, (∃! p : T ⟶ P, p ≫ fst = x ∧ p ≫ snd = y)

  variable (P) in
  /-- A tripos is a contravariant functor `P`, with chosen left and right adjoints
      to substitutions, the corresponding Beck-Chevalley rules, and a chosen
      generic object -/
  class Tripos extends ChosenGeneric (P := P) where
    /-- The existential quantifier -/
    𝔼 : ChosenLeftAdjoints (P := P)
    /-- The universal quantifier -/
    𝔸 : ChosenRightAdjoints (P := P)

    /-- For the pullback square
        ```
        X ---f---> Y
        |          |
        g          h
        |          |
        v          v
        Z ---k---> W
        ```
        the proposition `∃_f (g* z) = g* (∃_k z)` -/
    𝔼_BeckChevalley : ∀ {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} {z : P₀ Z},
      IsPullback f g h k →  𝔼.map f (P₁ g z) = P₁ h (𝔼.map k z)

    /-- For the pullback square
        ```
        X ---f---> Y
        |          |
        g          h
        |          |
        v          v
        Z ---k---> W
        ```
        the proposition `∀_f (g* z) = g* (∀_k z)` -/
    𝔸_BeckChevalley : ∀ {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} {z : P₀ Z},
      IsPullback f g h k → 𝔸.map f (P₁ g z) = P₁ h (𝔸.map k z)

  namespace Tripos
    variable [T : Tripos P]
    variable {X Y : 𝒞} {f g : X ⟶ Y} {x : P₀ (P := P) X} {y : P₀ (P := P) Y}

    omit fp ccc in
    /-- The proposition that `∀_f(φ(x) ⇒ ψ) = (∃_f φ(x)) ⇒ ψ` -/
    lemma frobenius : T.𝔸.map f (x ⇨ P₁ f y) = (T.𝔼.map f x) ⇨ y := frobenius' (𝔸 := T.𝔸) (𝔼 := T.𝔼)

  end Tripos
end Tripos
