import Triposes.Basic
import Triposes.Language.Basic

open CategoryTheory
open MonoidalCategory

open Language

section Algebra
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {As : 𝒞}

  instance : LE (Formula (P := P) As) where
    le φ ψ := φ.eval ≤ ψ.eval

  syntax "unfold_quotient_le" : tactic
  syntax "full_eval" : tactic
  macro_rules
    | `(tactic| unfold_quotient_le) =>
      `(tactic| simp [LE.le, instLEFormula])
    | `(tactic| full_eval) =>
      `(tactic| simp [Formula.ι, Formula.app, Formula.impl, Formula.conj, Formula.disj, Formula.all, Formula.any, Formula.eval, Formula'.eval])
      -- `(tactic| repeat (first | unfold Formula.app | unfold Formula.impl | unfold Formula.conj | unfold Formula.disj | unfold Formula.all | unfold Formula.any))

  instance : Lattice (Formula (P := P) As) where
  -- instance : HeytingAlgebra (Formula (P := P) As) where
    le_refl _ := by unfold_quotient_le
    le_trans _ _ _ := le_trans
    le_antisymm φ ψ := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      rintro H K
      unfold_quotient
      simp [instLEFormula] at H
      simp [instLEFormula] at K
      apply_rules [le_antisymm]
    sup := Formula.disj
    le_sup_left φ ψ := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      unfold_quotient_le
      full_eval
    le_sup_right φ ψ := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      unfold_quotient_le
      full_eval
    sup_le φ ψ α := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      rintro H K
      unfold_quotient_le
      simp [instLEFormula] at H
      simp [instLEFormula] at K
      full_eval
      tauto
    inf := Formula.conj
    inf_le_left φ ψ := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      unfold_quotient_le
      full_eval
    inf_le_right φ ψ := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      unfold_quotient_le
      full_eval
    le_inf φ ψ α := by
      induction φ using Quotient.ind
      induction ψ using Quotient.ind
      induction α using Quotient.ind
      rintro H K
      unfold_quotient_le
      simp [instLEFormula] at H
      simp [instLEFormula] at K
      full_eval
      tauto

  instance : HeytingAlgebra (Formula (P := P) As) where
    himp := Formula.impl
    le_himp_iff φ ψ α := by
      apply φ.ind; apply ψ.ind; apply α.ind; rintro φ ψ α
      constructor
      · rintro H
        unfold LE.le Preorder.toLE PartialOrder.toPreorder SemilatticeSup.toPartialOrder
        unfold Lattice.toSemilatticeSup instLatticeFormula instLEFormula Formula.eval; simp
        conv =>
          enter [1]
          tactic =>
            unfold min SemilatticeInf.toMin SemilatticeInf.inf Lattice.toSemilatticeInf Formula.conj; simp
        conv => lhs; unfold Formula'.eval
        unfold LE.le Preorder.toLE PartialOrder.toPreorder SemilatticeSup.toPartialOrder at H
        unfold Lattice.toSemilatticeSup instLatticeFormula instLEFormula at H
        unfold Formula.eval Formula.impl at H; simp at H
        conv at H => rhs; unfold Formula'.eval
        apply_rules [le_himp_iff.mp]
      · rintro H
        unfold LE.le Preorder.toLE PartialOrder.toPreorder SemilatticeSup.toPartialOrder
        unfold Lattice.toSemilatticeSup instLatticeFormula instLEFormula
        unfold Formula.eval Formula.impl; simp
        conv => rhs; unfold Formula'.eval
        unfold LE.le Preorder.toLE PartialOrder.toPreorder SemilatticeSup.toPartialOrder at H
        unfold Lattice.toSemilatticeSup instLatticeFormula instLEFormula at H
        unfold Formula.eval at H; simp at H
        conv at H =>
          enter [1]
          tactic =>
            unfold min SemilatticeInf.toMin SemilatticeInf.inf Lattice.toSemilatticeInf Formula.conj; simp
        conv at H => lhs; unfold Formula'.eval
        apply_rules [le_himp_iff.mpr]
    top := Formula.tru
    le_top φ := le_top
    bot := Formula.fal
    bot_le φ := bot_le
    compl x := x.impl Formula.fal
    himp_bot _ := rfl

  section Formula
    variable (α β γ : Formula (P := P) As)

    def conj_top_eq : α.conj ⊤ = α := inf_top_eq α
    def top_conj_eq : Formula.tru.conj α = α := top_inf_eq α
    def conj_comm : α.conj β = β.conj α := inf_comm α β
    def conj_idem : α.conj α = α := inf_idem α
    def conj_assoc : (α.conj β).conj γ = α.conj (β.conj γ) := inf_assoc α β γ
    variable {β γ}
    def conj_le_conj_left : β ≤ γ → α.conj β ≤ α.conj γ := inf_le_inf_left α
    def conj_le_conj_right : β ≤ γ → β.conj α ≤ γ.conj α := inf_le_inf_right α
    variable {α}
    def conj_le_left : α.conj β ≤ α := inf_le_left
    def conj_le_right : α.conj β ≤ β := inf_le_right
    def le_conj : α ≤ β → α ≤ γ → α ≤ β.conj γ := le_inf
    def conj_eq_left : α.conj β = α ↔ α ≤ β := inf_eq_left
    def conj_eq_right : α.conj β = β ↔ β ≤ α := inf_eq_right
    def left_eq_conj : α = α.conj β ↔ α ≤ β := left_eq_inf
    def right_eq_conj : β = α.conj β ↔ β ≤ α := right_eq_inf

    variable (α β γ)
    def disj_comm : α.disj β = β.disj α := sup_comm α β
    def disj_idem : α.disj α = α := sup_idem α
    def disj_assoc : (α.disj β).disj γ = α.disj (β.disj γ) := sup_assoc α β γ

    def impl_conj_distrib : α.impl (β.conj γ) = (α.impl β).conj (α.impl γ) := himp_inf_distrib α β γ
    variable {α β} in
    def impl_eq_top_iff : α.impl β = ⊤ ↔ α ≤ β := himp_eq_top_iff
    variable {a} in
    def impl_self : α.impl α = ⊤ := himp_self

    lemma tru_eq_tru : Formula.tru (As := As) = q (P := P) Formula'.tru := by unfold_quotient

    variable {α β} in
    theorem conj_eq_top_iff : α.conj β = Formula.tru ↔ α = Formula.tru ∧ β = Formula.tru := by
      induction α using Quotient.ind
      induction β using Quotient.ind
      constructor
      · rintro H
        replace H := Quotient.eq.mp H
        simp [Formula'.eval] at H
        simp
        replace ⟨H, K⟩ := H
        constructor
        all_goals unfold_quotient; assumption
      · rintro ⟨H, K⟩
        rw [H, K]
        unfold_quotient; full_eval

    lemma iota_eval : Formula.ι (α.eval) = α := by
      induction α using Quotient.ind
      unfold_quotient
      full_eval

    variable {α β}
    def biimpl_eq_top_iff : (α.impl β).conj (β.impl α) = ⊤ ↔ α = β := by
      constructor
      · rintro H
        replace ⟨H, K⟩ := conj_eq_top_iff.mp H
        replace H := impl_eq_top_iff.mp H
        replace K := impl_eq_top_iff.mp K
        exact le_antisymm H K
      · rintro rfl
        rw [impl_self, conj_idem]

  end Formula
end Algebra

section Map
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {α α' : Formula (P := P) As} {β β' : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  @[simp]
  theorem map_id : Formula.app α (𝟙 As) = α := by
    induction α using Quotient.ind
    unfold_quotient
    full_eval
    aesop_cat

  theorem map_comp_app : γ.app (f ≫ g) = (γ.app g).app f := by
    induction γ using Quotient.ind
    unfold_quotient
    simp [Formula'.eval]
    aesop_cat

  theorem map_top_eq_top : Formula.app (P := P) ⊤ f = ⊤ := by
    unfold_quotient
    full_eval

  theorem map_conj : (β.conj β').app f = (β.app f).conj (β'.app f) := by
    induction β using Quotient.ind
    induction β' using Quotient.ind
    unfold_quotient
    full_eval

  theorem map_disj : (β.disj β').app f = (β.app f).disj (β'.app f) := by
    induction β using Quotient.ind
    induction β' using Quotient.ind
    unfold_quotient
    full_eval

  theorem map_impl : (β.impl β').app f = (β.app f).impl (β'.app f) := by
    induction β using Quotient.ind
    induction β' using Quotient.ind
    unfold_quotient
    full_eval

  variable (f) (β) in
  theorem weakening : β.app f ≤ α → β = ⊤ → α = ⊤ := by
    induction α using Quotient.ind
    induction β using Quotient.ind
    rintro le isTop
    rw [isTop] at le
    apply eq_top_iff.mpr
    trans Formula.app ⊤ f
    · apply le_of_eq
      unfold_quotient
      full_eval
    · exact le

  theorem map_monotone : β ≤ β' → β.app f ≤ β'.app f := by
    induction β using Quotient.ind
    induction β' using Quotient.ind
    intro H
    exact P₁.map_mono H

end Map

section FPCat
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z : 𝒞}
  open ChosenFiniteProducts

  theorem lift_diag {f : X ⟶ Y} : lift f f = f ≫ diag := by unfold diag; aesop_cat
  theorem lift_snd_fst : lift (fp.snd X Y) (fp.fst X Y) = twist := by unfold twist; aesop_cat
  theorem comp_lift_left {f : X ⟶ Y} {g : Y ⟶ Z} : lift (f ≫ g) f = f ≫ lift g (𝟙 _) := by aesop_cat
  theorem comp_lift_right {f : X ⟶ Y} {g : Y ⟶ Z} : lift f (f ≫ g) = f ≫ lift (𝟙 _) g := by aesop_cat
  theorem lift_comp_fst_comp_snd {f : X ⟶ Y ⊗ Z} : lift (f ≫ fp.fst _ _) (f ≫ fp.snd _ _) = f := by aesop_cat
  theorem diag_fst : diag ≫ fp.fst _ _ = 𝟙 X := by unfold diag; aesop_cat
  theorem diag_snd : diag ≫ fp.snd _ _ = 𝟙 X := by unfold diag; aesop_cat

  syntax "simp_proj" : tactic
  syntax "simp_proj_only" : tactic
  macro_rules
    | `(tactic| simp_proj_only) =>
      `(tactic| simp only
        [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
        ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp])
    | `(tactic| simp_proj) =>
      `(tactic| simp
        [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, diag_fst, diag_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl])

end FPCat

namespace Any
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z As Bs Cs : 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y} {z : P₀ (P := P) Z}
  variable {φ : Formula (P := P) X} {ψ : Formula (P := P) Y}
  variable {α α' : Formula (P := P) As} {β : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  lemma adj : (α ≤ β.app f) ↔ (Formula.any f α ≤ β) := by
    induction α using Quotient.ind
    induction β using Quotient.ind
    constructor
    · rintro H
      unfold_quotient_le
      exact (T.𝔼 _).adj.mp H
    · rintro H
      unfold_quotient_le
      exact (T.𝔼 _).adj.mpr H

  lemma unit : α ≤ Formula.app (Formula.any f α) f := by
    induction α using Quotient.ind
    unfold_quotient_le
    full_eval
    exact (T.𝔼 _).unit

  lemma counit : Formula.any f (Formula.app β f) ≤ β := by
    induction β using Quotient.ind
    unfold_quotient_le
    full_eval
    exact (T.𝔼 _).counit

  lemma id_adj_id : Formula.any (𝟙 _) α = α := by
    induction α using Quotient.ind
    unfold_quotient
    full_eval
    rw [(T.𝔼 _).id_adj_id]
    simp

  lemma frob_left : Formula.any f (α.conj (β.app f)) = (Formula.any f α).conj β := by
    induction α using Quotient.ind
    induction β using Quotient.ind
    unfold_quotient
    full_eval
    apply (T.𝔼 _).frob_left

  lemma frob_right : Formula.any f ((β.app f).conj α) = β.conj (Formula.any f α) := by
    rw [conj_comm, conj_comm β]
    exact frob_left

  lemma monotone : α ≤ α' → Formula.any f α ≤ Formula.any f α' := by
    induction α using Quotient.ind
    induction α' using Quotient.ind
    rintro H
    exact (T.𝔼 _).map.monotone H

  section BC
    variable {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}

    def BeckChevalley : IsPullback f g h k → ∀ {z : Formula (P := P) Z}, Formula.any f (z.app g) = (Formula.any k z).app h := by
      rintro isPB z
      induction z using Quotient.ind
      unfold_quotient
      full_eval
      apply T.𝔼_BeckChevalley isPB
  end BC

  theorem comp_app
    : Formula.any g (Formula.any f α) = Formula.any (f ≫ g) α := by
      apply le_antisymm
      · repeat apply adj.mp
        rw [←map_comp_app]
        have isPB : IsPullback (𝟙 _) (𝟙 _) (f ≫ g) (f ≫ g) := by sorry
        simp [←BeckChevalley isPB, id_adj_id]
      · apply adj.mp
        rw [map_comp_app]
        have isPB : IsPullback (𝟙 _) (𝟙 _) (g) (g) := by sorry
        have isPB' : IsPullback (𝟙 _) (𝟙 _) (f) (f) := by sorry
        simp [←BeckChevalley isPB, ←BeckChevalley isPB', id_adj_id]

  variable (f) in
  theorem iso_app {φ : IsIso f} : Formula.any g β = Formula.any (f ≫ g) (β.app f) := by
    have isPB : IsPullback (f ≫ g) (f) (𝟙 _) (g) := by
      apply IsPullback.of_iso (IsPullback.id_vert g)
      case e₁ => exact {
        hom := inv f
        inv := f
      }
      case e₂ => exact Iso.refl Cs
      case e₃ => exact Iso.refl Bs
      case e₄ => exact Iso.refl Cs
      all_goals aesop_cat
    rw [BeckChevalley isPB]
    simp

  open ChosenFiniteProducts
  theorem comm_app [fp : ChosenFiniteProducts 𝒞] {φ : Formula (P := P) ((X ⊗ Y) ⊗ Z)}
    : Formula.any (fp.fst X Y) (Formula.any (fp.fst (X ⊗ Y) Z) φ) = Formula.any (fp.fst X Z) (Formula.any (fp.fst (X ⊗ Z) Y) (φ.app (x : X, z : Z, y : Y ⊢ₑ ⟨⟨x, y⟩, z⟩))) := by
      repeat rw [comp_app]
      rw [iso_app (x : X, z : Z, y : Y ⊢ₑ ⟨⟨x, y⟩, z⟩)]
      · simp_proj
      · use x : X, y : Y, z : Z ⊢ₑ ⟨⟨x, z⟩, y⟩
        aesop_cat
end Any

namespace All
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y} {z : P₀ (P := P) Z}
  variable {φ : Formula (P := P) X} {ψ : Formula (P := P) Y}
  variable {α α' : Formula (P := P) As} {β : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  lemma adj : (β.app f ≤ α) ↔ (β ≤ Formula.all f α) := by
    induction α using Quotient.ind
    induction β using Quotient.ind
    constructor
    · rintro H
      unfold_quotient_le
      full_eval
      exact (T.𝔸 _).adj.mp H
    · rintro H
      unfold_quotient_le
      full_eval
      exact (T.𝔸 _).adj.mpr H

  lemma unit : β ≤ Formula.all f (Formula.app β f) := by
    induction β using Quotient.ind
    unfold_quotient_le
    full_eval
    exact (T.𝔸 _).unit

  lemma counit : Formula.app (Formula.all f α) f ≤ α := by
    induction α using Quotient.ind
    unfold_quotient_le
    full_eval
    exact (T.𝔸 _).counit

  lemma id_adj_id : Formula.all (𝟙 _) α = α := by
    induction α using Quotient.ind
    unfold_quotient
    full_eval
    rw [(T.𝔸 _).id_adj_id]
    simp

  -- lemma top_eq_top : (y : Y ⊢ₕ ∀ x : X , ⊤) = (y : Y ⊢ₕ ⊤ : Formula _ (T := T)) := by
  lemma top_eq_top : Formula.all (T := T) f ⊤ = ⊤ := by
    unfold_quotient
    full_eval
    exact (T.𝔸 _).top_eq_top

  variable (f) in
  lemma eq_top_iff_forall_eq_top : α = ⊤ ↔ (Formula.all f α) = ⊤ := by
    constructor
    · rintro rfl
      exact top_eq_top
    · rintro H
      apply eq_top_iff.mpr
      rw [←map_top_eq_top (f := f)]
      apply All.adj.mpr
      rw [H]

  lemma monotone : α ≤ α' → Formula.all f α ≤ Formula.all f α' := by
    induction α using Quotient.ind
    induction α' using Quotient.ind
    rintro H
    exact (T.𝔸 _).map.monotone H

  section BC
    variable {X Y Z W : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}

    def BeckChevalley : IsPullback f g h k → ∀ {z : Formula (P := P) Z}, Formula.all f (z.app g) = (Formula.all k z).app h := by
      rintro isPB z
      induction z using Quotient.ind
      unfold_quotient
      full_eval
      apply T.𝔸_BeckChevalley isPB
  end BC
end All

section Adjoints
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y} {z : P₀ (P := P) Z}
  variable {φ : Formula (P := P) X} {ψ : Formula (P := P) Y}
  variable {α : Formula (P := P) As} {β : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  lemma frobenius : Formula.all f (α ⇨ (Formula.app β f)) = (Formula.any f α) ⇨ β := by
    induction α using Quotient.ind
    induction β using Quotient.ind
    unfold_quotient
    full_eval
    apply T.frobenius

end Adjoints
