import Triposes.PER.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types

open Language
open CategoryTheory
open MonoidalCategory


section Defn

  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  open ChosenFiniteProducts

  instance Tripos.category : Category (Σ X : 𝒞, PER (P := P) X) where
    Hom X Y := PERHom (𝒞 := 𝒞) X.2 Y.2
    comp f g := PERHomComp g f
    id X := {
        hom := X.2.rel
        congrDom := X.2.trans
        congrCod := X.2.trans
        unique := by
          replace ⟨X, ρX⟩ := X
          simp_proj
          apply impl_eq_top_iff.mpr
          have H := impl_eq_top_iff.mp ρX.sym
          have H' := map_monotone (f := twist) H
          simp [←map_comp_app] at H
          simp [←map_comp_app, twist] at H'
          replace H := le_antisymm H H'
          simp [lift_snd_fst] at H

          conv => enter [1, 1]; rw [H]
          unfold twist; simp [←map_comp_app, comp_lift]

          have K := impl_eq_top_iff.mp ρX.trans
          replace K := map_monotone (f := x : X, y : X, z : X ⊢ₑ ⟨⟨y, x⟩, z⟩) K
          simp only [map_conj, lift_fst, lift_snd, comp_lift, Category.comp_id, ←Category.assoc, ←map_comp_app] at K
          exact K
        total := by
          replace ⟨X, ρX⟩ := X
          apply biimpl_eq_top_iff.mpr
          simp_proj
          apply le_antisymm
          · exact impl_eq_top_iff.mp ρX.extent_le_exists_rel
          · apply Any.adj.mp
            have H := biimpl_eq_top_iff.mp ρX.rel_le_extent_left
            simp only [Category.comp_id, lift_diag, lift_fst_snd, map_id] at H
            simp_proj
            exact conj_eq_right.mp H
        }
    id_comp := by
      rintro ⟨X, ρX⟩ ⟨Y, ρY⟩ f
      apply PERHom_ext
      unfold PERHom.hom
      unfold CategoryStruct.id CategoryStruct.comp
      unfold PERHomComp PERHom.hom
      simp
      apply le_antisymm
      · have H := impl_eq_top_iff.mp f.congrDom; simp at H
        replace H := map_monotone (T := T) (f := x : X, y : Y, x' : X ⊢ₑ ⟨⟨x, x'⟩, y⟩) H
        simp only [lift_comp_fst_comp_snd, map_conj, ←map_comp_app, lift_fst, lift_snd, comp_lift, ←Category.assoc, Category.comp_id] at H

        apply le_trans
        · apply Any.monotone
          exact H
        apply le_trans
        · exact Any.counit
        · full_eval
          rfl
      · apply le_trans
        · have H := impl_eq_top_iff.mp f.map_le_extent_dom
          simp at H
          exact le_conj H (le_refl _)
        · simp_proj
          have H : ((Formula.ι ρX.rel).app ((fp.fst X Y) ≫ diag) ⊓ f.hom) =
            ((Formula.ι ρX.rel).app (x : X, y : Y, x' : X ⊢ₑ ⟨x, x'⟩) ⊓ (Formula.ι f.hom).app (x : X, y : Y, x' : X ⊢ₑ ⟨x', y⟩)).app (x : X, y : Y ⊢ₑ ⟨⟨x, y⟩, x⟩) := by
              conv => rhs; exact map_conj
              simp_proj; rfl
          simp only [Category.comp_id, lift_comp_fst_comp_snd, lift_fst_snd] at H
          conv => enter [1, 1]; exact H
          apply All.adj.mpr

          apply le_trans
          · exact Any.unit (f := fp.fst _ _)
          apply le_trans
          · exact All.unit (f := lift (𝟙 _) (fp.fst X Y))
          · simp_proj
            rfl
    comp_id := by
      rintro ⟨X, ρX⟩ ⟨Y, ρY⟩ f
      apply PERHom_ext
      unfold PERHom.hom
      unfold CategoryStruct.id CategoryStruct.comp
      unfold PERHomComp PERHom.hom
      simp
      apply le_antisymm
      · have H := impl_eq_top_iff.mp f.congrCod; simp at H
        replace H := map_monotone (T := T) (f := x : X, y : Y, y' : Y ⊢ₑ ⟨⟨x, y'⟩, y⟩) H
        simp only [lift_comp_fst_comp_snd, map_conj, ←map_comp_app, lift_fst, lift_snd, comp_lift, ←Category.assoc, Category.comp_id] at H

        apply le_trans
        · apply Any.monotone
          exact H
        apply le_trans
        · exact Any.counit
        · full_eval
          rfl
      · apply le_trans
        · have H := impl_eq_top_iff.mp f.map_le_extent_cod
          simp at H
          exact le_conj (le_refl _) H
        · simp_proj
          have H : ((.ι f.hom) ⊓ (Formula.ι ρY.rel).app ((fp.snd X Y) ≫ diag)) =
            ((Formula.ι f.hom).app (x : X, y : Y, y' : Y ⊢ₑ ⟨x, y'⟩) ⊓ (Formula.ι ρY.rel).app (x : X, y : Y, y' : Y ⊢ₑ ⟨y', y⟩)).app (x : X, y : Y ⊢ₑ ⟨⟨x, y⟩, y⟩) := by
              conv => rhs; exact map_conj
              simp_proj; rfl
          simp only [Category.comp_id, lift_comp_fst_comp_snd, lift_fst_snd] at H
          conv => enter [1, 1]; exact H
          apply All.adj.mpr

          apply le_trans
          · exact Any.unit (f := fp.fst _ _)
          apply le_trans
          · exact All.unit (f := lift (𝟙 _) (fp.snd X Y))
          · simp_proj
            rfl
    assoc := by
      rintro ⟨X, ρX⟩ ⟨Y, ρY⟩ ⟨Z, ρZ⟩ ⟨W, ρW⟩ f g h
      apply PERHom_ext
      unfold PERHom.hom CategoryStruct.comp PERHomComp PERHom.hom
      simp [iota_eval]
      have isPB : IsPullback
        (x : X, w : W, z : Z, y : Y ⊢ₑ ⟨⟨x, w⟩, z⟩) (x : X, w : W, z : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, y⟩)
        (x : X, w : W, z : Z ⊢ₑ ⟨x, z⟩) (x : X, z : Z, y : Y ⊢ₑ ⟨x, z⟩) := by sorry
      have isPB' : IsPullback
        (x : X, w : W, z : Z, y : Y ⊢ₑ ⟨⟨x, w⟩, y⟩) (x : X, w : W, z : Z, y : Y ⊢ₑ ⟨⟨y, w⟩, z⟩)
        (x : X, w : W, y : Y ⊢ₑ ⟨y, w⟩) (y : Y, w : W, z : Z ⊢ₑ ⟨y, w⟩) := by sorry

      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB
      rw [←Any.BeckChevalley isPB]
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB'
      rw [←Any.BeckChevalley isPB']

      rw [←Any.frob_right, ←Any.frob_left, Any.comp_app, Any.comp_app]
      simp_proj
      simp [conj_assoc]

end Defn
