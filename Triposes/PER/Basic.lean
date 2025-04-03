import Triposes.Language.Basic
import Triposes.Language.Properties

import Mathlib.CategoryTheory.Generator

open Language
open CategoryTheory
open MonoidalCategory
open ChosenFiniteProducts

universe u v
variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

/- Fix a tripos -/
variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

section PERdef
  /-- Internal equality -/
  syntax:90 fpterm "=[" term "]" fpterm:70 : fpformula
  local macro_rules
  | `($Γ:fpcontext ⊢ₕ $x:fpterm =[ $ρ:term ] $y:fpterm) => `($Γ:fpcontext ⊢ₕ ⟪.ι $ρ | ⟨$x, $y⟩⟫) --  =[]

  /-- The class of partial equivalence relations on object `X` -/
  class PER (X : 𝒞) where
    /-- The relation -/
    rel   : P₀ (P := P) (X ⊗ X)

    /-- Symmetry -/
    sym   : a : X, b : X        ⊢ a =[rel] b ⇒ b =[rel] a

    /-- Transitivity -/
    trans : a : X, b : X, c : X ⊢ a =[rel] b ⊓ b =[rel] c ⇒ a =[rel] c

end PERdef

namespace Language
  /-- Internal equality -/
  syntax:90 fpterm "=" fpterm:70 : fpformula
  macro_rules
  | `($Γ:fpcontext ⊢ₕ $x:fpterm = $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪.ι (T := T) (PER.rel (X := _)) | ⟨$x, $y⟩ ⟫)
  | `($Γ:fpcontext ⊢ₕ $x:fpterm =[ $ρ:term ] $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪.ι (T := T) (PER.rel (X := $ρ)) | ⟨$x, $y⟩ ⟫)
end Language

section PERHomDef
  /-- Internal function applucation -/
  syntax:1025 term:1024 "⸨" fpterm "⸩ =" fpterm : fpformula
  local macro_rules
  | `($Γ:fpcontext ⊢ₕ $map:term ⸨ $x:fpterm ⸩ = $y:fpterm) => `($Γ:fpcontext ⊢ₕ ⟪.ι $map | ⟨$x, $y⟩⟫)

  /-- The class of morphisms between PERs -/
  class PERHom {X Y : 𝒞} (ρX : PER (P := P) X) (ρY : PER (P := P) Y) where
    /-- The function -/
    hom : P₀ (P := P) (X ⊗ Y)

    /-- Congruence with domain equality -/
    congrDom : x : X, x' : X, y : Y ⊢ x = x' ⊓ hom⸨x'⸩ = y ⇒ hom⸨x⸩ = y

    /-- Congruence with codomain equality -/
    congrCod : x : X, y : Y, y' : Y ⊢ hom⸨x⸩ = y ⊓ y = y' ⇒ hom⸨x⸩ = y'

    /-- Uniqueness -/
    unique   : x : X, y : Y, y' : Y ⊢ hom⸨x⸩ = y ⊓ hom⸨x⸩ = y' ⇒ y = y'

    /-- Totallity -/
    total    : x : X                ⊢ x = x ⇔ ∃ y : Y , hom⸨x⸩ = y

end PERHomDef

namespace Language
  macro_rules
  | `($Γ:fpcontext ⊢ₕ $hom:term ⸨ $x:fpterm ⸩ = $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪.ι (T := T) (PERHom.hom (self := $hom)) | ⟨$x, $y⟩⟫)
end Language

namespace PERHom
  variable {X Y Z : 𝒞} {ρX : PER (P := P) X} {ρY : PER (P := P) Y} {ρZ : PER (P := P) Z}

  /- Helper functions and defined terms -/
  @[reducible]
  def congrDomTerm  (f : PERHom ρX ρY) := x : X, x' : X, y : Y ⊢ₕ x = x' ⊓ f⸨x'⸩ = y ⇒ f⸨x⸩ = y
  @[reducible]
  def congrCodTerm  (f : PERHom ρX ρY) := x : X, y : Y, y' : Y ⊢ₕ f⸨x⸩ = y ⊓ y = y' ⇒ f⸨x⸩ = y'
  @[reducible]
  def uniqueTerm    (f : PERHom ρX ρY) := x : X, y : Y, y' : Y ⊢ₕ f⸨x⸩ = y ⊓ f⸨x⸩ = y' ⇒ y = y'
  @[reducible]
  def totalTerm     (f : PERHom ρX ρY) := x : X ⊢ₕ x = x ⇔ ∃ y : Y , f⸨x⸩ = y
  @[reducible]
  def totalTerm_mp  (f : PERHom ρX ρY) := x : X ⊢ₕ x = x ⇒ ∃ y : Y , f⸨x⸩ = y
  @[reducible]
  def totalTerm_mpr (f : PERHom ρX ρY) := x : X ⊢ₕ ∃ y : Y , f⸨x⸩ = y ⇒ x = x

  @[reducible]
  def total_mp      (f : PERHom ρX ρY) : x : X ⊢ x = x ⇒ ∃ y : Y , f⸨x⸩ = y := by
    have ⟨total_mp, _⟩ := conj_eq_top_iff.mp f.total
    exact total_mp
  @[reducible]
  def total_mpr     (f : PERHom ρX ρY) : x : X ⊢ (∃ y : Y , f⸨x⸩ = y) ⇒ x = x := by
    have ⟨_, total_mpr⟩ := conj_eq_top_iff.mp f.total
    exact total_mpr
end PERHom

section PERLemata

  variable {X Y Z : 𝒞} {ρX : PER (P := P) X} {ρY : PER (P := P) Y} {ρZ : PER (P := P) Z}

  omit ccc in
  /-- x = x ⇒ ∃ x' : X, x = x' -/
  -- theorem PER.extent_le_exists_rel : (((Formula.ι ρX.rel).app diag).impl (Formula.any (fp.fst _ _) (Formula.ι ρX.rel))) = ⊤ := by
  theorem PER.extent_le_exists_rel : x : X ⊢ x = x ⇒ ∃ x' : X, x = x' := by
    apply impl_eq_top_iff.mpr
    apply All.adj.mpr
    apply le_trans
    · exact Any.unit (f := fp.fst X X)
    apply le_trans
    · exact All.unit (f := diag)
    · simp_proj

  omit ccc
  /-- PERHoms are equal when their underlying funcitions are -/
  @[ext]
  theorem PERHom_ext (f g : PERHom (T := T) ρX ρY) : f.hom = g.hom → f = g := by
    induction f
    induction g
    rintro H
    unfold PERHom.hom at H; simp at H
    simp [H]

  omit ccc in
  /-- The proposition `f(x) = y ≤ x = x` -/
  theorem PERHom.map_le_extent_dom (f : PERHom (T := T) ρX ρY)
    : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ x = x := by
    apply (All.eq_top_iff_forall_eq_top (x : X, y : Y ⊢ₑ x)).mpr
    simp_proj
    rw [map_comp_app (P := P)]
    conv => lhs; exact frobenius
    have cow := f.total_mpr
    simp at cow
    exact cow

  omit ccc in
  /-- The proposition `f(x) = y ≤ y = y` -/
  theorem PERHom.map_le_extent_cod (f: PERHom (T := T) ρX ρY)
    : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ y = y := by
    apply weakening (x : X, y : Y ⊢ₑ ⟨⟨x, y⟩, y⟩) f.uniqueTerm
    unfold uniqueTerm
    simp_proj
    rw [conj_idem]
    apply f.unique

  /-- Composition of `PERHom`s -/
  def PERHomComp (g : PERHom ρY ρZ) (f : PERHom ρX ρY) : PERHom ρX ρZ where
    hom := (x : X, z : Z ⊢ₕ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z)).eval
    congrDom := by
      simp [iota_eval]
      simp_proj
      have isPB : IsPullback
        (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, z⟩) (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x', z⟩, y⟩)
        (x : X, x' : X, z : Z ⊢ₑ ⟨x', z⟩) (x' : X, z : Z, y : Y ⊢ₑ ⟨x', z⟩) := by sorry
      have isPB' : IsPullback
        (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, z⟩) (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, y⟩)
        (x : X, x' : X, z : Z ⊢ₑ ⟨x, z⟩) (x : X, z : Z, y : Y ⊢ₑ ⟨x, z⟩) := by sorry

      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB
      rw [←Any.BeckChevalley isPB]
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB'
      rw [←Any.BeckChevalley isPB']
      simp_proj
      rw [←Any.frob_right, ←conj_assoc]
      simp_proj
      have cow := f.congrDom
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at cow
      replace cow := impl_eq_top_iff.mp cow
      conv =>
        enter [1, 1, 2, 1]
        conv =>
          lhs
          tactic =>
            have : (fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _) = (lift (fp.fst ((X ⊗ X) ⊗ Z) Y ≫ fp.fst _ _) (fp.snd _ _)) ≫ (fp.fst _ _) := by aesop_cat
            rw [this, map_comp_app]
        conv =>
          rhs
          tactic =>
            have : lift (((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _)) ≫ (fp.snd _ _)) (fp.snd _ _) = (lift (fp.fst ((X ⊗ X) ⊗ Z) Y ≫ fp.fst _ _) (fp.snd _ _)) ≫ lift (fp.fst _ _ ≫ fp.snd _ _) (fp.snd _ _) := by aesop_cat
            rw [this, map_comp_app]
        rw [←map_conj]
      apply impl_eq_top_iff.mpr
      apply le_trans
      · apply Any.monotone
        apply conj_le_conj_right
        apply map_monotone
        exact cow
      · simp_proj

    congrCod := by
      simp [iota_eval]
      simp_proj

      have isPB : IsPullback
        (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, z'⟩) (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, y⟩)
        (x : X, z : Z, z' : Z ⊢ₑ ⟨x, z⟩) (x : X, z : Z, y : Y ⊢ₑ ⟨x, z⟩) := by sorry
      have isPB' : IsPullback
        (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, z'⟩) (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨x, z'⟩, y⟩)
        (x : X, z : Z, z' : Z ⊢ₑ ⟨x, z'⟩) (x : X, z' : Z, y : Y ⊢ₑ ⟨x, z'⟩) := by sorry

      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB
      rw [←Any.BeckChevalley isPB]
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB'
      rw [←Any.BeckChevalley isPB']

      have H := impl_eq_top_iff.mp g.congrCod
      apply impl_eq_top_iff.mpr
      simp only [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at H

      rw [←Any.frob_left]
      simp_proj
      conv => enter [1, 2]; exact conj_assoc (P := P) _ _ _
      conv =>
        enter [1, 2, 2, 1]
        tactic =>
          have : lift (fp.snd ((X ⊗ Z) ⊗ Z) Y) ((fp.fst _ _ ≫ fp.fst _ _) ≫ fp.snd _ _) = (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨y, z⟩, z'⟩) ≫ fp.fst (Y ⊗ Z) Z := by aesop_cat
          rw [this, map_comp_app]
      conv =>
        enter [1, 2, 2, 2]
        tactic =>
          have : lift ((fp.fst ((X ⊗ Z) ⊗ Z) Y ≫ fp.fst _ _) ≫ fp.snd _ _) (fp.fst _ _ ≫ fp.snd _ _) = (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨y, z⟩, z'⟩) ≫ lift (fp.fst (Y ⊗ Z) Z ≫ fp.snd _ _) (fp.snd _ _) := by aesop_cat
          rw [this, map_comp_app]
      rw [←map_conj]
      apply le_trans
      · apply Any.monotone
        apply conj_le_conj_left
        apply map_monotone
        exact H
      · simp_proj

    unique := by
      simp [iota_eval]
      simp_proj
      apply impl_eq_top_iff.mpr

      have isPB : IsPullback
        (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, z'⟩) (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, y⟩)
        (x : X, z : Z, z' : Z ⊢ₑ ⟨x, z⟩) (x : X, z : Z, y : Y ⊢ₑ ⟨x, z⟩) := by sorry

      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB
      rw [←Any.BeckChevalley isPB, ←Any.frob_left]
      simp_proj

      have isPB' : IsPullback
        (x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨⟨x, z⟩, z'⟩, y⟩) (x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨x, z'⟩, y'⟩)
        (x : X, z : Z, z' : Z, y : Y ⊢ₑ ⟨x, z'⟩) (x : X, z' : Z, y' : Y ⊢ₑ ⟨x, z'⟩) := by sorry

      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at isPB'
      rw [←Any.BeckChevalley isPB', ←Any.frob_right]
      simp_proj

      have guniq := impl_eq_top_iff.mp g.unique
      have funiq := impl_eq_top_iff.mp f.unique
      have gcongrdom := impl_eq_top_iff.mp g.congrDom
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at guniq
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at funiq
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at gcongrdom

      conv => enter [1, 2, 2, 1]; rw [conj_comm]
      simp [conj_assoc]
      conv => enter [1, 2, 2, 2]; rw [←conj_assoc]
      simp_proj
      conv =>
        enter [1, 2, 2]
        conv =>
          enter [2, 1, 1]
          tactic =>
            have : lift (((fp.fst (((X ⊗ Z) ⊗ Z) ⊗ Y) Y ≫ fp.fst _ _) ≫ fp.fst _ _) ≫ fp.fst _ _) (fp.fst _ _ ≫ fp.snd _ _) = (x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨x, y⟩, y'⟩) ≫ fp.fst (X ⊗ Y) Y := by aesop_cat
            rw [this, map_comp_app]
        conv =>
          enter [2, 1, 2]
          tactic =>
            have : lift (((fp.fst (((X ⊗ Z) ⊗ Z) ⊗ Y) Y ≫ fp.fst _ _) ≫ fp.fst _ _) ≫ fp.fst _ _) (fp.snd _ _) = (x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨x, y⟩, y'⟩) ≫ (lift (fp.fst _ _ ≫ fp.fst _ _) (fp.snd _ _)) := by aesop_cat
            rw [this, map_comp_app]
        rw [←map_conj]
      apply le_trans
      · repeat apply Any.monotone
        apply conj_le_conj_left
        apply conj_le_conj_right
        apply map_monotone
        exact funiq
      simp_proj
      conv =>
        enter [1, 2, 2, 2]
        conv =>
          lhs
          tactic =>
            have : lift ((fp.fst (((X ⊗ Z) ⊗ Z) ⊗ Y) Y) ≫ fp.snd _ _) (fp.snd _ _) = x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨y, y'⟩, z'⟩ ≫ fp.fst _ _ := by aesop_cat
            rw [this, map_comp_app]
        conv =>
          rhs
          tactic =>
            have : lift (fp.snd (((X ⊗ Z) ⊗ Z) ⊗ Y) Y) ((fp.fst _ _ ≫ fp.fst _ _) ≫ fp.snd _ _) = x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨y, y'⟩, z'⟩ ≫ (lift (fp.fst _ _ ≫ fp.snd _ _) (fp.snd _ _)):= by aesop_cat
            rw [this, map_comp_app]
        exact (Eq.comm.mp map_conj)
      apply le_trans
      · repeat apply Any.monotone
        apply conj_le_conj_left
        apply map_monotone
        exact gcongrdom
      simp_proj
      conv =>
        enter [1, 2, 2]
        conv =>
          lhs
          tactic =>
            have : lift ((fp.fst (((X ⊗ Z) ⊗ Z) ⊗ Y) Y) ≫ fp.snd _ _) (((fp.fst _ _ ≫ fp.fst _ _) ≫ fp.fst _ _) ≫ fp.snd _ _) = x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨y, z⟩, z'⟩ ≫ fp.fst _ _ := by aesop_cat
            rw [this, map_comp_app]
        conv =>
          rhs
          tactic =>
            have : lift ((fp.fst (((X ⊗ Z) ⊗ Z) ⊗ Y) Y) ≫ fp.snd _ _) ((fp.fst _ _ ≫ fp.fst _ _) ≫ fp.snd _ _) = x : X, z : Z, z' : Z, y : Y, y' : Y ⊢ₑ ⟨⟨y, z⟩, z'⟩ ≫ (lift (fp.fst _ _ ≫ fp.fst _ _) (fp.snd _ _)) := by aesop_cat
            rw [this, map_comp_app]
        rw [←map_conj]
      apply le_trans
      · repeat apply Any.monotone
        apply map_monotone
        exact guniq
      · repeat apply Any.adj.mp
        simp_proj

    total := by
      simp [iota_eval]
      simp_proj
      apply biimpl_eq_top_iff.mpr

      have ftot := le_antisymm (impl_eq_top_iff.mp f.total_mp) (impl_eq_top_iff.mp f.total_mpr)
      have gtot := le_antisymm (impl_eq_top_iff.mp g.total_mp) (impl_eq_top_iff.mp g.total_mpr)
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at ftot
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at gtot

      rw [Any.comm_app]
      simp_proj
      rw [Any.frob_right]

      have isPB : IsPullback
        (fp.fst (X ⊗ Y) Z) (lift (fp.fst _ _ ≫ fp.snd _ _) (fp.snd _ _))
        (fp.snd _ _) (fp.fst _ _) := by sorry
      rw [Any.BeckChevalley isPB, ←gtot]
      simp_proj

      have H := impl_eq_top_iff.mp f.map_le_extent_cod
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd, ←Category.assoc, Category.id_comp, Category.comp_id, ←map_comp_app, map_conj, map_disj, map_impl] at H
      conv =>
        enter [2, 2]
        exact inf_eq_left.mpr H
      exact ftot
