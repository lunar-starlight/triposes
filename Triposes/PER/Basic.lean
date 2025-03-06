import Triposes.Language.Basic
import Triposes.Language.Properties

open Language
open CategoryTheory
open MonoidalCategory

universe u v
variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

/- Fix a tripos -/
variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

section PERdef
  syntax:90 fpterm "=[" term "]" fpterm:70 : fpformula
  local macro_rules
  | `($Γ:fpcontext ⊢ₕ $x:fpterm =[ $ρ:term ] $y:fpterm) => `($Γ:fpcontext ⊢ₕ ⟪ $ρ | ⟨$x, $y⟩ ⟫) --  =[]

  class PER (X : 𝒞) where
    rel   : P₀ (P := P) (X ⊗ X)
    sym   : a : X, b : X        ⊢ a =[rel] b ⇒ b =[rel] a
    -- sym   : a : X, b : X        ⊢ ⟪rel | ⟨a, b⟩⟫ ⇒ ⟪rel | ⟨b, a⟩⟫
    trans : a : X, b : X, c : X ⊢ a =[rel] b ⊓ b =[rel] c ⇒ a =[rel] c
end PERdef

namespace Language
  syntax:90 fpterm "=" fpterm:70 : fpformula
  macro_rules
  | `($Γ:fpcontext ⊢ₕ $x:fpterm = $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪ PER.rel (X := _) | ⟨$x, $y⟩ ⟫)
  | `($Γ:fpcontext ⊢ₕ $x:fpterm =[ $ρ:term ] $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪ PER.rel (X := $ρ) | ⟨$x, $y⟩ ⟫)
end Language

section PERHomDef
  syntax:1025 term:1024 "⸨" fpterm "⸩ =" fpterm : fpformula
  local macro_rules
  | `($Γ:fpcontext ⊢ₕ $map:term ⸨ $x:fpterm ⸩ = $y:fpterm) => `($Γ:fpcontext ⊢ₕ ⟪$map | ⟨$x, $y⟩⟫)

  class PERHom {X Y : 𝒞} (ρX : PER (P := P) X) (ρY : PER (P := P) Y) where
    hom : P₀ (P := P) (X ⊗ Y)
    congrDom : x : X, x' : X, y : Y ⊢ x = x' ⊓ hom⸨x'⸩ = y ⇒ hom⸨x⸩ = y
    congrCod : x : X, y : Y, y' : Y ⊢ hom⸨x⸩ = y ⊓ y = y' ⇒ hom⸨x⸩ = y'
    unique   : x : X, y : Y, y' : Y ⊢ hom⸨x⸩ = y ⊓ hom⸨x⸩ = y' ⇒ y = y'
    total    : x : X                ⊢ x = x ⇔ ∃ y : Y , hom⸨x⸩ = y

end PERHomDef

namespace Language
  macro_rules
  | `($Γ:fpcontext ⊢ₕ $hom:term ⸨ $x:fpterm ⸩ = $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪ PERHom.hom (self := $hom) | ⟨$x, $y⟩⟫)
end Language

namespace PERHom
  variable {X Y Z : 𝒞} {ρX : PER (P := P) X} {ρY : PER (P := P) Y} {ρZ : PER (P := P) Z}

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
    have ⟨total_mp, _⟩ := le_inf_iff.mp f.total
    exact total_mp
  @[reducible]
  def total_mpr     (f : PERHom ρX ρY) : x : X ⊢ (∃ y : Y , f⸨x⸩ = y) ⇒ x = x := by
    have ⟨_, total_mpr⟩ := le_inf_iff.mp f.total
    exact total_mpr
end PERHom


-- variable {X Y Z : 𝒞} {ρX : PER (P := P) X} {ρY : PER (P := P) Y} {ρZ : PER (P := P) Z} (g : PERHom ρY ρZ) (f : PERHom ρX ρY) (h : PERHom ρX ρZ)
-- #check f.hom

section PERLemata

  variable {X Y Z : 𝒞} {ρX : PER (P := P) X} {ρY : PER (P := P) Y} {ρZ : PER (P := P) Z}
  open ChosenFiniteProducts
  open Tripos.TermLE

  omit fp ccc in lemma isTop_iff_forall_isTop (f : X ⟶ Y) {t : P₀ X} : isTop t ↔ isTop (T.𝔸 f t) := by
    constructor
    · simp
      rintro rfl
      exact T.𝔸_top_eq_top
    · rintro H
      apply isTop_le_isTop H
      exact forall_le (𝔸 := T.𝔸 f)

  omit ccc in theorem lift_diag {f : X ⟶ Y} : lift f f = f ≫ diag := by unfold diag; aesop_cat
  omit ccc in theorem lift_snd_fst : lift (fp.snd X Y) (fp.fst X Y) = twist := by unfold twist; aesop_cat
  omit ccc in theorem comp_lift_left {f : X ⟶ Y} {g : Y ⟶ Z} : lift (f ≫ g) f = f ≫ lift g (𝟙 _) := by aesop_cat
  omit ccc in theorem comp_lift_right {f : X ⟶ Y} {g : Y ⟶ Z} : lift f (f ≫ g) = f ≫ lift (𝟙 _) g := by aesop_cat
  omit ccc in theorem lift_comp_fst_comp_snd {f : X ⟶ Y ⊗ Z} : lift (f ≫ fp.fst _ _) (f ≫ fp.snd _ _) = f := by aesop_cat


  syntax "simp_proj" : tactic
  syntax "simp_proj_only" : tactic
  macro_rules
    | `(tactic| simp_proj_only) =>
      `(tactic| simp only
        [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
        ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp])
    | `(tactic| simp_proj) =>
      `(tactic| simp
        [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
        ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp])


  omit ccc in
  theorem PERHom.map_le_extent_dom (f: PERHom (T := T) ρX ρY)
    : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ x = x := by
    apply (isTop_iff_forall_isTop (x : X, y : Y ⊢ₑ x)).mpr
    simp_proj
    conv =>
      enter [1, 2, 1, 2]
      rw [map_comp_app (P := P)]
    simp [T.𝔸_congr_app]

    conv =>
      enter [1]
      tactic =>
        apply T.𝔸_congr_app
        simp
    rw [T.frobenius]
    have cow := f.total_mpr
    simp at cow
    repeat unfold Formula.eval at cow
    exact cow

  omit ccc in theorem PERHom.map_le_extent_cod (f: PERHom (T := T) ρX ρY)
    : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ y = y := by
    apply isTop_le_isTop f.unique
    exact {
      map := x : X, y : Y ⊢ₑ ⟨⟨x, y⟩, y⟩
      le := by
        rw [lift_diag]
        simp only [Category.comp_id, lift_fst_snd]
        rw [P₁.map_himp, P₁.map_inf]
        simp_proj_only
        simp
    }

  omit ccc in theorem PERHomDom (f: PERHom (T := T) ρX ρY)
    : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ x = x ⊓ f⸨x⸩ = y := by
    simp
    have := f.map_le_extent_dom
    simp at this
    exact this

  def PERHomComp (g : PERHom ρY ρZ) (f : PERHom ρX ρY) : PERHom ρX ρZ where
    hom := (x : X, z : Z ⊢ₕ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z)).eval
    congrDom := by
      simp_proj_only
      have isPB : IsPullback
        (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, z⟩) (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x', z⟩, y⟩)
        (x : X, x' : X, z : Z ⊢ₑ ⟨x', z⟩) (x' : X, z : Z, y : Y ⊢ₑ ⟨x', z⟩) := by sorry
      have isPB' : IsPullback
        (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, z⟩) (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, y⟩)
        (x : X, x' : X, z : Z ⊢ₑ ⟨x, z⟩) (x : X, z : Z, y : Y ⊢ₑ ⟨x, z⟩) := by sorry
      conv =>
        enter [1, 2]
        tactic =>
          have cow := T.BeckChevalley𝔼' isPB'
          apply funext_iff.mp at cow
          simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
                ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp] at cow
          conv at cow =>
            rhs; enter [2, 2, 1]
            tactic =>
              apply T.𝔼_congr
              simp_proj
          conv at cow =>
            enter [2, 1, 1]
            tactic =>
              apply T.𝔼_congr
              simp_proj
          symm; exact cow _
      conv =>
        enter [1, 1, 2]
        tactic =>
          have cow := T.BeckChevalley𝔼' isPB
          apply funext_iff.mp at cow
          simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
                ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp] at cow
          conv at cow =>
            rhs; enter [2, 2, 1]
            tactic =>
              apply T.𝔼_congr
              simp_proj
          conv at cow =>
            enter [2, 1, 1]
            tactic =>
              apply T.𝔼_congr
              simp_proj
          symm; exact cow _

      have H : (x : X, x' : X, z : Z ⊢ₕ x = x' ⊓ ∃ y : Y, (f⸨x'⸩ = y ⊓ g⸨y⸩ = z) ⇒ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z))
             = (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (x = x' ⊓ f⸨x'⸩ = y ⊓ g⸨y⸩ = z) ⇒ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by
                simp
                simp_proj
                conv =>
                  rhs; enter [1, 2, 1, 1]
                  rw [←P₁.map_comp]
                  exact P₁.map_comp_app
                rw [inf_assoc]
                conv =>
                  rhs; enter [1]
                  exact T.𝔼_frob_right
                simp
      simp only [Function.comp_apply, op_tensorObj, Category.assoc, map_inf, ge_iff_le, le_top]
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
            ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp] at H
      conv =>
        enter [2, 1, 2, 2]
        conv => enter [1]; tactic => symm; exact P₁.map_comp_app
        conv => enter [2]; tactic => symm; exact P₁.map_comp_app
        tactic => simp_proj
      conv =>
        enter [2, 2, 2]
        conv => enter [1]; tactic => symm; exact P₁.map_comp_app
        conv => enter [2]; tactic => symm; exact P₁.map_comp_app
        tactic => simp_proj
      rw [H]
      simp
      have weak_f_congrDom : isTop (P₁ (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, y⟩) f.congrDomTerm) := by
        apply P₁.map_isTop
        exact f.congrDom
      simp at weak_f_congrDom


        -- have H := f.congrDom
        -- simp at H

      -- let weak_f_congrDomTerm := P₁ (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, y⟩) f.congrDomTerm
      -- have weak_f_congrDom : isTop weak_f_congrDomTerm := by
      --   exact isTop_le_isTop f.congrDom {
      --     map := x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, y⟩
      --     le := by
      --       unfold weak_f_congrDomTerm
      --   }
        -- unfold isTop
        -- unfold weak_f_congrDomTerm
        -- apply ge_iff_le.mpr; trans
        -- · apply ge_iff_le.mp
        --   exact f.congrDom
        -- ·
      simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
            ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp] at H



      -- -- simp
      -- have H :
      --   -- calc
      --       (x : X, x' : X, z : Z ⊢ₕ x = x' ⊓ ∃ y : Y, (f⸨x'⸩ = y ⊓ g⸨y⸩ = z) ⇒ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z))
      --     = (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (x = x' ⊓ f⸨x'⸩ = y ⊓ g⸨y⸩ = z) ⇒ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by
      --         simp
      --         simp_proj
      --         conv =>
      --           rhs; enter [1, 2, 1, 1]
      --           rw [←P₁.map_comp]
      --           exact P₁.map_comp_app
      --         rw [inf_assoc]
      --         conv =>
      --           rhs; enter [1]
      --           exact T.𝔼_frob_right
      --         simp
      -- simp_proj_only
      -- -- apply le_himp_iff.mpr
      -- rw [H]


        -- _  (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z) ⇒ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by simp_proj

          --     (x : X, x' : X, z : Z ⊢ₕ x = x' ⊓ ∃ y : Y, (f⸨x'⸩ = y ⊓ g⸨y⸩ = z))
          --   ≤ (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (x = x' ⊓ f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by sorry
          -- _ ≤ (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by sorry

      -- have H :=
      --   calc
      --     (x : X, x' : X, z : Z ⊢ₕ x = x' ⊓ ∃ y : Y, (f⸨x⸩ = y ⊓ g⸨y⸩ = z))
      --       ≤ (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (x = x' ⊓ f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by
      --         simp_proj
      --         conv =>
      --           lhs; tactic => symm; exact T.𝔼_frob_right
      --         apply (T.𝔼 _).map.monotone
      --         rw [inf_assoc, ←P₁.map_comp]
      --         simp_proj_only
      --         conv => rhs; enter [1]; exact P₁.map_comp_app
      --         simp
      --     _ ≤ (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (x' = x ⊓ f⸨x⸩ = y ⊓ g⸨y⸩ = z)) := by sorry
      --     _ ≤ (x : X, x' : X, z : Z ⊢ₕ ∃ y : Y, (f⸨x'⸩ = y ⊓ g⸨y⸩ = z)) := by
      --       simp_proj
      --       gcongr
      --       rw [←P₁.map_comp]
      --       conv =>
      --         lhs; enter [1]
      --         tactic =>
      --           have cow : (fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _) = (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) ≫ (fp.fst (X ⊗ X) Y) := by aesop_cat
      --           have foo : P₁ ((lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) ≫ (fp.fst (X ⊗ X) Y)) ρX.rel = P₁ (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) (P₁ (fp.fst (X ⊗ X) Y) ρX.rel) := by rw [P₁.map_comp_app]
      --           trans
      --           · rw [cow]
      --           · exact foo
      --       conv =>
      --         lhs; enter [2]
      --         tactic =>
      --           have cow : lift (((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _)) ≫ (fp.fst _ _)) (fp.snd _ _)
      --             = (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) ≫ ((fp.fst _ _) ⊗ 𝟙 _) := by aesop_cat
      --           have foo : P₁ ((lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) ≫ ((fp.fst _ _) ⊗ 𝟙 _)) f.hom = P₁ (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) (P₁ ((fp.fst _ _) ⊗ 𝟙 _) f.hom) := by
      --             conv => rhs; tactic => symm; exact P₁.map_comp_app
      --           trans
      --           · rw [cow]
      --           · exact foo
      --       conv =>
      --         rhs
      --         tactic =>
      --           have cow : lift (((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _)) ≫ (fp.snd _ _)) (fp.snd _ _)
      --             = (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) ≫ ((fp.snd _ _) ⊗ 𝟙 _) := by aesop_cat
      --           have foo : P₁ ((lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) ≫ ((fp.snd _ _) ⊗ 𝟙 _)) f.hom = P₁ (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst (X ⊗ X) Z)) ((fp.snd ((X ⊗ X) ⊗ Z) Y))) (P₁ ((fp.snd _ _) ⊗ 𝟙 _) f.hom) := by rw [P₁.map_comp_app]
      --           trans
      --           · rw [cow]
      --           · exact foo
      --       rw [←P₁.map_inf]
      --       apply OrderHomClass.GCongr.mono _
      --       simp

      --       have H := f.congrDom
      --       simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
      --             ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp]
      --           at H
      --       simp [Category.assoc] at H


      -- sorry



      -- simp_proj
      -- simp [comp_lift, lift_fst, lift_snd, lift_diag, lift_snd_fst, lift_fst_snd, lift_comp_fst_comp_snd,
      --       ←Category.assoc, Category.id_comp, Category.comp_id, ←P₁.map_comp_app, P₁.map_inf, P₁.map_sup, P₁.map_himp]
      --      at H

      -- have isPB : IsPullback ((x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, z⟩)) (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x', z⟩, y⟩) (lift ((fp.fst (X ⊗ X) Z) ≫ (fp.snd _ _)) (fp.snd _ _)) (fp.fst _ _) := by sorry
      -- have isPB' : IsPullback ((x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, x'⟩, z⟩)) (x : X, x' : X, z : Z, y : Y ⊢ₑ ⟨⟨x, z⟩, y⟩) (lift ((fp.fst (X ⊗ X) Z) ≫ (fp.fst _ _)) (fp.snd _ _)) (fp.fst _ _) := by sorry

      -- conv =>
      --   lhs; enter [2]
      --   tactic => symm; exact T.BeckChevalley𝔼 isPB
      -- conv =>
      --   rhs
      --   tactic => symm; exact T.BeckChevalley𝔼 isPB'
      -- simp_proj


      -- conv =>
      --   rhs; enter [2, 1]
      --   tactic => symm; exact P₁.map_comp_app
      -- conv =>
      --   rhs; enter [2, 2]
      --   tactic => symm; exact P₁.map_comp_app
      -- conv =>
      --   lhs; enter [2, 2, 1]
      --   tactic => symm; exact P₁.map_comp_app
      -- conv =>
      --   lhs; enter [2, 2, 2]
      --   tactic => symm; exact P₁.map_comp_app
      -- conv =>
      --   lhs; enter [2]
      --   tactic =>
      --     have H : (lift (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _) ≫ (fp.fst _ _) ≫ 𝟙 X) ((fp.fst _ _) ≫ (fp.fst _ _) ≫ (fp.snd _ _))) ((fp.fst _ _) ≫ (fp.snd _ _))) = fp.fst _ _ := by simp_proj
      --     exact T.𝔼_congr_app H
      -- conv =>
      --   rhs
      --   tactic =>
      --     have H : lift (lift ((fp.fst ((X ⊗ X) ⊗ Z) Y) ≫ (fp.fst _ _) ≫ (fp.fst _ _) ≫ 𝟙 X) ((fp.fst _ _) ≫ (fp.fst _ _) ≫ (fp.snd _ _))) ((fp.fst _ _) ≫ (fp.snd _ _)) = fp.fst _ _ := by simp_proj
      --     exact T.𝔼_congr_app H
      -- simp_proj_only
      -- simp
      -- simp at H

      -- -- conv at H =>
      -- --   lhs; enter [2, 1]
      -- --   tactic =>

      -- -- conv =>
      -- --   lhs; tactic => symm; exact T.exists_frob_right'
      -- -- apply (T.𝔼 _).map.monotone
      -- -- rw [←inf_assoc]
      -- -- apply inf_le_inf_right
      -- -- simp_proj

      -- -- -- simp at H
      -- -- conv at H =>
      -- --   lhs; tactic => symm; exact T.exists_frob_right'
      -- -- have H := (T.𝔼 _).adjTo H



      -- -- apply inf_le_inf_right at H



    congrCod := sorry
    unique   := sorry
    total    := sorry
