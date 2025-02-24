import Triposes.Language

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
    sym   : a : X, b : X        ⊢ ⟪rel | ⟨a, b⟩⟫ ⇒ ⟪rel | ⟨b, a⟩⟫
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
    let total := f.total
    simp at total
    simp
    rw [total]
  @[reducible]
  def total_mpr     (f : PERHom ρX ρY) : x : X ⊢ (∃ y : Y , f⸨x⸩ = y) ⇒ x = x := by
    let total := f.total
    simp at total
    simp
    rw [total]
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
      apply T.forall_top_eq_top'
    · apply isTop_le_isTop
      exact forall_le (𝔸 := T.𝔸 f)

  open Lean PrettyPrinter Delaborator SubExpr

  @[app_unexpander ChosenFiniteProducts.fst]
  def unexpFpFst : Unexpander
    | `($_fst $X $Y) => `([$X]⊗$Y)
    | `($_fst) => pure $ mkIdent `fst
  @[app_unexpander ChosenFiniteProducts.snd]
  def unexpFpSnd : Unexpander
    | `($_snd $X $Y) => `($X⊗[$Y])
    | `($_snd) => pure $ mkIdent `snd
  @[app_unexpander P₁]
  def unexpP₁ : Unexpander
    | `($_ $f) => `($f *)
    | `($_) => `(P₁)

  omit ccc in theorem lift_diag {f : X ⟶ Y} : lift f f = f ≫ diag := by unfold diag; aesop_cat
  omit ccc in theorem lift_snd_fst : lift (fp.snd X Y) (fp.fst X Y) = twist := by unfold twist; aesop_cat
  omit ccc in theorem comp_lift_left {f : X ⟶ Y} {g : Y ⟶ Z} : lift (f ≫ g) f = f ≫ lift g (𝟙 _) := by aesop_cat
  omit ccc in theorem comp_lift_right {f : X ⟶ Y} {g : Y ⟶ Z} : lift f (f ≫ g) = f ≫ lift (𝟙 _) g := by aesop_cat
  omit ccc in theorem lift_comp_fst_comp_snd {f : X ⟶ Y ⊗ Z} : lift (f ≫ fp.fst _ _) (f ≫ fp.snd _ _) = f := by aesop_cat

  omit ccc in theorem PERHom.map_le_extent_dom (f: PERHom (T := T) ρX ρY)
    : isTop (x : X, y : Y ⊢ₕ f⸨x⸩ = y ⇒ x = x) := by
    apply (isTop_iff_forall_isTop (x : X, y : Y ⊢ₑ x)).mpr
    conv =>
      enter [1, 2]
      rhs
      tactic =>
        have H : «fst» X Y = «fst» X Y ≫ 𝟙 _ := by aesop_cat
        rw [H, ←comp_lift]
    rw [P₁.map_comp_app, T.exists_universal_property']
    have cow := f.total_mpr
    simp
    rw [Category.comp_id]
    simp at cow
    exact cow
      -- apply isTop_le_isTop
      -- case s => exact y : Y, x : X ⊢ₕ f⸨x⸩ = y ⇒ x = x
      -- case H =>
      --   apply (isTop_iff_forall_isTop (y : Y, x : X ⊢ₑ x)).mpr
      --   conv =>
      --     enter [1, 2]
      --     rhs
      --     tactic =>
      --       have H : «snd» Y X = «snd» Y X ≫ 𝟙 _ := by aesop_cat
      --       rw [H, ←comp_lift]
      --   rw [P₁.map_comp_app, T.exists_universal_property']
      --   have cow := f.total_mpr
      --   simp
      --   rw [Category.comp_id]
      --   simp at cow
      --   exact cow
      -- case φ => exact {
      --     map := x : X, y : Y ⊢ₑ ⟨y, x⟩
      --     le := by
      --       rw [Category.comp_id, lift_fst_snd, lift_snd_fst]
      --       rw [Category.comp_id, lift_snd_fst, lift_diag, lift_diag]
      --       rw [P₁.map_comp_app, P₁.map_himp]
      --       conv =>
      --         lhs
      --         enter [1]
      --         rw [←P₁.map_comp_app, twist_twist_eq_id, P₁.map_id]
      --       conv =>
      --         lhs
      --         enter [2]
      --         rw [←P₁.map_comp_app, twist_snd_eq_fst]
      --       rw [P₁.map_id, P₁.map_comp_app]
      -- }

  syntax "proj_calc" : tactic
  macro_rules
    | `(tactic| proj_calc) =>
      `(tactic| simp only [comp_lift, lift_fst, lift_snd, ←Category.assoc, Category.id_comp, lift_diag, lift_fst_snd, lift_comp_fst_comp_snd, ←P₁.map_comp_app])

  omit ccc in theorem PERHom.map_le_extent_cod (f: PERHom (T := T) ρX ρY)
    : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ y = y := by
    apply isTop_le_isTop f.unique
    exact {
      map := x : X, y : Y ⊢ₑ ⟨⟨x, y⟩, y⟩
      le := by
        -- simp only [Function.comp_apply, Category.comp_id, map_himp, map_inf, lift_fst_snd, P₁.map_id]
        -- rw [HeytingHom.id_apply, lift_diag]
        rw [lift_diag]
        simp only [Category.comp_id, lift_fst_snd]
        rw [P₁.map_himp, P₁.map_inf]
        proj_calc
        -- simp only [←P₁.map_comp_app, ←comp_lift, lift_fst_snd, Category.comp_id, lift_fst, lift_snd]
        -- simp only [comp_lift, lift_fst, lift_snd, ←Category.assoc, Category.id_comp, lift_diag, lift_fst_snd]
        simp

        -- conv =>
        --   lhs; enter [2, 1, 1, 1, 1]
        --   rw [←Category.comp_id (f := fp.fst _ _), ←lift_map]
        --   simp
        -- conv =>
        --   lhs; enter [2, 1, 2, 1, 1]
        --   rw [←Category.comp_id (f := fp.fst _ _), ←lift_map]
        --   simp
        -- conv =>
        --   lhs; enter [2, 2, 1, 1]
        --   rw [←comp_lift]
        --   simp
        -- simp only [Category.comp_id, lift_fst_snd]
        -- rw [P₁.map_himp, P₁.map_inf]
        -- conv =>
        --   lhs; enter [1, 1]
        --   rw [←P₁.map_comp_app]
        --   enter [1, 1]
        --   rw [←MonoidalCategory.whiskerLeft_comp, diag_fst_eq_id, ←id_tensorHom]
        --   simp
        -- conv =>
        --   lhs; enter [1, 2]
        --   rw [←P₁.map_comp_app]
        --   enter [1, 1]
        --   rw [←MonoidalCategory.whiskerLeft_comp, diag_snd_eq_id, ←id_tensorHom]
        --   simp
        -- conv =>
        --   lhs; enter [2]
        --   rw [←P₁.map_comp_app]
        --   enter [1, 1]
        --   rw [←id_tensorHom]
        --   simp
        -- simp










        -- simp only [Function.comp_apply, op_tensorObj, Category.comp_id, map_himp, map_inf, lift_fst_snd]



    }
    -- let subst := (P₁ (P := P) (x : X, y : Y ⊢ₑ ⟨x, ⟨y, y⟩⟩))
    -- let funiq := x : X, y : Y, y' : Y ⊢ₕ f⸨x⸩ = y ⊓ f⸨x⸩ = y' ⇒ y = y'
    -- calc
    --   x : X, y : Y ⊢ₕ f⸨x⸩ = y ⇒ y = y
    --   _ = subst funiq        := by
    --     unfold subst
    --     unfold funiq
    --     simp
    --   _ ≥ subst ⊤            := by gcongr; exact f.unique
    --   _ ≥ ⊤                  := by rw [map_top]

  -- omit ccc in theorem PERHomDom (f: PERHom (T := T) ρX ρY)
  --   : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ x = x ⊓ f⸨x⸩ = y := by
  --   simp
  --   have := f.map_le_extent_dom
  --   simp at this
  --   exact this

  -- def PERHomComp {X Y Z : 𝒞} {ρX : PER (P := P) X} {ρY : PER (P := P) Y} {ρZ : PER (P := P) Z}
  --   : (PERHom ρY ρZ) → (PERHom ρX ρY) → (PERHom ρX ρZ) :=
  --   fun g f => {
  --     hom := x : X, z : Z ⊢ₕ ∃ y : Y, f⸨x⸩ = y ⊓ g⸨y⸩ = z
  --     congrDom := by
  --       apply Preorder.le_trans
  --       · sorry
  --       · sorry
  --     congrCod := sorry
  --     unique   := sorry
  --     total    := sorry
  --   }
