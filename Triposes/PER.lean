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
  -- omit ccc in lemma isTop_iff_forall_isTop {t : P₀ (P := P) (X ⊗ Y)} : (y : Y, x : X ⊢ ⟪t | ⟨x, y⟩⟫) ↔ (x : X ⊢ ∀ y : Y, ⟪t | ⟨x, y⟩⟫) := by
    constructor
    · simp
      rintro rfl
      apply map_top
    · apply isTop_le_isTop
      exact forall_le (𝔸 := T.𝔸 f)
      -- rintro 𝔸ttop
      -- rw [eq_top_iff] at 𝔸ttop
      -- apply RightAdjoint.adjFrom at 𝔸ttop
      -- simp at 𝔸ttop
      -- assumption

  omit ccc in theorem PERHom.map_le_extent_dom (f: PERHom (T := T) ρX ρY)
    : isTop (x : X, y : Y ⊢ₕ f⸨x⸩ = y ⇒ x = x) := by
      apply (isTop_iff_forall_isTop (x : X, y : Y ⊢ₑ x)).mpr
      conv =>
        enter [1, 2]
        rhs
        tactic =>
          have H : «fst» X Y = «fst» X Y ≫ 𝟙 _ := by aesop_cat
          rw [H, ←comp_lift]
      rw [←P₁.map_comp, T.exists_universal_property']
      have cow := f.total_mpr
      simp
      simp at cow
      refine le_trans ?a cow
      conv =>
        rhs
        tactic =>
          have isPB : IsPullback («snd» Y X) (lift («snd» Y X) («fst» Y X)) (𝟙 X) («fst» X Y) := by
            apply IsPullback.of_iso
            case h =>
              constructor
              · constructor
                exact Limits.pullbackConeOfLeftIsoIsLimit (𝟙 X) («fst» X Y)
              · aesop_cat
            case e₁ => exact {
              hom := lift («snd» X Y) («fst» X Y)
              inv := lift («snd» Y X) («fst» Y X)
            }
            case e₂ => exact Iso.refl _
            case e₃ => exact Iso.refl _
            case e₄ => exact Iso.refl _
            repeat aesop_cat
          have BC := T.BeckChevalley𝔼 _ _ _ _ isPB
          apply funext_iff.mp at BC
          simp at BC
          have BC := BC (hom ρX ρY)
          rw [BC]
      aesop_cat
      -- conv at cow =>
      --   lhs
      --   tactic =>
      --     have isPB : IsPullback («snd» Y X) (lift («snd» Y X) («fst» Y X)) (𝟙 X) («fst» X Y) := by sorry
      --     have BC := T.BeckChevalley𝔼 _ _ _ _ isPB
      --     apply funext_iff.mp at BC
      --     simp at BC
      --     have BC := BC (hom ρX ρY)
      --     rw [BC]
      -- unfold P₁
      -- unfold P₁ at cow

    -- apply isTop_le_isTop (s := x : X ⊢ₕ (∃ y : Y , f⸨x⸩ = y) ⇒ x = x)
    -- · exact f.total_mpr
    -- · exact {
    --     map := x : X, y : Y ⊢ₑ x
    --     le := by
    --       rw [P₁.map_himp]
    --       apply himp_le_himp
    --       · simp
    --         conv =>
    --           rhs
    --           enter [2]
    --           tactic =>
    --             have isPB : IsPullback («snd» Y X) (lift («snd» Y X) («fst» Y X)) (𝟙 X) («fst» X Y) := by sorry
    --             have cow := T.BeckChevalley𝔼 _ _ _ _ isPB
    --             apply funext_iff.mp at cow
    --             simp at cow
    --             have cow := cow (hom ρX ρY)
    --             rw [cow]
    --         conv =>
    --           rhs
    --           enter [2]
    --           exact P₁.map_id
    --             -- simp
    --             -- have H : 𝟙 (P.obj (.op X)) = HeytingHom.id _ := by aesop_cat
    --             -- rw [H]
    --         conv =>
    --           rhs
    --           tactic =>
    --             have isPB : IsPullback (𝟙 (X ⊗ Y)) (𝟙 (X ⊗ Y)) («fst» X Y) («fst» X Y)  := by sorry
    --             have cow := T.BeckChevalley𝔼 _ _ _ _ isPB
    --             apply funext_iff.mp at cow
    --             simp at cow
    --             have cow := cow (hom ρX ρY)
    --             rw [←cow]

    --       · rw [P₁.map_comp]
    --         simp


          -- simp only [Function.comp_apply, map_himp]
          -- unfold P₁
          -- simp only [Function.comp_apply]
          -- rw [map_comp', ←op_comp, comp_lift]
          -- repeat rw [Category.comp_id]
          -- apply himp_le_himp_right
          -- have H' : P.map (lift («fst» X Y) («snd» X Y)).op = P₁ (lift («fst» X Y) («snd» X Y)) := by
          --   unfold P₁
          --   simp
          -- rw [H']
          -- have H' : P.map (lift («snd» Y X) («fst» Y X)).op = P₁ twist := by
          --   unfold twist P₁
          --   simp
          -- rw [H']
          -- have H' : P.map («fst» X Y).op = P₁ (fp.fst X Y) := by rfl
          -- rw [H']
          -- have H' (𝔼 : LeftAdjoint (fp.snd Y X)) : LeftAdjoint.map (self := 𝔼) («snd» Y X) ((P₁ twist) (hom ρX ρY)) = ((LeftAdjoint.map (self := 𝔼) («snd» Y X)) ∘ (P₁ twist)) (hom ρX ρY) := by
          --   apply Function.comp_apply

          -- -- rw [H' (T.𝔼 (fp.snd Y X))]
          -- rw [←Function.comp_apply (f := T.𝔼 (fp.snd _ _)) (g := P₁ twist) (x := hom ρX ρY)]
          -- -- rw [T.BeckChevalley𝔼 (fp.snd Y X) twist _ _]

          -- let x := (P₁ (lift (fp.fst X Y) (fp.snd X Y))) (hom ρX ρY)
          -- have H := (T.𝔼 (fp.snd X Y)).unit (x := x)
          -- trans
          -- · exact H
          -- · unfold x
          --   simp
          --   apply T.BeckChevalley𝔸 (fp.snd _ _) twist _ _

          -- trans (P₁ (fp.fst Y X)) ((T.𝔼 (fp.fst Y X)) (P.map (lift («snd» Y X) («fst» Y X)).op) (hom ρX ρY)))
          -- · exact (T.𝔼 (fp.fst Y X)).unit
          -- · sorry
          -- apply (T.𝔸 _).adjFrom
          -- have H : fp.fst X Y = fp.fst X Y ≫ 𝟙 _ := by aesop
          -- rw [H, ←comp_lift, ←exists_universal_property (𝔼 := T.𝔼 _) (𝔸 := T.𝔸 _)]

      -- }
    -- apply isTop_le_isTop (s := y : Y, x : X ⊢ₕ f⸨x⸩ = y ⇒ x = x)
    -- · apply (isTop_iff_forall_isTop (f := fp.snd Y X)).mpr
    --   rw [←comp_lift]
    --   have H : P₁ (P := P) ((fp.snd Y X) ≫ fp.lift (𝟙 X) (𝟙 X)) PER.rel = P₁ (fp.snd Y X) (P₁ (fp.lift (𝟙 X) (𝟙 X)) PER.rel) := by
    --     unfold P₁
    --     simp only [Function.comp_apply]
    --     rw [op_comp, P.map_comp]
    --     aesop_cat
    --   rw [H]
    --   simp
    --   trans
    --   · exact T.exists_universal_property'
    --   · have cow := f.total_mpr
    --     simp
    --     simp at cow
    --     apply cow
    -- · exact {
    --   map := x : X, y : Y ⊢ₑ ⟨ y, x ⟩
    --   le := by
    --     simp
    --     unfold P₁
    --     simp
    --     have cow := map_comp' (P := P) (z := _)
    --     -- rw [←P.map_comp' (P := P)]

    -- }
    -- apply (isTop_iff_forall_isTop (f := fp.snd Y X)).mpr
    -- simp
    -- conv =>
    --   lhs
    --   enter [2, 2]
    --   tactic =>
    --     symm
    --     trans
    --     · apply P₁.map_comp
    --       · exact fp.snd _ _
    --       · exact lift (𝟙 X) (𝟙 X)
    --       · exact ρX.rel
    --     · simp
    -- simp
    -- trans
    -- · exact T.exists_universal_property'
    -- · have cow := f.total_mpr
    --   simp
    --   simp at cow
    --   apply cow

  -- theorem PERHom.map_le_extent_cod (f: PERHom (T := T) ρX ρY)
  --   : x : X, y : Y ⊢ f⸨x⸩ = y ⇒ y = y := by
  --   -- let subst := (P₁ (P := P) (x : X, y : Y ⊢ₑ ⟨x, ⟨y, y⟩⟩))
  --   let subst := (P₁ (P := P) (x : X, y : Y ⊢ₑ ⟨⟨x, y⟩, y⟩))
  --   let funiq := x : X, y : Y, y' : Y ⊢ₕ f⸨x⸩ = y ⊓ f⸨x⸩ = y' ⇒ y = y'
  --   calc
  --     x : X, y : Y ⊢ₕ f⸨x⸩ = y ⇒ y = y
  --     _ = subst funiq := by sorry
  --     _ ≥ subst ⊤            := by gcongr; exact f.unique
  --     _ ≥ ⊤                  := by rw [map_top]

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
