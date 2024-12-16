import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory
open MonoidalCategory

section ProjDSL
  open Lean

  /-- A context entry -/
  declare_syntax_cat typing_judgement
  syntax ident ":" term : typing_judgement

  /-- A context takes the form `x₁ : X₁, …, xₙ : Xₙ` where `xᵢ` are identifiers and `Xᵢ` objects of a category. -/
  declare_syntax_cat fpcontext
  syntax typing_judgement,* : fpcontext

  /-- The syntax of terms -/
  declare_syntax_cat fpterm

  /-- a variable -/
  syntax ident : fpterm

  /-- the unique (generalized) element of the terminal object -/
  syntax "tt" : fpterm

  /-- ordered pair -/
  syntax "⟨" fpterm "," fpterm "⟩" : fpterm

  /-- first projection -/
  syntax "fst" fpterm : fpterm

  /-- second projection -/
  syntax "snd" fpterm : fpterm

  syntax "(" fpterm ")" : fpterm

  /-- morphism application -/
  syntax "$(" term ")" fpterm : fpterm

  /-- morphism -/
  syntax fpcontext "⊢ₑ" fpterm : term

  /-- Convert a context `x₁ : X₁, …, xₙ : Xₙ` to the term `X₁ ⊗ ⋯ ⊗ Xₙ`,
      making sure that the empty context is the terminal object `𝟙_ _` and
      that `x : X` is just `X`, rather than `X ⊗ 𝟙_ 𝒞`.
  -/
  partial def prodify : TSyntax `fpcontext → MacroM Term
  | `(fpcontext| ) => `(𝟙_ _)
  | `(fpcontext| $_:ident : $A:term) => `($A)
  | `(fpcontext| $_:ident : $A:term, $Γ:typing_judgement,*) =>
    do
      let Γ ← `(fpcontext| $Γ:typing_judgement,*)
      let As ← prodify Γ
      `($A ⊗ $As)
  | _ => Macro.throwError "invalid context syntax"

  /-- Given an identifier `x` and a context `Γ`, compute the projection from `Γ` determined by `x`. -/
  partial def project (x : Name) : TSyntax `fpcontext → MacroM Term
  | `(fpcontext| ) => Macro.throwError s!"unkown identifier {x}"
  | `(fpcontext| $y:ident : $A:term) =>
      -- the only thing that can be projected is `x` by the identity morphism
      if x = y.getId then `(𝟙 $A) else Macro.throwError s!"unkown identifier {x}"
  | `(fpcontext| $y:ident : $A:term, $Γ:typing_judgement,*) =>
    if x = y.getId then
      `(ChosenFiniteProducts.fst $A _)
    else do
      let Γ ← `(fpcontext| $Γ:typing_judgement,*)
      let p ← project x Γ
      `(ChosenFiniteProducts.snd $A _ ≫ $p)
  | _ => Macro.throwError "invalid context syntax"

  /-- Conversion of the internal syntax to a (term representing) morphism -/
  macro_rules
  | `($Γ:fpcontext ⊢ₑ $x:ident) => project x.getId Γ
  | `($Γ:fpcontext ⊢ₑ tt) =>
    /- We could skip using `prodify` here and just return `(ChosenFiniteProducts.toUnit _)`, but the
       result is a bit too polymorphic, as `⊢ₑ tt` would denote *any* morphihm `toUnit X`. -/
    do { let A ← prodify Γ ; `(ChosenFiniteProducts.toUnit $A) }
  | `($Γ:fpcontext ⊢ₑ ⟨ $a:fpterm, $b:fpterm ⟩) => `(ChosenFiniteProducts.lift ($Γ:fpcontext ⊢ₑ $a) ($Γ:fpcontext ⊢ₑ $b))
  | `($Γ:fpcontext ⊢ₑ fst $a:fpterm) => `(($Γ:fpcontext ⊢ₑ $a) ≫ ChosenFiniteProducts.fst _ _)
  | `($Γ:fpcontext ⊢ₑ snd $a:fpterm) => `(($Γ:fpcontext ⊢ₑ $a) ≫ ChosenFiniteProducts.snd _ _)
  | `($Γ:fpcontext ⊢ₑ $($f:term) $a:fpterm) => `(($Γ:fpcontext ⊢ₑ $a) ≫ $f)
  | `($Γ:fpcontext ⊢ₑ ($a:fpterm)) => `($Γ:fpcontext ⊢ₑ $a)
end ProjDSL

section Examples

  /- We work over a a category with (chosen) finite products. -/
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞]

  open ChosenFiniteProducts

  /-- the identity map -/
  example {X : 𝒞} : X ⟶ X := x : X ⊢ₑ x

  /-- the twist morphism -/
  example {X Y : 𝒞} : X ⊗ Y ⟶ Y ⊗ X :=
    x : X, y : Y ⊢ₑ ⟨ y, x ⟩

  /-- the diagonal -/
  example {X : 𝒞} : X ⟶ X ⊗ X :=
    x : X ⊢ₑ ⟨ x, x ⟩

  /-- the first projection is the first projection -/
  example {X Y : 𝒞} : (p : X ⊗ Y ⊢ₑ fst p) = (p : X ⊗ Y ⊢ₑ $(fp.fst X Y) p) := by simp

  /-- A silly example showing that we can embed the internal language inside `$(⋯)`. Please don't do this. -/
  example {X : 𝒞} : X ⟶ X := x : X ⊢ₑ $(y : X ⊢ₑ y) x

  /-- identity on the terminal -/
  example : 𝟙_ 𝒞 ⟶ 𝟙_ 𝒞 := ⊢ₑ tt

  /-- composition of morphisms -/
  example {X Y Z: 𝒞} (g : Y ⟶ Z) (f : X ⟶ Y): X ⟶ Z :=
    x : X ⊢ₑ $(g) $(f) x

  /-- right associator -/
  def assocRight (X Y Z : 𝒞) : (X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z) :=
  p : (X ⊗ Y) ⊗ Z ⊢ₑ ⟨fst (fst p), ⟨snd (fst p), snd p⟩⟩

  /-- left associator -/
  def assocLeft (X Y Z : 𝒞) : X ⊗ (Y ⊗ Z) ⟶ (X ⊗ Y) ⊗ Z :=
  p : X ⊗ (Y ⊗ Z) ⊢ₑ ⟨⟨fst p, fst (snd p)⟩, snd (snd p)⟩

  /-- the associators are inverses -/
  example {X Y Z : 𝒞} : assocLeft X Y Z ≫ assocRight X Y Z = 𝟙 _ := by
   simp [assocLeft, assocRight]
   aesop_cat

end Examples
