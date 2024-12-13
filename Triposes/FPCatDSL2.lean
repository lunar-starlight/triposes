import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory
open MonoidalCategory

section ProjDSL

  /- We work over a cartesian closed category -/
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞]

  /- To simplify the definition of `proj`, we use the terminal object of `𝒞` as the default element of `𝒞`. -/
  instance : Inhabited 𝒞 where default := 𝟙_ 𝒞

  /-- The product of a list of objects, where we make sure that the product of `[A]` is `A`, rather than `A ⊗ 𝟙_ 𝒞`. -/
  @[reducible]
  def listProd : Lean.AssocList Lean.Name 𝒞 → 𝒞
  | .nil => 𝟙_ 𝒞
  | .cons _ A .nil => A
  | .cons _ A As => A ⊗ listProd As

  @[simp]
  def lookup (As : Lean.AssocList Lean.Name 𝒞) (x : Lean.Name) : 𝒞 := (As.find? x).getD (𝟙_ 𝒞)

  /-- The k-th projection from a product, or the terminal morphism if the index is invalid -/
  @[reducible]
  def proj (As : Lean.AssocList Lean.Name 𝒞) (x : Lean.Name) : listProd As ⟶ lookup As x :=
    match As  with
    | .nil => fp.toUnit _ -- invalid index

    | .cons x' A .nil =>
      if h : x' = x then
        (by
         simp [Lean.AssocList.find?, h]
         exact 𝟙 A)
      else
        (by
         simp [Lean.AssocList.find?, not_beq_of_ne h]
         exact fp.toUnit _)

    | .cons x' A (.cons y B Bs) =>
      if h : x' = x then
        (by
        simp [Lean.AssocList.find?, h]
        exact fp.fst _ _
        )
      else
        (by
         simp [Lean.AssocList.find?, not_beq_of_ne h]
         exact fp.snd _ _ ≫ proj (.cons y B Bs) x)

  /-- Given an association list of objects `As = [x₀ : A₀, …, xₙ : Aₙ]` we can form expressions that denote
      morphisms `A₀ ⊗ ⋯ ⊗ Aₙ ⟶ B` but are written as if objects are sets. -/
  inductive Expr (As : Lean.AssocList Lean.Name 𝒞) : 𝒞 → Type _ where
    /-- Variable `var x` refers to the `x`-th element of `As`. -/
    | var : ∀ (x : Lean.Name), Expr As (lookup As x)
    /-- The unique element of the terminal object -/
    | tt : Expr As (𝟙_ _)
    /-- Ordered pair -/
    | pair : ∀ {B C}, Expr As B → Expr As C → Expr As (B ⊗ C)
    /-- First projection -/
    | fst : ∀ {B C}, Expr As (B ⊗ C) → Expr As B
    /-- Second projection -/
    | snd : ∀ {B C}, Expr As (B ⊗ C) → Expr As C
    /-- Application of a morphism -/
    | app : ∀ {B C : 𝒞}, (B ⟶ C) → Expr As B → Expr As C

  declare_syntax_cat fpentry
  syntax ident ":" term : fpentry
  -- macro_rules
  -- | `(fpentry| $x:ident : $A:term) => `(($(Lean.quote x.getId), $A))

  declare_syntax_cat fpcontext
  syntax fpentry,* : fpcontext

  macro_rules
  | `(fpcontext| $[$key:ident : $value:term],* ) =>
    let key := key.map (fun x => Lean.quote x.getId)
    `([$[($key, $value)],*].toAssocList)

  declare_syntax_cat fpterm
  syntax ident : fpterm
  syntax "tt" : fpterm
  syntax "⟨" fpterm "," fpterm "⟩" : fpterm
  syntax "fst" fpterm : fpterm
  syntax "snd" fpterm : fpterm
  syntax term fpterm : fpterm

  syntax term "⊢ₑ" fpterm : term

  #check Lean.Syntax.getId

  macro_rules
  | `($Γ ⊢ₑ $x:ident) => `(proj $Γ $(Lean.quote x.getId))
  | `($Γ ⊢ₑ ⟨ $a:fpterm, $b:fpterm ⟩) => `(fp.lift ($Γ ⊢ₑ $a) ($Γ ⊢ₑ $b))
  | `($Γ ⊢ₑ fst $a:fpterm) => `(($Γ ⊢ₑ $a) ≫ fp.fst _ _)
  | `($Γ ⊢ₑ snd $a:fpterm) => `(($Γ ⊢ₑ $a) ≫ fp.snd _ _)
  | `($Γ ⊢ₑ $f:term $a:fpterm) => `(($Γ ⊢ₑ $a) ≫ $f)

  /-- Evaluate an expression to the corresponding morphism -/
  @[reducible]
  def Expr.eval (As : Lean.AssocList Lean.Name 𝒞) {B : 𝒞} : Expr As B → (listProd As ⟶ B)
    | .var k => proj As k
    | .tt => fp.toUnit _
    | .pair a b => fp.lift a.eval b.eval
    | .fst a => a.eval ≫ fp.fst _ _
    | .snd a => a.eval ≫ fp.snd _ _
    | .app f a => a.eval ≫ f

  namespace Proj
    @[reducible]
    def id {As : Lean.AssocList Lean.Name 𝒞} : listProd As ⟶ listProd As := 𝟙 (listProd As)

    @[reducible]
    def swap {X Y : 𝒞} : X ⊗ Y ⟶ Y ⊗ X :=
      .cons `x X (.cons `y Y .nil) ⊢ₑ ⟨ y, x ⟩

    @[reducible]
    def diag {X : 𝒞} : X ⟶ X ⊗ X :=
      .cons `x X .nil ⊢ₑ ⟨ x, x ⟩
  end Proj

end ProjDSL
