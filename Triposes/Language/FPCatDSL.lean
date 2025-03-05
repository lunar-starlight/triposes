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
  def listProd : List 𝒞 → 𝒞
  | [] => 𝟙_ 𝒞
  | [A] => A
  | A :: As => A ⊗ listProd As

  /-- The k-th projection from a product, or the terminal morphism if the index is invalid -/
  @[reducible]
  def proj (As : List 𝒞) (k : ℕ) : listProd As ⟶ As.get! k :=
    match As, k with
    | [], _ => fp.toUnit _ -- invalid index
    | [A], 0 => 𝟙 A
    | [_], .succ _ => fp.toUnit _ -- invalid index
    | _ :: _ :: _, 0 => fp.fst _ _
    | _ :: (A :: As), .succ k => fp.snd _ _ ≫ proj (A :: As) k

  /-- Given a list of objects `As = [A₀, …, Aₙ]` we can form expressions that denote morphisms `A₀ ⊗ ⋯ ⊗ Aₙ ⟶ B` but are written as if objects are sets. -/
  inductive Expr (As : List 𝒞) : 𝒞 → Type _ where
    /-- Variable `var k` refers to the `k`-th element of `As`. That is, variables are de Bruijn levels. -/
    | var : ∀ (k : ℕ), Expr As (As.get! k)
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

  @[inherit_doc]
  notation:100 "⟨" a "," b "⟩" => Expr.pair a b

  /-- Ordered triple -/
  notation:100 "⟨" a "," b "," c "⟩" => Expr.pair a (Expr.pair b c)

  /-- Evaluate an expression to the corresponding morphism -/
  @[reducible]
  def Expr.eval (As : List 𝒞) {B : 𝒞} : Expr As B → (listProd As ⟶ B)
    | .var k => proj As k
    | .tt => fp.toUnit _
    | .pair a b => fp.lift a.eval b.eval
    | .fst a => a.eval ≫ fp.fst _ _
    | .snd a => a.eval ≫ fp.snd _ _
    | .app f a => a.eval ≫ f

  notation:30 As " ⊢ₑ " e => Expr.eval As e

  namespace Proj
    @[reducible]
    def id {As : List 𝒞} : listProd As ⟶ listProd As := 𝟙 (listProd As)

    @[reducible]
    def swap {X Y : 𝒞} : X ⊗ Y ⟶ Y ⊗ X :=
      [X, Y] ⊢ₑ ⟨ .var 1, .var 0 ⟩

    @[reducible]
    def diag {X : 𝒞} : X ⟶ X ⊗ X :=
      [X] ⊢ₑ ⟨ .var 0, .var 0 ⟩
  end Proj

end ProjDSL
