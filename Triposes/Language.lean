import Triposes.Basic

open CategoryTheory
open MonoidalCategory


namespace Language

  section Structure
    universe u v
    variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

    /- Fix a tripos -/
    variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

    -- /- To simplify the definition of `proj`, we use the terminal object of `𝒞` as the default element of `𝒞`. -/
    -- instance : Inhabited 𝒞 where default := 𝟙_ 𝒞

    /-- The product of a list of objects, where we make sure that the product of `[A]` is `A`, rather than `A ⊗ 𝟙_ 𝒞`. -/
    @[reducible]
    def listProd : Lean.AssocList Lean.Name 𝒞 → 𝒞
    | .nil => 𝟙_ 𝒞
    | .cons _ A .nil => A
    | .cons _ A As => A ⊗ listProd As

    -- @[simp]
    -- def lookup (As : Lean.AssocList Lean.Name 𝒞) (x : Lean.Name) : 𝒞 := (As.find? x).getD (𝟙_ 𝒞)

    -- /-- The k-th projection from a product, or the terminal morphism if the index is invalid -/
    -- @[reducible]
    -- def proj (As : Lean.AssocList Lean.Name 𝒞) (x : Lean.Name) : listProd As ⟶ lookup As x :=
    --   match As  with
    --   | .nil => fp.toUnit _ -- invalid index

    --   | .cons x' A .nil =>
    --     if h : x' = x then
    --       (by
    --        simp [Lean.AssocList.find?, h]
    --        exact 𝟙 A)
    --     else
    --       (by
    --        simp [Lean.AssocList.find?, not_beq_of_ne h]
    --        exact fp.toUnit _)

    --   | .cons x' A (.cons y B Bs) =>
    --     if h : x' = x then
    --       (by
    --       simp [Lean.AssocList.find?, h]
    --       exact fp.fst _ _
    --       )
    --     else
    --       (by
    --        simp [Lean.AssocList.find?, not_beq_of_ne h]
    --        exact fp.snd _ _ ≫ proj (.cons y B Bs) x)

    -- /-- Given an association list of objects `As = [x₀ : A₀, …, xₙ : Aₙ]` we can form expressions that denote
    --     morphisms `A₀ ⊗ ⋯ ⊗ Aₙ ⟶ B` but are written as if objects are sets. -/
    -- inductive Expr (As : Lean.AssocList Lean.Name 𝒞) : 𝒞 → Type _ where
    --   /-- Variable `var x` refers to the `x`-th element of `As`. -/
    --   | var : ∀ (x : Lean.Name), Expr As (lookup As x)
    --   /-- The unique element of the terminal object -/
    --   | tt : Expr As (𝟙_ _)
    --   /-- Ordered pair -/
    --   | pair : ∀ {B C}, Expr As B → Expr As C → Expr As (B ⊗ C)
    --   /-- First projection -/
    --   | fst : ∀ {B C}, Expr As (B ⊗ C) → Expr As B
    --   /-- Second projection -/
    --   | snd : ∀ {B C}, Expr As (B ⊗ C) → Expr As C
    --   /-- Application of a morphism -/
    --   | app : ∀ {B C : 𝒞}, (B ⟶ C) → Expr As B → Expr As C


    -- /-- Evaluate an expression to the corresponding morphism -/
    -- @[reducible]
    -- def Expr.eval (As : Lean.AssocList Lean.Name 𝒞) {B : 𝒞} : Expr As B → (listProd As ⟶ B)
    --   | .var k => proj As k
    --   | .tt => fp.toUnit _
    --   | .pair a b => fp.lift a.eval b.eval
    --   | .fst a => a.eval ≫ fp.fst _ _
    --   | .snd a => a.eval ≫ fp.snd _ _
    --   | .app f a => a.eval ≫ f


    /-- `Formula As` denotes a predicate in `P (listProd As)`.
        It should be easy to add other connectives and quantifiers. -/
    inductive Formula : Lean.AssocList Lean.Name 𝒞 → Type _ where
      /-- Application of a predicate to an expression -/
      --   | `($Γ:fpcontext ⊢ₕ ⟪ $f:term | $t:fpterm ⟫) => do
      -- let t ← `($Γ:fpcontext ⊢ₑ $t)
      -- `(P₁ $t $f)
    | app : ∀ {B As}, P₀ (P := P) (listProd B) → (listProd As ⟶ listProd B) → Formula As
      /-- The true predicate -/
    | tru : ∀ {As}, Formula As
      /-- The false predicate -/
    | fal : ∀ {As}, Formula As
      /-- Conjunction -/
    | conj : ∀ {As}, Formula As → Formula As → Formula As
      /-- Disjunction -/
    | disj : ∀ {As}, Formula As → Formula As → Formula As
      /-- Implication -/
    | impl : ∀ {As}, Formula As → Formula As → Formula As
      /-- Universal quantifier -/
    | all : ∀ {Bs As}, (listProd Bs ⟶ listProd As) → Formula Bs → Formula As
      /-- Existential quantifier -/
    | any : ∀ {Bs As}, (listProd Bs ⟶ listProd As) → Formula Bs → Formula As

    def Formula.eval {As : Lean.AssocList Lean.Name 𝒞} : Formula (P := P) As → P₀ (P := P) (listProd As)
    | .app ρ f => P₁ f ρ
    | .tru => ⊤
    | .fal => ⊥
    | .conj φ ψ => eval φ ⊓ eval ψ
    | .disj φ ψ => eval φ ⊔ eval ψ
    | .impl φ ψ => eval φ ⇨ eval ψ
    | .all f φ => (Tripos.𝔸 f).map (eval φ)
    | .any f φ => (Tripos.𝔼 f).map (eval φ)
  end Structure

  section Syntax
    open Lean

    scoped infixl:100 " ⇔ " => bihimp

    declare_syntax_cat fpformula
    syntax "⊤" : fpformula
    syntax "⊥" : fpformula
    syntax:70 fpformula "⊓" fpformula:71 : fpformula
    syntax:60 fpformula "⊔" fpformula:61 : fpformula
    syntax:50 fpformula "⇒" fpformula:51 : fpformula
    syntax:50 fpformula "⇔" fpformula:51 : fpformula
    syntax:80 "∀" typing_judgement "," fpformula:79 : fpformula
    syntax:80 "∃" typing_judgement "," fpformula:79 : fpformula
    syntax:100 "(" fpformula ")" : fpformula
    syntax:1025 "⟪" term "|" fpterm "⟫" : fpformula

    syntax:30 fpcontext "⊢ₕ" fpformula : term
    syntax:30 fpcontext "⊢" fpformula : term

    partial def unfold : TSyntax `fpcontext → MacroM (Array (TSyntax `typing_judgement))
    | `(fpcontext| ) => pure Array.empty
    | `(fpcontext| $x:ident : $A:term) =>
      do
        let j ← `(typing_judgement| $x:ident : $A)
        return Array.mk [j]
    | `(fpcontext| $x:ident : $A:term, $Γ:typing_judgement,*) =>
      do
        let Γ ← `(fpcontext| $Γ:typing_judgement,*)
        let As ← unfold Γ
        let j ← `(typing_judgement| $x:ident : $A)
        return Array.mk (j :: As.toList)
    | _ => Macro.throwError "invalid context syntax"

    -- macro_rules
    -- | `($Γ:fpcontext ⊢ₕ ⟪ $f:term | $t:fpterm ⟫) => do
    --   let t ← `($Γ:fpcontext ⊢ₑ $t)
    --   `(P₁ $t $f)
    -- | `($Γ:fpcontext ⊢ₕ $s:fpformula ⊓ $t:fpformula) => do
    --   let s ← `($Γ:fpcontext ⊢ₕ $s)
    --   let t ← `($Γ:fpcontext ⊢ₕ $t)
    --   `($s ⊓ $t)
    -- | `($Γ:fpcontext ⊢ₕ $s:fpformula ⊔ $t:fpformula) => do
    --   let s ← `($Γ:fpcontext ⊢ₕ $s)
    --   let t ← `($Γ:fpcontext ⊢ₕ $t)
    --   `($s ⊔ $t)
    -- | `($Γ:fpcontext ⊢ₕ $s:fpformula ⇒ $t:fpformula) => do
    --   let s ← `($Γ:fpcontext ⊢ₕ $s)
    --   let t ← `($Γ:fpcontext ⊢ₕ $t)
    --   `($s ⇨ $t)
    -- | `($Γ:fpcontext ⊢ₕ $s:fpformula ⇔ $t:fpformula) => do
    --   let s ← `($Γ:fpcontext ⊢ₕ $s)
    --   let t ← `($Γ:fpcontext ⊢ₕ $t)
    --   `($s ⇔ $t)
    -- | `($_:fpcontext ⊢ₕ ⊤) => `(⊤)
    -- | `($_:fpcontext ⊢ₕ ⊥) => `(⊥)
    -- | `($jdgs:typing_judgement,* ⊢ₕ ∀ $y:ident : $Y:term , $t:fpformula) => do
    --   let t ← `($jdgs:typing_judgement,* , $y:ident : $Y:term ⊢ₕ $t)
    --   `((Tripos.𝔸 (ChosenFiniteProducts.fst _ _)).map $t)
    -- | `($jdgs:typing_judgement,* ⊢ₕ ∃ $y:ident : $Y:term , $t:fpformula) => do
    --   let t ← `($jdgs:typing_judgement,* , $y:ident : $Y:term  ⊢ₕ $t)
    --   `((Tripos.𝔼 (ChosenFiniteProducts.fst _ _)).map $t)
    -- | `($Γ:fpcontext ⊢ₕ ($t:fpformula)) => `($Γ:fpcontext ⊢ₕ $t)
    -- | `($Γ:fpcontext ⊢ $t:fpformula) => `(($Γ:fpcontext ⊢ₕ $t) ≥ ⊤)

    macro_rules
    | `($Γ:fpcontext ⊢ₕ ⟪ $f:term | $t:fpterm ⟫) => do
      let t ← `($Γ:fpcontext ⊢ₑ $t)
      `(Formula.app $f $t)
    | `($Γ:fpcontext ⊢ₕ $s:fpformula ⊓ $t:fpformula) => do
      let s ← `($Γ:fpcontext ⊢ₕ $s)
      let t ← `($Γ:fpcontext ⊢ₕ $t)
      `(Formula.conj $s $t)
    | `($Γ:fpcontext ⊢ₕ $s:fpformula ⊔ $t:fpformula) => do
      let s ← `($Γ:fpcontext ⊢ₕ $s)
      let t ← `($Γ:fpcontext ⊢ₕ $t)
      `(Formula.disj $s $t)
    | `($Γ:fpcontext ⊢ₕ $s:fpformula ⇒ $t:fpformula) => do
      let s ← `($Γ:fpcontext ⊢ₕ $s)
      let t ← `($Γ:fpcontext ⊢ₕ $t)
      `(Formula.impl $s $t)
    | `($Γ:fpcontext ⊢ₕ $s:fpformula ⇔ $t:fpformula) => do
      let s ← `($Γ:fpcontext ⊢ₕ $s)
      let t ← `($Γ:fpcontext ⊢ₕ $t)
      `(Formula.conj (Formula.impl $s $t) (Formula.impl $t $s))
    | `($_:fpcontext ⊢ₕ ⊤) => `(Formula.tru)
    | `($_:fpcontext ⊢ₕ ⊥) => `(Formula.fal)
    | `($jdgs:typing_judgement,* ⊢ₕ ∀ $y:ident : $Y:term , $t:fpformula) => do
      let t ← `($jdgs:typing_judgement,* , $y:ident : $Y:term ⊢ₕ $t)
      `(Formula.all (ChosenFiniteProducts.fst _ _) $t)
    | `($jdgs:typing_judgement,* ⊢ₕ ∃ $y:ident : $Y:term , $t:fpformula) => do
      let t ← `($jdgs:typing_judgement,* , $y:ident : $Y:term  ⊢ₕ $t)
      `(Formula.any (ChosenFiniteProducts.fst _ _) $t)
    | `($Γ:fpcontext ⊢ₕ ($t:fpformula)) => `(Formula.eval ($Γ:fpcontext ⊢ₕ $t))
    | `($Γ:fpcontext ⊢ $t:fpformula) => `((Formula.eval (T := by infer_instance) ($Γ:fpcontext ⊢ₕ $t)) ≥ ⊤)

  end Syntax

end Language
