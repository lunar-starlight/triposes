import Triposes.Basic
import Triposes.Language.FPCatDSL2

open CategoryTheory
open MonoidalCategory


namespace Language

  section Structure
    universe u v
    variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

    /- Fix a tripos -/
    variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

    /-- `Formula' As` denotes a predicate in `P (listProd As)`. -/
    inductive Formula' [T : Tripos P] : 𝒞 → Type _ where
      /-- Injection from underlying structure-/
    | ι : ∀ {As}, P₀ (P := P) As → Formula' As
      /-- Application of a predicate to an expression -/
    | app : ∀ {B As}, Formula' B → (As ⟶ B) → Formula' As
      /-- The true predicate -/
    | tru : ∀ {As}, Formula' As
      /-- The false predicate -/
    | fal : ∀ {As}, Formula' As
      /-- Conjunction -/
    | conj : ∀ {As}, Formula' As → Formula' As → Formula' As
      /-- Disjunction -/
    | disj : ∀ {As}, Formula' As → Formula' As → Formula' As
      /-- Implication -/
    | impl : ∀ {As}, Formula' As → Formula' As → Formula' As
      /-- Universal quantifier -/
    | all : ∀ {Bs As}, (Bs ⟶ As) → Formula' Bs → Formula' As
      /-- Existential quantifier -/
    | any : ∀ {Bs As}, (Bs ⟶ As) → Formula' Bs → Formula' As

    /-- The evaluation of a formula into a bona fide element of the Heyting algebra -/
    def Formula'.eval {As : 𝒞} : Formula' (P := P) As → P₀ (P := P) As
    | .ι x => x
    | .app ρ f => P₁ f (eval ρ)
    | .tru => ⊤
    | .fal => ⊥
    | .conj φ ψ => eval φ ⊓ eval ψ
    | .disj φ ψ => eval φ ⊔ eval ψ
    | .impl φ ψ => eval φ ⇨ eval ψ
    | .all f φ => T.𝔸.map f (eval φ)
    | .any f φ => T.𝔼.map f (eval φ)

    /-- The definition of equality of formulas up to evaluation -/
    @[simp]
    def FormulaSetoid {As : 𝒞} : Setoid (Formula' (P := P) As) where
      r φ ψ := φ.eval = ψ.eval
      iseqv := by
        constructor
        case refl => simp
        case symm => exact Eq.symm
        case trans => exact Eq.trans
    -- def Formula_Eq {As : 𝒞} (φ ψ : Formula' (P := P) As) := φ.eval = ψ.eval

    /-- `Formula As` denotes an equivalence class of a predicate in `P (listProd As)`. -/
    def Formula (As : 𝒞) := Quotient (FormulaSetoid (As := As) (P := P))

    /-- The quotient map for `Formula` -/
    @[simp]
    def q {As : 𝒞} : Formula' (P := P) As → Formula (P := P) As := Quotient.mk FormulaSetoid

    /-- Injection from underlying structure-/
    def Formula.ι {As : 𝒞} (x : P₀ (P := P) As) : Formula (P := P) As := q (P := P) (.ι x)
    /-- The true predicate -/
    def Formula.tru {As : 𝒞} : Formula (P := P) As := q (P := P) (.tru (As := As))
    /-- The false predicate -/
    def Formula.fal {As : 𝒞} : Formula (P := P) As := q (P := P) (.fal (As := As))

    /-- Equality of `Formula`s is equality of evaluations of representatives -/
    syntax "unfold_quotient" : tactic
    local syntax "formula_unop_cong" : tactic
    local syntax "formula_binop_cong" : tactic
    macro_rules
      | `(tactic| unfold_quotient) =>
        `(tactic| apply Quotient.eq.mpr; simp [FormulaSetoid])
      | `(tactic| formula_binop_cong) =>
        `(tactic| rintro _ _ _ _ H K; unfold_quotient; unfold Formula'.eval; rw [H, K])
      | `(tactic| formula_unop_cong) =>
        `(tactic| rintro _ _ H; unfold_quotient; unfold Formula'.eval; rw [H])

    /-- Application of a predicate to an expression -/
    def Formula.app {B As : 𝒞} : Formula (P := P) B → (f : As ⟶ B) → Formula (P := P) As :=
      Quotient.lift
      (fun φ ↦ q (P := P) ∘ Formula'.app (As := As) (B := B) φ)
      (by
        rintro _ _ H
        funext
        unfold_quotient
        unfold Formula'.eval
        rw [H]
      )

    /-- Conjunction -/
    def Formula.conj {As : 𝒞} : Formula (P := P) As → Formula (P := P) As → Formula (P := P) As :=
      Quotient.lift₂
      (fun φ ↦ q (P := P) ∘ (Formula'.conj (As := As) φ))
      (by formula_binop_cong)

    /-- Disjunction -/
    def Formula.disj {As : 𝒞} : Formula (P := P) As → Formula (P := P) As → Formula (P := P) As :=
      Quotient.lift₂
      (fun φ ↦ q (P := P) ∘ (Formula'.disj (As := As) φ))
      (by formula_binop_cong)

    /-- Implication -/
    def Formula.impl {As : 𝒞} : Formula (P := P) As → Formula (P := P) As → Formula (P := P) As :=
      Quotient.lift₂
      (fun φ ↦ q (P := P) ∘ (Formula'.impl (As := As) φ))
      (by formula_binop_cong)

    /-- Universal quantifier -/
    def Formula.all {Bs As : 𝒞} (f : As ⟶ Bs) : Formula (P := P) As → Formula (P := P) Bs :=
      Quotient.lift (q (P := P) ∘ Formula'.all f)
      (by formula_unop_cong)

    /-- Existential quantifier -/
    def Formula.any {Bs As : 𝒞} (f : As ⟶ Bs) : Formula (P := P) As → Formula (P := P) Bs :=
      Quotient.lift (q (P := P) ∘ Formula'.any f)
      (by formula_unop_cong)

    /-- The evaluation of a formula into a bona fide element of the Heyting algebra -/
    @[reducible]
    def Formula.eval {As : 𝒞} : Formula (P := P) As → P₀ (P := P) As :=
      Quotient.lift (Formula'.eval (As := As) (P := P)) (by
        rintro _ _ H
        rw [H]
      )

    instance {As : 𝒞} : Coe (@Bundled.α HeytingAlgebra (P₀ (P := P) As)) (Formula (P := P) As) where
      coe x := .ι x

  end Structure

  section Syntax
    open Lean

    /-- Syntax for heyting biimplication -/
    scoped infixl:100 " ⇔ " => bihimp

    /-- Syntax category for formulas -/
    declare_syntax_cat fpformula

    /-- Top element -/
    syntax "⊤" : fpformula

    /-- Bottom element -/
    syntax "⊥" : fpformula

    /-- Conjunction -/
    syntax:70 fpformula "⊓" fpformula:71 : fpformula

    /-- Disjunction -/
    syntax:60 fpformula "⊔" fpformula:61 : fpformula

    /-- Implication -/
    syntax:50 fpformula "⇒" fpformula:51 : fpformula

    /-- Biimplication -/
    syntax:50 fpformula "⇔" fpformula:51 : fpformula

    /-- Universal quantifier -/
    syntax:80 "∀" typing_judgement "," fpformula:79 : fpformula

    /-- Existential quantifier -/
    syntax:80 "∃" typing_judgement "," fpformula:79 : fpformula

    /-- Grouping -/
    syntax:100 "(" fpformula ")" : fpformula

    /-- Evaluation of a relation on some variables (given by an `fpterm`) -/
    syntax:1025 "⟪" term "|" fpterm "⟫" : fpformula

    /-- The element of `Formula` defined by the internal language -/
    syntax:30 fpcontext "⊢ₕ" fpformula : term
    /-- Truth in the internal language -/
    syntax:30 fpcontext "⊢" fpformula : term

    /-- Conversion of the internal syntax to a formula -/
    macro_rules
    | `($Γ:fpcontext ⊢ₕ ⟪ $t:term | $f:fpterm ⟫) => do
      let f ← `($Γ:fpcontext ⊢ₑ $f)
      `(Formula.app $t $f)
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
    | `($Γ:fpcontext ⊢ₕ ⊤) => do
      let As ← prodify Γ
      `(Formula.tru (As := $As))
    | `($Γ:fpcontext ⊢ₕ ⊥) => do
      let As ← prodify Γ
      `(Formula.fal (As := $As))
    | `( ⊢ₕ ∀ $y:ident : $Y:term , $t:fpformula) => do
      let t ← `( $y:ident : $Y:term ⊢ₕ $t)
      `(Formula.all (ChosenFiniteProducts.toUnit $Y) $t)
    | `($jdgs:typing_judgement,* ⊢ₕ ∀ $y:ident : $Y:term , $t:fpformula) => do
      let t ← `($jdgs:typing_judgement,* , $y:ident : $Y:term ⊢ₕ $t)
      `(Formula.all (ChosenFiniteProducts.fst _ _) $t)
    | `( ⊢ₕ ∃ $y:ident : $Y:term , $t:fpformula) => do
      let t ← `( $y:ident : $Y:term ⊢ₕ $t)
      `(Formula.any (ChosenFiniteProducts.toUnit $Y) $t)
    | `($jdgs:typing_judgement,* ⊢ₕ ∃ $y:ident : $Y:term , $t:fpformula) => do
      let t ← `($jdgs:typing_judgement,* , $y:ident : $Y:term  ⊢ₕ $t)
      `(Formula.any (ChosenFiniteProducts.fst _ _) $t)
    | `($Γ:fpcontext ⊢ₕ ($t:fpformula)) => `($Γ:fpcontext ⊢ₕ $t)
    | `($Γ:fpcontext ⊢ $t:fpformula) => `(($Γ:fpcontext ⊢ₕ $t) = Formula.tru)

    namespace Delab
      open PrettyPrinter

      local syntax term "*" : term
      @[app_unexpander Formula.ι]
      def unexpFormula_ι : Unexpander
        | `($_ι $t) => `($t)
        | `($_ι) => pure $ mkIdent `ι
      @[app_unexpander Formula.app]
      def unexpFormula_app : Unexpander
        | `($_app $t $f) => `(($f*) $t)
        | `($_app) => pure $ mkIdent `app
      @[app_unexpander Formula.conj]
      def unexpFormula_conj : Unexpander
        | `($_conj $X $Y) => `($X ⊓ $Y)
        | `($_conj) => pure $ mkIdent `conj
      @[app_unexpander Formula.disj]
      def unexpFormula_disj : Unexpander
        | `($_disj $X $Y) => `($X ⊔ $Y)
        | `($_disj) => pure $ mkIdent `disj
      @[app_unexpander Formula.impl]
      def unexpFormula_impl : Unexpander
        | `($_impl $X $Y) => `($X ⇨ $Y)
        | `($_impl) => pure $ mkIdent `impl
      @[app_unexpander Formula.tru]
      def unexpFormula_tru : Unexpander
        | `($_tru) => `(⊤)
      @[app_unexpander Formula.fal]
      def unexpFormula_fal : Unexpander
        | `($_fal) => `(⊥)

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
   end Delab

  end Syntax

end Language
