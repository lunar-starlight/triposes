import Triposes.Basic

open CategoryTheory
open MonoidalCategory


namespace Language

  -- universe u v
  -- variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  /- Fix a tripos -/
  -- variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]
  open Lean

  -- def π {X Y : 𝒞} : X ⊗ Y ⟶ Y := fp.snd _ _

  -- /-- `Formula As` denotes a predicate in `P (listProd As)`.
  --     It should be easy to add other connectives and quantifiers. -/
  -- inductive Formula : Lean.AssocList Lean.Name 𝒞 → Type _ where
  --   /-- Application of a predicate to an expression -/
  -- | app : ∀ {B As}, P₀ (P := P) B → Expr As B → Formula As
  --   /-- The true predicate -/
  -- | tru : ∀ {As}, Formula As
  --   /-- The false predicate -/
  -- | fal : ∀ {As}, Formula As
  --   /-- Conjunction -/
  -- | conj : ∀ {As}, Formula As → Formula As → Formula As
  --   /-- Disjunction -/
  -- | disj : ∀ {As}, Formula As → Formula As → Formula As
  --   /-- Implication -/
  -- | impl : ∀ {As}, Formula As → Formula As → Formula As
  --   /-- Universal quantifier, we always quantify on `var .0` -/
  -- | all : ∀ (A : 𝒞) {As : List 𝒞}, Formula (A :: As) → Formula As
  --   /-- Existential quantifier, we always quantify on `var .0` -/
  -- | any : ∀ (A : 𝒞) {As : List 𝒞}, Formula (A :: As) → Formula As

  -- def Formula.eval (As : Lean.AssocList Lean.Name 𝒞) : Formula (P := P) As → P₀ (P := P) (listProd As)
  -- | .app ρ e => P₁ (Expr.eval As e) ρ
  -- | .tru => ⊤
  -- | .fal => ⊥
  -- | .conj φ ψ => eval As φ ⊓ eval As ψ
  -- | .disj φ ψ => eval As φ ⊔ eval As ψ
  -- | .impl φ ψ => eval As φ ⇨ eval As ψ
  -- | .all _ φ =>
  --   /- This case is somewhat complicated by the fact that `listProd [A]` is special. -/
  --   match As with
  --   | [] => (T.𝔸 π).map (P₁ (fp.fst _ _) (eval _ φ))
  --   | _ :: _ => (T.𝔸 π).map (eval _ φ)
  -- | .any _ φ =>
  --   match As with
  --   | [] => (T.𝔼 π).map (P₁ (fp.fst _ _) (eval _ φ))
  --   | _ :: _ => (T.𝔼 π).map (eval _ φ)


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

  macro_rules
  | `($Γ:fpcontext ⊢ₕ ⟪ $f:term | $t:fpterm ⟫) => do
    let t ← `($Γ:fpcontext ⊢ₑ $t)
    `(P₁ $t $f)
  | `($Γ:fpcontext ⊢ₕ $s:fpformula ⊓ $t:fpformula) => do
    let s ← `($Γ:fpcontext ⊢ₕ $s)
    let t ← `($Γ:fpcontext ⊢ₕ $t)
    `($s ⊓ $t)
  | `($Γ:fpcontext ⊢ₕ $s:fpformula ⊔ $t:fpformula) => do
    let s ← `($Γ:fpcontext ⊢ₕ $s)
    let t ← `($Γ:fpcontext ⊢ₕ $t)
    `($s ⊔ $t)
  | `($Γ:fpcontext ⊢ₕ $s:fpformula ⇒ $t:fpformula) => do
    let s ← `($Γ:fpcontext ⊢ₕ $s)
    let t ← `($Γ:fpcontext ⊢ₕ $t)
    `($s ⇨ $t)
  | `($Γ:fpcontext ⊢ₕ $s:fpformula ⇔ $t:fpformula) => do
    let s ← `($Γ:fpcontext ⊢ₕ $s)
    let t ← `($Γ:fpcontext ⊢ₕ $t)
    `($s ⇔ $t)
  | `($_:fpcontext ⊢ₕ ⊤) => `(⊤)
  | `($_:fpcontext ⊢ₕ ⊥) => `(⊥)
  | `($Γ:fpcontext ⊢ₕ ∀ $y:ident : $Y:term , $t:fpformula) => do
    let jdgs ← unfold Γ
    let t ← `($y:ident : $Y:term , $jdgs,* ⊢ₕ $t)
    `((Tripos.𝔸 (ChosenFiniteProducts.snd _ _)).map $t)
  | `($Γ:fpcontext ⊢ₕ ∃ $y:ident : $Y:term , $t:fpformula) => do
    let jdgs ← unfold Γ
    let t ← `($y:ident : $Y:term , $jdgs,* ⊢ₕ $t)
    `((Tripos.𝔼 (ChosenFiniteProducts.snd _ _)).map $t)
  | `($Γ:fpcontext ⊢ₕ ($t:fpformula)) => `($Γ:fpcontext ⊢ₕ $t)
  | `($Γ:fpcontext ⊢ $t:fpformula) => `(($Γ:fpcontext ⊢ₕ $t) ≥ ⊤)

end Language
