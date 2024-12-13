import Triposes.Advanced

open CategoryTheory
open MonoidalCategory


namespace Language

  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  /- Fix a tripos -/
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  def π {X Y : 𝒞} : X ⊗ Y ⟶ Y := fp.snd _ _

  /-- `Formula As` denotes a predicate in `P (listProd As)`.
      It should be easy to add other connectives and quantifiers. -/
  inductive Formula : List 𝒞 → Type _ where
    /-- Application of a predicate to an expression -/
  | app : ∀ {B As}, P₀ (P := P) B → Expr As B → Formula As
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
    /-- Universal quantifier, we always quantify on `var .0` -/
  | all : ∀ (A : 𝒞) {As : List 𝒞}, Formula (A :: As) → Formula As
    /-- Existential quantifier, we always quantify on `var .0` -/
  | any : ∀ (A : 𝒞) {As : List 𝒞}, Formula (A :: As) → Formula As

  def Formula.eval (As : List 𝒞) : Formula (P := P) As → P₀ (P := P) (listProd As)
  | .app ρ e => P₁ (As ⊢ₑ e) ρ
  | .tru => ⊤
  | .fal => ⊥
  | .conj φ ψ => eval As φ ⊓ eval As ψ
  | .disj φ ψ => eval As φ ⊔ eval As ψ
  | .impl φ ψ => eval As φ ⇨ eval As ψ
  | .all _ φ =>
    /- This case is somewhat complicated by the fact that `listProd [A]` is special. -/
    match As with
    | [] => (T.𝔸 π).map (P₁ (fp.fst _ _) (eval _ φ))
    | _ :: _ => (T.𝔸 π).map (eval _ φ)
  | .any _ φ =>
    match As with
    | [] => (T.𝔼 π).map (P₁ (fp.fst _ _) (eval _ φ))
    | _ :: _ => (T.𝔼 π).map (eval _ φ)

  /- Syntax for (some) connectives -/
  infixr:10 "⊑" => Formula.impl
  infixr:80 "@" => Formula.app
  infixl:20 "⊓" => Formula.conj
  infixl:15 "⊔" => Formula.disj
  /- Basic "evaluates to true" syntax -/
  notation:30 As " ⊨ " f => ⊤ = Formula.eval As f

  open Lean Elab Command Term Meta

  syntax (name := letVars) "let_vars " ident,* " in " term : term
  syntax (name := letVarsI) "let_vars_i " term " | " ident,* " in " term : term

  @[term_elab letVarsI]
  def elabLetVarsI : TermElab := λ stx type? =>
    match stx with
    | `(let_vars_i $n | $x in $body) => do
      let stx ← `(let $x := Expr.var $n; $body)
      elabTerm stx type?
    | `(let_vars_i $n | $x,$xs,* in $body) => do
      let stx ← `(let $x := Expr.var $n; let_vars_i ($n+1) | $xs,* in $body)
      elabTerm stx type?
    | _ => throwUnsupportedSyntax

  @[term_elab letVars] def elabLetVars : TermElab := λ stx type? =>
    match stx with
  | `(let_vars $xs,* in $body) => do
    let stx ← `(let_vars_i 0 | $xs,* in $body)
    elabTerm stx type?
    | _ => throwUnsupportedSyntax

  declare_syntax_cat typing_judgement
  syntax ident " : " term : typing_judgement
  declare_syntax_cat context
  syntax "[" typing_judgement,* "]" : context
  syntax (name := tripos) context " ⊢ " term : term

  @[term_elab tripos] def elabTripos : TermElab := λ stx type? =>
    match stx with
    | `([ $[$x:ident : $X:term],* ] ⊢ $f:term) => do
      let stx ← `(let As := [$X,*]; let_vars $x,* in (As ⊨ $f))
      elabTerm stx type?
    | _ => throwUnsupportedSyntax

end Language
