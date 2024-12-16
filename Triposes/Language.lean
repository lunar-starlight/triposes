import Triposes.Basic

open CategoryTheory
open MonoidalCategory


namespace Language

  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  /- Fix a tripos -/
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

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


  declare_syntax_cat heyt_expr
  syntax "⊤" : heyt_expr
  syntax "⊥" : heyt_expr
  syntax:50 heyt_expr "⊓" heyt_expr : heyt_expr
  syntax:40 heyt_expr "⊔" heyt_expr : heyt_expr
  syntax:30 heyt_expr "⇒" heyt_expr : heyt_expr
  syntax:60 "∀" typing_judgement "," heyt_expr : heyt_expr
  syntax:60 "∃" typing_judgement "," heyt_expr : heyt_expr
  syntax "(" heyt_expr ")" : heyt_expr
  syntax:1025 "[" term "]" fpterm : heyt_expr

  syntax:10 fpcontext "⊢" heyt_expr : term
  macro_rules
  | `([fpcontext| $[$key:ident : $value:term],* ]) =>
    let key := key.map (fun x => Lean.quote x.getId)
    `([$[($key, $value)],*].toAssocList')

  macro_rules
  | `($Γ:fpcontext ⊢ [$f:term] $t:fpterm) => `(P₁ ($Γ:fpcontext ⊢ₑ $t) $f)
  | `($Γ:fpcontext ⊢ $s:heyt_expr ⊓ $t:heyt_expr) => `(($Γ:fpcontext ⊢ $s) ⊓ ($Γ:fpcontext ⊢ $t))
  | `($Γ:fpcontext ⊢ $s:heyt_expr ⊔ $t:heyt_expr) => `(($Γ:fpcontext ⊢ $s) ⊔ ($Γ:fpcontext ⊢ $t))
  | `($Γ:fpcontext ⊢ $s:heyt_expr ⇒ $t:heyt_expr) => `(($Γ:fpcontext ⊢ $s) ⇨ ($Γ:fpcontext ⊢ $t))
  | `($_:fpcontext ⊢ ⊤) => `(⊤)
  | `($_:fpcontext ⊢ ⊥) => `(⊥)
  | `($[$jdgs],* ⊢ ∀ $y:ident : $Y:term , $t:heyt_expr) => `($y:ident : $Y:term , $jdgs,* ⊢ $t)
  | `($[$jdgs],* ⊢ ∃ $y:ident : $Y:term , $t:heyt_expr) => `($y:ident : $Y:term , $jdgs,* ⊢ $t)
  | `($Γ:fpcontext ⊢ ($t:heyt_expr)) => `($Γ:fpcontext ⊢ $t)

end Language
