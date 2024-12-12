import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Monotone.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Types
import Mathlib.Order.Category.HeytAlg


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
  infix:90 "@" => Expr.app

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


    example (X Y Z : 𝒞) (f : X⊗Y ⟶ X⊗Y): X ⊗ (Y ⊗ Z) ⟶ (X ⊗ Y) ⊗ Z :=
      [X, Y, Z] ⊢ₑ ⟨ f @ ⟨ .var 0, .var 1 ⟩ , .var 2 ⟩

  end Proj

end ProjDSL

section Tripos

  /- We work over a cartesian closed category -/
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg}

  def P₀ {P : 𝒞ᵒᵖ ⥤ HeytAlg} := P.obj ∘ .op
  def P₁ {P : 𝒞ᵒᵖ ⥤ HeytAlg} {X Y : 𝒞} : (f : X ⟶ Y) → P₀ (P := P) Y ⟶ P₀ (P := P) X := P.map ∘ .op

  class HasExists {X Y : 𝒞} (f : X ⟶ Y) where
    map : P₀ (P := P) X ⟶ P₀ Y
    adjTo   : ∀ {x : P₀ X} {y : P₀ Y}, (map x ≤ y) → (x ≤ P₁ f y)
    adjFrom : ∀ {x : P₀ X} {y : P₀ Y}, (x ≤ P₁ f y) → (map x ≤ y)

  class HasForall {X Y : 𝒞} (f : X ⟶ Y) where
    map : P₀ (P := P) X ⟶ P₀ Y
    adjTo   : ∀ {y : P₀ Y} {x : P₀ X}, (P₁ f y ≤ x) → (y ≤ map x )
    adjFrom : ∀ {y : P₀ Y} {x : P₀ X}, (y ≤ map x) → (P₁ f y ≤ x)

  class HasGeneric where
    𝕊 : 𝒞
    σ : P₀ (P := P) 𝕊
    bracket : ∀ {X : 𝒞} (_ : P₀ X), X ⟶ 𝕊
    σIsGeneric : ∀ {X : 𝒞} (φ : P₀ X), φ = P₁ (bracket φ) σ

  class Tripos (P : 𝒞ᵒᵖ ⥤ HeytAlg) where
    𝔼 : ∀ {X Y : 𝒞} (f : X ⟶ Y), HasExists (P := P) f
    𝔸 : ∀ {X Y : 𝒞} (f : X ⟶ Y), HasForall (P := P) f

    BeckChevalley : ∀ {X Y Z W : 𝒞} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W), IsPullback f g h k → (𝔸 f).map ∘ P₁ g = P₁ h ∘ (𝔸 k).map

  def π {X Y : 𝒞} : X ⊗ Y ⟶ Y := fp.snd _ _
  -- def 𝔸π [T : Tripos P] {X Y : 𝒞} : HasForall (X := X ⊗ Y) (Y := Y) (P := P) π := T.𝔸 π

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

  def Formula.eval (As : List 𝒞) [T : Tripos P] : Formula (P := P) As → P₀ (P := P) (listProd As)
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

  notation:30 As " ⊢ " f => ⊤ = Formula.eval As f

  section Syntax
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
        -- let nExpr : Expr ← elabTermEnsuringType n (mkConst `Nat)
        -- let nlit := nExpr.natLit!
        let stx ← `(let $x := Expr.var $n; let_vars_i ($n+1) | $xs,* in $body)
        elabTerm stx type?
      | `(let_vars_i $_ | in $body) => elabTerm body type?
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
    syntax (name := tripos) context " ⊨ " term : term
    -- macro_rules
    -- | `([ $[$x:ident : $X:term],* ] ⊨ $f:term) =>
    --   `(let_vars $x,* in let As := [$X,*]; let f := $f; ⊤ = Formula.eval As f)

    @[term_elab tripos] def elabTripos : TermElab := λ stx type? =>
      match stx with
      | `([ $[$x:ident : $X:term],* ] ⊨ $f:term) => do
        let stx ← `(let As := [$X,*]; let_vars $x,* in (⊤ = Formula.eval As $f))
        elabTerm stx type?
      | _ => throwUnsupportedSyntax

    infixr:10 "⊑" => Formula.impl
    infixr:80 "@" => Formula.app
    infixl:20 "⊓" => Formula.conj
    infixl:15 "⊔" => Formula.disj

    -- variable {X Y : 𝒞} [T : Tripos P]
    -- #check [a : X, b : X] ⊨ ((⟦a =[rel] b⟧) ⊑ (⟦b =[rel] a⟧))
  end Syntax

  -- notation:70 "a" => Expr.var 0
  -- notation:70 "b" => Expr.var 1
  -- notation:70 "c" => Expr.var 2
  -- def a {As : List 𝒞} {A : 𝒞} : Expr (A :: As) A := Expr.var 0
  -- def b {As : List 𝒞} {A B : 𝒞} : Expr (A :: B :: As) B := Expr.var 1
  -- def c {As : List 𝒞} {A B C : 𝒞} : Expr (A :: B :: C :: As) C := Expr.var 2

  notation:70 "⟦" x "=[" ρ "]" y "⟧" => (ρ @ ⟨x, y⟩) -- ⟦ =[] ⟧
  notation:5505555 "⟦" map "(" x ") =" y "⟧" => (map @ ⟨x, y⟩) -- ⟦() = ⟧

  -- #check

  class PER [T : Tripos P] (X : 𝒞) [fp : ChosenFiniteProducts 𝒞] where
    rel : P₀ (P := P) (X ⊗ X)
    -- sym : [a : X, b : X] ⊨ Formula.app rel (⟨a, b⟩)
    sym : [a : X, b : X] ⊨ ⟦a =[rel] b⟧ ⊑ ⟦b =[rel] a⟧
    -- sym : [X, X] ⊢ ⟦a =[rel] b⟧ ⊑ ⟦b =[rel] a⟧
    trans : [a : X, b : X, c : X] ⊨ ⟦a =[rel] b⟧ ⊓ ⟦b =[rel] c⟧ ⊑ ⟦a =[rel] c⟧
    -- trans : [X, X, X] ⊢ ⟦a =[rel] b⟧ ⊓ ⟦b =[rel] c⟧ ⊑ ⟦a =[rel] c⟧

  -- def x {As : List 𝒞} {A : 𝒞} : Expr (A :: As) A := Expr.var 0
  -- def x' {As : List 𝒞} {A B : 𝒞} : Expr (A :: B :: As) B := Expr.var 1
  -- def y {As : List 𝒞} {A B : 𝒞} : Expr (A :: B :: As) B := Expr.var 1
  -- def y' {As : List 𝒞} {A B C : 𝒞} : Expr (A :: B :: C :: As) C := Expr.var 2
  -- variable [T : Tripos P] {X : 𝒞} (ρX : PER (T := T) X)

  -- #reduce [X, X, X] ⊢ ⟦x =[ρX.rel] x'⟧ ⊓ ⟦x =[ρX.rel] y'⟧

  -- class PERHom [T : Tripos P] {X Y : 𝒞} (ρX : PER (T := T) X) (ρY : PER (T := T) Y) where
  --   map : P₀ (P := P) (X ⊗ Y)
  --   congrDom : [X, X, Y] ⊢ ⟦x =[ρX.rel] x'⟧ ⊓ ⟦map[x'] = y'⟧ ⊑ ⟦map[x] = y'⟧
  --   congrCod : [X, Y, Y] ⊢ ⟦map[x] = y⟧ ⊓ ⟦y =[ρY.rel] y'⟧ ⊑ ⟦map[x] = y'⟧
  --   unique   : [X, Y, Y] ⊢ ⟦map[x] = y⟧ ⊓ ⟦map[x] = y'⟧ ⊑ ⟦y =[ρY.rel] y'⟧
  --   total    : [X]       ⊢ ⟦x =[ρX.rel] x⟧ ⊑ .any Y ⟦map[b] = a⟧ -- this is [x = x] ⊑ ∃_y [fx = y], so b = x and a = y
  class PERHom [T : Tripos P] {X Y : 𝒞} (ρX : PER (T := T) X) (ρY : PER (T := T) Y) where
    map : P₀ (P := P) (X ⊗ Y)
    -- congrDom : [X, X, Y] ⊢ ⟦x =[ρX.rel] x'⟧ ⊓ ⟦map(x') = y'⟧ ⊑ ⟦map(x) = y'⟧
    -- congrCod : [X, Y, Y] ⊢ ⟦map(x) = y⟧ ⊓ ⟦y =[ρY.rel] y'⟧ ⊑ ⟦map(x) = y'⟧
    -- unique   : [X, Y, Y] ⊢ ⟦map(x) = y⟧ ⊓ ⟦map(x) = y'⟧ ⊑ ⟦y =[ρY.rel] y'⟧
    -- total    : [X]       ⊢ ⟦x =[ρX.rel] x⟧ ⊑ .any Y ⟦map(b) = a⟧ -- this is [x = x] ⊑ ∃_y [fx = y], so b = x and a = y
    congrDom : [x : X, x' : X, y : Y] ⊨ ⟦x =[ρX.rel] x'⟧ ⊓ ⟦map(x') = y⟧ ⊑ ⟦map(x) = y⟧
    congrCod : [x : X, y : Y, y' : Y] ⊨ ⟦map(x) = y⟧ ⊓ ⟦y =[ρY.rel] y'⟧ ⊑ ⟦map(x) = y'⟧
    unique   : [x : X, y : Y, y' : Y] ⊨ ⟦map(x) = y⟧ ⊓ ⟦map(x) = y'⟧ ⊑ ⟦y =[ρY.rel] y'⟧
    total    : [x : X]                ⊨ ⟦x =[ρX.rel] x⟧ ⊑ .any Y ⟦map(.var 1) = .var 0⟧ -- this is [x = x] ⊑ ∃_y [fx = y]
