import Triposes.Language

open Language
open CategoryTheory
open MonoidalCategory

universe u v
variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

/- Fix a tripos -/
variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

namespace PERdef
  syntax:70 fpterm "=[" term "]" fpterm:70 : fpformula
  local macro_rules
  | `($Γ:fpcontext ⊢ₕ $x:fpterm =[ $ρ:term ] $y:fpterm) => `($Γ:fpcontext ⊢ₕ ⟪ $ρ | ⟨$x, $y⟩ ⟫) --  =[]

  class PER (X : 𝒞) where
    rel : P₀ (P := P) (X ⊗ X)
    sym : a : X, b : X ⊢ ⟪rel | ⟨a, b⟩⟫ ⇒ ⟪rel | ⟨b, a⟩⟫
    trans : a : X, b : X, c : X ⊢ a =[rel] b ⊓ b =[rel] c ⇒ a =[rel] c
end PERdef
open PERdef

namespace Language
  syntax:70 fpterm "=" fpterm:70 : fpformula
  macro_rules
  | `($Γ:fpcontext ⊢ₕ $x:fpterm = $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪ PER.rel (X := _) | ⟨$x, $y⟩ ⟫)
  | `($Γ:fpcontext ⊢ₕ $x:fpterm =[ $ρ:term ] $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪ PER.rel (X := $ρ) | ⟨$x, $y⟩ ⟫)
end Language

namespace PERHomDef
  syntax:1025 term:1024 "⸨" fpterm "⸩ =" fpterm : fpformula
  local macro_rules
  | `($Γ:fpcontext ⊢ₕ $map:term ⸨ $x:fpterm ⸩ = $y:fpterm) => `($Γ:fpcontext ⊢ₕ ⟪$map | ⟨$x, $y⟩⟫)

  class PERHom (X Y : 𝒞) [ρX : PER (P := P) X] [ρY : PER (P := P) Y] where
    map : P₀ (P := P) (X ⊗ Y)
    congrDom : x : X, x' : X, y : Y ⊢ x = x'  ⊓ map⸨x'⸩ = y ⇒ map⸨x⸩ = y
    congrCod : x : X, y : Y, y' : Y ⊢ map⸨x⸩ = y ⊓ y = y'   ⇒ map⸨x⸩ = y'
    unique   : x : X, y : Y, y' : Y ⊢ map⸨x⸩ = y ⊓ map⸨x⸩ = y' ⇒ y = y'
    total    : x : X                ⊢ x = x ⇒ ∃ y : Y , map⸨x⸩ = y
end PERHomDef
open PERHomDef

namespace Language
  macro_rules
  | `($Γ:fpcontext ⊢ₕ $hom:term ⸨ $x:fpterm ⸩ = $y:fpterm) =>
    `($Γ:fpcontext ⊢ₕ ⟪ PERHom.map $hom | ⟨$x, $y⟩⟫)
end Language
