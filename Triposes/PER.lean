import Triposes.Language

open Language
open CategoryTheory
open MonoidalCategory

universe u v
variable {𝒞 : Type u} [Category.{v, u} 𝒞] [fp : ChosenFiniteProducts 𝒞] [ccc : CartesianClosed 𝒞]

/- Fix a tripos -/
variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

namespace PERdef
  local notation:70 "⟦" x "=[" ρ "]" y "⟧" => (Formula.app ρ (⟨x, y⟩)) -- ⟦ =[] ⟧

  class PER [T : Tripos P] (X : 𝒞) where
    rel : P₀ (P := P) (X ⊗ X)
    sym : [a : X, b : X] ⊢ ⟦a =[rel] b⟧ ⊑ ⟦b =[rel] a⟧
    trans : [a : X, b : X, c : X] ⊢ ⟦a =[rel] b⟧ ⊓ ⟦b =[rel] c⟧ ⊑ ⟦a =[rel] c⟧
end PERdef
open PERdef

namespace Language
  notation:70 "⟦" x "=[" ρ "]" y "⟧" => (Formula.app (PER.rel (X := ρ)) (⟨x, y⟩)) -- ⟦ =[] ⟧
end Language

namespace PERHomDef
  local notation:1025 "⟦" map "(" x ") =" y "⟧" => (Formula.app map (⟨x, y⟩)) -- ⟦() = ⟧
  class PERHom [T : Tripos P] (X Y : 𝒞) [ρX : PER (T := T) X] [ρY : PER (T := T) Y] where
    map : P₀ (P := P) (X ⊗ Y)
    congrDom : [x : X, x' : X, y : Y] ⊢ ⟦x =[X] x'⟧ ⊓ ⟦map(x') = y⟧ ⊑ ⟦map(x) = y⟧
    congrCod : [x : X, y : Y, y' : Y] ⊢ ⟦map(x) = y⟧ ⊓ ⟦y =[Y] y'⟧ ⊑ ⟦map(x) = y'⟧
    unique   : [x : X, y : Y, y' : Y] ⊢ ⟦map(x) = y⟧ ⊓ ⟦map(x) = y'⟧ ⊑ ⟦y =[Y] y'⟧
    total    : [x : X]                ⊢ ⟦x =[X] x⟧ ⊑ .any Y ⟦map(.var 1) = .var 0⟧ -- this is [x = x] ⊑ ∃_y [fx = y]
end PERHomDef
open PERHomDef

namespace Language
  notation:1025 "⟦" ρ "(" x ") =" y "⟧" => Formula.app (PERHom.map ρ) (⟨x, y⟩) -- ⟦() = ⟧
end Language
