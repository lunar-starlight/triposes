import Triposes.Basic
import Triposes.Language.Basic

open CategoryTheory
open MonoidalCategory

open Language

section Algebra
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {As Bs Cs: 𝒞}
  variable {f g: As ⟶ Bs}
  variable (α β : Formula (P := P) As)
  variable {φ ψ : Formula (P := P) As}

  namespace Formula

    def conj_comm : α.conj β = β.conj α := by
      apply α.ind
      apply β.ind
      rintro α β
      unfold_quotient
      apply inf_comm

    def disj_comm : α.disj β = β.disj α := by
      apply α.ind
      apply β.ind
      rintro α β
      unfold_quotient
      apply sup_comm

  end Formula
end Algebra

section Map
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {γ : Formula (P := P) Cs}

  -- @[simp]
  -- theorem map_id {X : 𝒞} {x : P₀ (P := P) X} : Formula.app x (𝟙 X) = x := by
  --   unfold_quotient
  --   aesop_cat

  theorem map_comp_app : γ.app (f ≫ g) = (γ.app g).app f := by
    apply γ.ind
    rintro γ
    unfold_quotient
    aesop_cat

  instance : LE (Formula (P := P) As) := by
    constructor
    rintro φ ψ
    exact φ.eval ≤ ψ.eval

  -- macro_rules
  --   | `(tactic| unfold_quotient) =>
  --     `(tactic| apply Quot.sound; unfold Formula_Eq; unfold Formula'.eval; simp)
  syntax "unfold_quotient_le" : tactic
  syntax "full_eval" : tactic
  macro_rules
    | `(tactic| unfold_quotient_le) =>
      `(tactic| unfold LE.le; unfold instLEFormula; simp)
    | `(tactic| full_eval) =>
      `(tactic| repeat (first | unfold Formula.app | unfold Formula.impl | unfold Formula.conj | unfold Formula.disj | unfold Formula.all | unfold Formula.any))

end Map
namespace Any
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y} {z : P₀ (P := P) Z}
  variable {φ : Formula (P := P) X} {ψ : Formula (P := P) Y}
  variable {α : Formula (P := P) As} {β : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  lemma unit : α ≤ Formula.app (Formula.any f α) f := by
    unfold_quotient_le
    apply α.ind
    rintro α
    full_eval
    simp
    apply (T.𝔼 _).unit

  lemma counit : Formula.any f (Formula.app β f) ≤ β := by
    apply β.ind
    intros
    unfold_quotient_le
    full_eval
    simp
    apply (T.𝔼 _).counit

  lemma id_adj_id : Formula.any (𝟙 _) α = α := by
    apply α.ind
    rintro α
    full_eval
    simp
    apply Quot.sound
    unfold Formula_Eq
    conv => lhs; unfold Formula'.eval
    rw [(T.𝔼 _).id_adj_id]
    simp

  lemma frob_left : Formula.any f (α.conj (β.app f)) = (Formula.any f α).conj β := by
    apply α.ind
    apply β.ind
    rintro α β
    unfold_quotient
    conv => lhs; unfold Formula'.eval; enter [2, 2]; unfold Formula'.eval
    conv => enter [2, 1]; unfold Formula'.eval
    apply (T.𝔼 _).frob_left

  lemma frob_right : Formula.any f ((β.app f).conj α) = β.conj (Formula.any f α) := by
    rw [Formula.conj_comm, Formula.conj_comm β]
    exact frob_left

end Any

namespace All
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y} {z : P₀ (P := P) Z}
  variable {φ : Formula (P := P) X} {ψ : Formula (P := P) Y}
  variable {α : Formula (P := P) As} {β : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  lemma unit : β ≤ Formula.all f (Formula.app β f) := by
    unfold_quotient_le
    apply β.ind
    rintro β
    full_eval
    simp
    apply (T.𝔸 _).unit

  lemma counit : Formula.app (Formula.all f α) f ≤ α := by
    apply α.ind
    rintro α
    unfold_quotient_le
    full_eval
    simp
    apply (T.𝔸 _).counit

  lemma id_adj_id : Formula.all (𝟙 _) α = α := by
    apply α.ind
    rintro α
    full_eval
    simp
    apply Quot.sound
    unfold Formula_Eq
    conv => lhs; unfold Formula'.eval
    rw [(T.𝔸 _).id_adj_id]
    simp

  lemma top_eq_top : Formula.all f Formula.tru = Formula.tru (T := T) := by
    unfold_quotient
    unfold Formula'.eval
    apply (T.𝔸 _).top_eq_top

  -- lemma frob_left : Formula.all f (α.disj (β.app f)) = (Formula.all f α).disj β := by
  --   apply α.ind
  --   apply β.ind
  --   rintro α β
  --   unfold_quotient
  --   conv => lhs; unfold Formula'.eval; enter [2, 2]; unfold Formula'.eval
  --   conv => enter [2, 1]; unfold Formula'.eval
  --   apply (T.𝔸 _).frob_left

  -- lemma frob_right : Formula.all f ((β.app f).disj α) = β.disj (Formula.all f α) := by
  --   rw [Formula.disj_comm, Formula.disj_comm β]
  --   exact frob_left

end All

section Adjoints
  universe u v
  variable {𝒞 : Type u} [Category.{v, u} 𝒞]
  variable {P : 𝒞ᵒᵖ ⥤ HeytAlg} [T : Tripos P]

  variable {X Y Z As Bs Cs: 𝒞}
  variable {f : As ⟶ Bs} {g : Bs ⟶ Cs}
  variable {x : P₀ (P := P) X} {y : P₀ (P := P) Y} {z : P₀ (P := P) Z}
  variable {φ : Formula (P := P) X} {ψ : Formula (P := P) Y}
  variable {α : Formula (P := P) As} {β : Formula (P := P) Bs} {γ : Formula (P := P) Cs}

  lemma frobenius : Formula.all f (α.impl (Formula.app β f)) = (Formula.any f α).impl β := by
    apply α.ind
    apply β.ind
    intros
    unfold_quotient
    conv => lhs; unfold Formula'.eval; enter [2, 2]; unfold Formula'.eval
    conv => enter [2, 1]; unfold Formula'.eval
    apply T.frobenius

end Adjoints
