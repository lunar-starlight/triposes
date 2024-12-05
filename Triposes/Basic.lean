import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Category.HeytAlg
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

universe u v₁ v₂

variable {C : Type u}

section Defn

class Tripos [CCat : CategoryTheory.Category.{v₁} C] : Type (max u v₁ v₂ + 1) where
  P : CategoryTheory.Functor C HeytAlg.{v₂}
  --𝔼 : ∀ {A B : CCat.obj} (f : CCat.Hom A B) (a : A)
  --𝔸 :

end Defn
