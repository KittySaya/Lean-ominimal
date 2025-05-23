import LeanOminimal.Basic

open FirstOrder
open Language
open Set

namespace Definability

/--
A set `U` of type `X` in language `L` is definable if there
exists some bounded formula `φ` in the language `L` with constants
of `X` such that `U` is the set of all `X` satisfying `φ`.
-/
@[simp]
def isDefinable {X : Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U
