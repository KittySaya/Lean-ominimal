import LeanOminimal.Basic

open FirstOrder
open Language
open Set

namespace Definability

@[simp]
def isDefinable {X : Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U
