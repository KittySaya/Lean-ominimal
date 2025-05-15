import LeanOminimal.DLO
import LeanOminimal.definability

open FirstOrder
open Language

class Ominimal (X : Type) (L : Language) extends DLO X, Language.Structure L X  where
  definable_sets: ∀ (U: Set (X)), isDefinable L U  ↔ DLO.interval.is_finite_union_of_intervalsP U

/--
The master plan
-/
instance Real_Ominimal : Ominimal ℝ order_language where
  definable_sets := by sorry
