import LeanOminimal.Definability.Definition
import LeanOminimal.intervals

open FirstOrder
open Language
open Set


namespace Definability

lemma definable_sets_are_finite_unions : ∀U: Set ℝ, isDefinable order_language U → DLO.interval.is_finite_union_of_intervalsP U := by
  intro U U_definable
  rcases U_definable with ⟨φ, hφ⟩
  sorry

end Definability
