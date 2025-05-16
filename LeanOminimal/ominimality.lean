import LeanOminimal.DLO
import LeanOminimal.Definability.Left
import LeanOminimal.Definability.Right

open FirstOrder
open Language
open Definability

class Ominimal (X : Type) (L : Language) extends DLO X, Language.Structure L X where
  definable_sets: ∀ (U: Set X), isDefinable L U  ↔ DLO.interval.is_finite_union_of_intervalsP U


theorem Real_definable_sets : ∀ (U: Set ℝ), isDefinable order_language U  ↔ DLO.interval.is_finite_union_of_intervalsP U := by
  intro U
  constructor
  · exact definable_sets_are_finite_unions U
  · exact finite_unions_are_definable U


/--
The master plan
-/
instance Real_Ominimal : Ominimal ℝ order_language where
  definable_sets := Real_definable_sets
