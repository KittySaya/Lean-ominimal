import LeanOminimal.DLO
import LeanOminimal.Definability
import LeanOminimal.Definability.Left
import LeanOminimal.Definability.Right

open FirstOrder
open Language
open Definability


/--
A type `X` with language `L` is Ominimal
if a set is definable
if and only if
it is a finite union of intervals.
-/
class Ominimal (X : Type) (L : Language) extends DLO X, Language.Structure L X where
  definable_sets: ∀ (U: Set X), isDefinable L U  ↔ DLO.interval.is_finite_union_of_intervalsP U


/--
In the model `(ℝ, <)`,
any set is definable
if and only if
it is a finite union of intervals.
-/
theorem Real_definable_sets : ∀ (U: Set ℝ), isDefinable order_language U  ↔ DLO.interval.is_finite_union_of_intervalsP U := by
  intro U
  constructor
  · exact definable_sets_are_finite_unions U
  · exact finite_unions_are_definable U


--The master plan
/--
The model `(ℝ, <)` is ominimal.
-/
instance Real_Ominimal : Ominimal ℝ order_language where
  definable_sets := Real_definable_sets
