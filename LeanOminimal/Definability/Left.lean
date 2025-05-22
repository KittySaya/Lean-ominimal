import LeanOminimal.Definability.Definition
import LeanOminimal.intervals

open FirstOrder
open Language
open Set


namespace Definability

-- Docstring missing
def Formulaisbounded  (φ : Formula (order_language[[@univ ℝ]]) (Fin 1)  ) : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 :=
  (by simp : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 = Formula (order_language[[@univ ℝ]]) (Fin 1)) ▸ φ

/--
Every set that is definable in the Language `(ℝ, <)` is a finite union of intervals.
-/
theorem definable_sets_left : ∀U : Set ℝ, isDefinable order_language U → DLO.interval.is_finite_union_of_intervalsP U := by
  intro U is_def_U
  rcases is_def_U with ⟨φ', set_eq⟩

  let φ := Formulaisbounded φ'
  let ψ := QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)

  have ψfin : Formulafiniteunion ψ :=
      QFimpAllFreeFormulafiniteunion ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)


  have φfin : Formulafiniteunion φ :=
    ((formulaequiv ψ φ (compatible2 φ))).mp ψfin

  unfold Formulafiniteunion at φfin
  have seteq : U = {x : ℝ | φ.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := by
    ext x
    rw [Set.ext_iff] at set_eq
    let xf := fun _ : Fin 1 => x
    specialize set_eq xf
    constructor
    · intro h
      have xf_in_setU : xf ∈ {x | x 0 ∈ U} := by
        exact h
      have xf_in_setOf_φRealize : xf ∈ setOf φ'.Realize := by
        apply set_eq.mp xf_in_setU

      rw [mem_setOf]
      rw [mem_setOf] at xf_in_setOf_φRealize
      exact (Formula.boundedFormula_realize_eq_realize φ (fun x_1 ↦ x) fun i ↦ nomatch i).mpr xf_in_setOf_φRealize

    · intro h
      show xf ∈ {x | x 0 ∈ U} --Suprised this works tbh. -Lily
      rw [mem_setOf] at h
      apply set_eq.mpr
      rw [mem_setOf]
      exact (Formula.boundedFormula_realize_eq_realize φ (fun x_1 ↦ x) fun i ↦ nomatch i).mp h

  rw [seteq]
  exact φfin

end Definability
