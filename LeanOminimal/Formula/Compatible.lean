import LeanOminimal.Formula.Complex_Conversions
import LeanOminimal.Formula.Realize

open FirstOrder
open Language
open Set

namespace FirstOrder
namespace Language


/--
Helper lemma to that shows that eliminating an exist from an existblock is compatible with .Realize of Mathlib.
That is, the formulas are equivalent.
-/
@[simp]
lemma compatible_1 (eb: Existblock (order_language[[@univ ℝ]]) (Fin 1) (1)) (x: Fin 1 → ℝ ) :
    eb.Realize x (fun i : (Fin 0) => nomatch i)
      ↔ @eb.elim.toBoundedFormula.Realize (order_language[[@univ ℝ]]) ℝ  _ _ _  x (fun i : Fin 0 => nomatch i) := by sorry



/--
Important lemma that shows compatibility with .Realize of the function eliminating exists from every possible Boundedformula.
-/
@[simp]
lemma compatible₂ (φ : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 ) :
    ∀x:ℝ ,φ.Realize (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i)
     ↔ (QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)).Realize
        (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i) := by
  sorry
