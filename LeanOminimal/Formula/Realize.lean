import LeanOminimal.Formula.Complex_Conversions

open FirstOrder
open Language
open Set

namespace FirstOrder
namespace Language


/--
Adds a Realize to an existblock by simply mapping it to a bounded formula.
-/
def Existblock.Realize {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Existblock L α (l + 1)) (v : α → M) (xs : Fin l → M) : Prop :=
  φ.toImpAllFreeFormula.toBoundedFormula.Realize v xs


/--
Proves that the Realize of an existblock equals that of the realize by mapping it to a bounded formula.
-/
@[simp]
lemma Existblock.Realize_equiv {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Existblock L α (l + 1)) (v : α → M) (xs : Fin l → M) : φ.Realize v xs ↔ φ.toImpAllFreeFormula.toBoundedFormula.Realize v xs := by
  rfl


-- Docstring missing
def Relblock.Realize {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Relblock L α l) (v : α → M) (xs : Fin l → M) : Prop :=
  φ.toBoundedFormula.Realize v xs

-- Docstring missing
@[simp]
lemma Relblock.Realize_equiv {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Relblock L α l) (v : α → M) (xs : Fin l → M) : φ.Realize v xs ↔ φ.toBoundedFormula.Realize v xs := by
  rfl

-- Docstring missing
def disjunctionAtomicblocks.RealRealize (φ : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) 1) (x: Fin 1 → ℝ ) : Prop :=
  φ.todisjunctionRelblocks.toBoundedFormula.Realize x (fun i : (Fin 0) => nomatch i)

-- Docstring missing
@[simp]
lemma disjunctionAtomicblocks.RealRealize_equiv (φ : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) 1) (x : Fin 1 → ℝ) : φ.RealRealize x ↔ φ.todisjunctionRelblocks.toBoundedFormula.Realize x (fun i : (Fin 0) => nomatch i) := by
  rfl
