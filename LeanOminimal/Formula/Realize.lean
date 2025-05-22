import LeanOminimal.Formula.Simple_Conversions

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
