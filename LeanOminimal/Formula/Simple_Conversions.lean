import LeanOminimal.Formula.Definitions

open FirstOrder
open Language
open Set

namespace FirstOrder
namespace Language


/--
Sends a BoundedFormula `φ` to their ImpAllFreeFormula representation.
-/
def BoundedFormula.toImpAllFreeFormula {L : Language} {α : Type} {n : ℕ} : BoundedFormula L α n → ImpAllFreeFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .imp f₁ f₂   => ((BoundedFormula.toImpAllFreeFormula f₁).not).or (BoundedFormula.toImpAllFreeFormula f₂)
  | .all f       => (((BoundedFormula.toImpAllFreeFormula f).not).exists).not

------------------------------------------------------

namespace ImpAllFreeFormula

/--
Sends ImpAllFreeFormula `φ` to their BoundedFormula representation.
-/
def toBoundedFormula {L} {α} {n} : ImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => (ImpAllFreeFormula.toBoundedFormula f).not
  | .or  f₁ f₂   => f₁.toBoundedFormula ⊔ f₂.toBoundedFormula
  | .and f₁ f₂   => f₁.toBoundedFormula ⊓ f₂.toBoundedFormula
  | .exists f    => (f.toBoundedFormula).ex

end ImpAllFreeFormula

------------------------------------------------------

namespace QFImpAllFreeFormula

/--
Sends a QFImpAllFreeFormula `φ` to their respective ImpAllFreeFormula by lifting the appropriate terms.
-/
def toImpAllFreeFormula {L} {α} {n}: QFImpAllFreeFormula L α n→ ImpAllFreeFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => (f.toImpAllFreeFormula).not
  | .or  f₁ f₂   => (f₁.toImpAllFreeFormula).or  (f₂.toImpAllFreeFormula)
  | .and f₁ f₂   => (f₁.toImpAllFreeFormula).and (f₂.toImpAllFreeFormula)

/--
Sends QFImpAllFreeFormula `φ` to their BoundedFormula representation.
-/
def toBoundedFormula {L} {α} {n}: QFImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => (f.toBoundedFormula).not
  | .or  f₁ f₂   => f₁.toBoundedFormula ⊔ f₂.toBoundedFormula
  | .and f₁ f₂   => f₁.toBoundedFormula ⊓ f₂.toBoundedFormula

/--
For a QFImpAllFree Formula, there are two ways to convert it to a bounded formula;
either directly with `QFImpAllFreeFormula.toBoundedFormula`, or by first converting
it to an `ImpAllFreeFormula` and then a `BoundedFormula`.

This lemma states that both methods are the same.
-/
lemma ImpAllFree_Bounded_conversion_equivalence {L} {α} {n} (φ : QFImpAllFreeFormula L α n): φ.toImpAllFreeFormula.toBoundedFormula = φ.toBoundedFormula := by
  induction' φ
  repeat' rfl
  · dsimp!
    congr
  · dsimp!
    congr
  · dsimp!
    congr

end QFImpAllFreeFormula

------------------------------------------------------

namespace Literal

/--
Sends a Literal `φ` to their respective ImpAllFreeFormula by lifting the appropriate terms.
-/
def toImpAllFreeFormula {L} {α} {n} : Literal L α n → ImpAllFreeFormula L α n
  | truth        => ImpAllFreeFormula.falsum.not
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => .not f.toImpAllFreeFormula

/--
Sends a Literal `φ` to their respective QFImpAllFreeFormula by lifting the appropriate terms.
-/
def toQFImpAllFreeFormula {L} {α} {n} : Literal L α n → QFImpAllFreeFormula L α n
  | truth => QFImpAllFreeFormula.falsum.not
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => .not f.toQFImpAllFreeFormula

/--
For a Literal, there are two ways to convert it to a ImpAllFree formula;
either directly with `Literal.toImpAllFreeFormula`, or by first converting
it to an `QFImpAllFreeFormula` and then a `toImpAllFreeFormula`.

This lemma states that both methods are the same.
-/
lemma conversion_equivalence {L} {α} {n} (lit : Literal L α n): lit.toQFImpAllFreeFormula.toImpAllFreeFormula = lit.toImpAllFreeFormula := by
  induction' lit
  repeat' rfl
  dsimp!
  congr

end Literal

------------------------------------------------------

namespace Existblock

-- !!! - Docstring missing (seems misplaced)
/--
Sends an existblock `∃x [Lit₁, Lit₂, Lit₃, ...]` to the ImpAllFreeFormula
`Lit₁ ∧ Lit₂ ∧ Lit₃ ∧ Lit₄ ∧ ...`. Crucially, this does *not* add an ∃ in front of the
formula! For that, use `Existblock.toImpAllFreeFormula`.
-/
def toQFImpAllFreeFormula {L} {α} {n}: Existblock L α (n ) → QFImpAllFreeFormula L α (n )
  | .lit l => l.toQFImpAllFreeFormula
  | .and l e => l.toQFImpAllFreeFormula.and e.toQFImpAllFreeFormula

/--
Sends an existblock `∃x [Lit₁, Lit₂, Lit₃, ...]` to the ImpAllFreeFormula
`∃x [Lit₁ ∧ Lit₂ ∧ Lit₃ ∧ Lit₄ ∧ ...]`.
-/
def toImpAllFreeFormula {L} {α} {n}: Existblock L α (n + 1) → ImpAllFreeFormula L α n :=
  fun φ => ImpAllFreeFormula.exists (φ.toQFImpAllFreeFormula.toImpAllFreeFormula)


/--
This lemma states that, for an existblock `eb`, calling `eb.toImpAllFreeFormulaWithoutExists` and then adding `.exists`
is the same as calling `eb.toImpAllFreeFormula`.
-/
@[simp]
lemma toImpAllFreeFormula_equivalence {L} {α} {n} (eb : Existblock L α (n+1)) : eb.toImpAllFreeFormula = eb.toQFImpAllFreeFormula.toImpAllFreeFormula.exists := rfl

end Existblock

------------------------------------------------------

namespace disjunctionExistblocks

/--
Sends an disjunction of existblocks recursively to a QFImpAllFreeFormula
-/
def toQFImpAllFreeFormula  {L} {α} {n}: disjunctionExistblocks L α n → QFImpAllFreeFormula L α n:= fun
  | .existbl r => r.toQFImpAllFreeFormula
  | .or f1 f2 => f1.toQFImpAllFreeFormula.or f2.toQFImpAllFreeFormula

end disjunctionExistblocks

------------------------------------------------------

namespace Atomicblock

/--
Sends an AtomicBlock `a` to the disjunction of atomic blocks consisting solely of itself.
-/
def todisjunctionAtomicblocks {m : ℕ} {L} {α} : Atomicblock L α m → disjunctionAtomicblocks L α m :=
  fun a => disjunctionAtomicblocks.atom a

/--
Sends a Atomic Block `φ` to their respective ImpAllFreeFormula by lifting the appropriate terms.
-/
def toImpAllFreeFormula {L} {α} {n} : (Atomicblock L α n) → ImpAllFreeFormula L α n
  | truth        => ImpAllFreeFormula.falsum.not
  | falsum       => ImpAllFreeFormula.falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel   R ts  => .rel R ts
  | .and   f₁ f₂ => f₁.toImpAllFreeFormula.and f₂.toImpAllFreeFormula

/--
Sends an AtomicBlock `a` to their respective bounded formula through an ImpAllFreeFormula.
-/
def toBoundedFormula {L} {α} {n} : Atomicblock L α n → BoundedFormula L α n :=
  fun φ => φ.toImpAllFreeFormula.toBoundedFormula

end Atomicblock

------------------------------------------------------

namespace disjunctionAtomicblocks

end disjunctionAtomicblocks

------------------------------------------------------

namespace Relblock

/--
Sends a RelBlock `φ` to their respective BoundedFormula by lifting the appropriate terms.
-/
def toBoundedFormula {L} {α} {n} : Relblock L α n → BoundedFormula L α n
  | truth => BoundedFormula.falsum.imp  BoundedFormula.falsum
  | falsum => BoundedFormula.falsum
  | rel R ts => .rel R ts
  | and t₁ t₂ => t₁.toBoundedFormula ⊓ t₂.toBoundedFormula

/--
Sends a RelBlock `φ` to their respective QFImpAllFreeFormula by lifting the appropriate terms.
-/
def toQFImpAllFreeFormula  {L} {α} {n} : Relblock L α n → QFImpAllFreeFormula L α n
  | truth     => QFImpAllFreeFormula.falsum.not
  | falsum    => .falsum
  | rel R ts  => .rel R ts
  | and f₁ f₂ => f₁.toQFImpAllFreeFormula.and f₂.toQFImpAllFreeFormula

/--
For a Relblock `R`, there are two ways to convert it to a bounded formula;
either directly with `QFImpAllFreeFormula.toBoundedFormula`, or by first converting
it to an `ImpAllFreeFormula` and then a `BoundedFormula`.

This lemma states that both methods are the same.
-/
lemma QFImpAllFree_Bounded_conversion_equivalence {L} {α} {n} (R : Relblock L α n): R.toQFImpAllFreeFormula.toBoundedFormula = R.toBoundedFormula := by
  induction' R
  repeat' rfl
  · dsimp!
    congr

-- !!! - Docstring missing
/--
???
-/
def toExistblock {L} {α} {n}: Relblock L α n → Existblock L α n
| truth      => Existblock.lit Literal.truth
| falsum     => Existblock.lit Literal.truth.not
| .rel R f   => Existblock.lit (Literal.rel R f)
| .and t₁ t₂ => t₁.toExistblock.and t₂.toExistblock


end Relblock

------------------------------------------------------

namespace disjunctionRelblocks

/--
Sends a disjunction of RelBlocks `φ` to their respective BoundedFormula by lifting the appropriate terms.
-/
def toBoundedFormula {L} {α} {n}: disjunctionRelblocks L α n → BoundedFormula L α n
  | relb r   => r.toBoundedFormula
  | or f₁ f₂ => f₁.toBoundedFormula ⊔ f₂.toBoundedFormula

/--
Sends a disjunction of RelBlocks `φ` to their respective QFImpAllFreeFormula by lifting the appropriate terms.
-/
def toQFImpAllFreeFormula  {L} {α} {n} : disjunctionRelblocks L α n → QFImpAllFreeFormula L α n
  | relb r   => r.toQFImpAllFreeFormula
  | or f₁ f₂ => f₁.toQFImpAllFreeFormula.or f₂.toQFImpAllFreeFormula

-- !!! - Docstring missing
def todisjunctionExistblocks {L} {α} {n}: disjunctionRelblocks L α n→ disjunctionExistblocks L α n
  | .relb r => disjunctionExistblocks.existbl r.toExistblock
  | .or f1 f2 =>  f1.todisjunctionExistblocks.or f2.todisjunctionExistblocks

/--
For a disjunction of Relblocks `Rs`, there are two ways to convert it to a bounded formula;
either directly with `QFImpAllFreeFormula.toBoundedFormula`, or by first converting
it to an `ImpAllFreeFormula` and then a `BoundedFormula`.

This lemma states that both methods are the same.
-/
lemma QFImpAllFree_Bounded_conversion_equivalence {L} {α} {n} (Rs : disjunctionRelblocks L α n): Rs.toQFImpAllFreeFormula.toBoundedFormula = Rs.toBoundedFormula := by
  induction' Rs with r f₁ f₂ f₁_ih f₂_ih
  · dsimp!
    exact Relblock.QFImpAllFree_Bounded_conversion_equivalence r
  · dsimp!
    congr

end disjunctionRelblocks

------------------------------------------------------
