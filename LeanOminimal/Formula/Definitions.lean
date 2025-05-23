import LeanOminimal.Basic

open FirstOrder
open Language

namespace FirstOrder
namespace Language


section AllPurpose_Formulas
/--
An `Implication_ForAll_free_formula`, also known as a `ImpAllFreeFormula`,
is a representation of some formula `φ` of a Language `L`, a Type `α` and a number of free variables `n`
written in such a way that it doesn't contain any → or ∀ symbols.
That is, it consists solely of:

  falsum, or falsehood.

  equality of terms.

  relations of terms.

  negation (`¬`) of other Implication_ForAll_free_formula.

  disjunction (or, `∨`) of other Implication_ForAll_free_formula.

  conjunction (and, `∧`) of other Implication_ForAll_free_formula.

  existentials (exists, `∃`) of other Implication_ForAll_free_formula.

It should be noted that, in classical logic, every formula is equivalent to an Implication_ForAll_free_formula.
-/
inductive ImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  /--Falsum is always evaluatued as false.-/
  | falsum {n : ℕ}                                                            : ImpAllFreeFormula L α n
  /--Equality of two terms.-/
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n)))                          : ImpAllFreeFormula L α n
  /--Relations of terms-/
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  /--negation (`¬`) of other Implication_ForAll_free_formula.-/
  | not    {n : ℕ}   (f     : ImpAllFreeFormula L α n)                        : ImpAllFreeFormula L α n
  /--disjunction (or, `∨`) of other Implication_ForAll_free_formula.-/
  | or     {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n)                        : ImpAllFreeFormula L α n
  /--conjunction (and, `∧`) of other Implication_ForAll_free_formula.-/
  | and    {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n)                        : ImpAllFreeFormula L α n
  /--existentials (exists, `∃`) of other Implication_ForAll_free_formula.-/
  | exists {n : ℕ}   (f : ImpAllFreeFormula L α (n + 1))                      : ImpAllFreeFormula L α n

alias Implication_ForAll_free_formula := ImpAllFreeFormula

------------------------------------------------------

/--
A `Quantiefier_Implication_free_formula`, also known as a `QFImpAllFreeFormula`,
is a quantifier-free formula `φ` of a Language `L`, a Type `α` and a number of free variables `n`
written in such a way that it doesn't contain any → symbols.
That is, it consists solely of:

  falsum, or falsehood.

  equality of terms.

  relations of terms.

  negation (`¬`) of other Quantiefier_Implication_free_formula.

  disjunction (or, `∨`) of other Quantiefier_Implication_free_formula.

  conjunction (and, `∧`) of other Quantiefier_Implication_free_formula.

It should be noted that, in classical logic, every quantifier free formula is equivalent to a Quantiefier_Implication_free_formula.
-/
inductive QFImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  /--Falsum is always evaluatued as false.-/
  | falsum {n : ℕ}                                                            : QFImpAllFreeFormula L α n
  /--Equality of two terms.-/
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n)))                          : QFImpAllFreeFormula L α n
  /--Relations of terms-/
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  /--negation (`¬`) of other Quantiefier_Implication_free_formula.-/
  | not    {n : ℕ}   (f     : QFImpAllFreeFormula L α n)                      : QFImpAllFreeFormula L α n
  /--disjunction (or, `∨`) of other Quantiefier_Implication_free_formula.-/
  | or     {n : ℕ}   (f₁ f₂ : QFImpAllFreeFormula L α n)                      : QFImpAllFreeFormula L α n
  /--conjunction (and, `∧`) of other Quantiefier_Implication_free_formula.-/
  | and    {n : ℕ}   (f₁ f₂ : QFImpAllFreeFormula L α n)                      : QFImpAllFreeFormula L α n

alias Quantiefier_Implication_free_formula := QFImpAllFreeFormula

end AllPurpose_Formulas

------------------------------------------------------

section Specific_Formulas
/--
A Literal of a Language `L`, a Type `α`, and a number of free variables `n`
is a formula consisting solely of

  equality of terms

  relations of terms

  and lastly, negation of either of those
-/
inductive Literal (L : Language) (α : Type) (n : ℕ) : Type _
  | truth                                 : Literal L α n
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Literal L α n
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n)))
                                          : Literal L α n
  | not (f : Literal L α n)               : Literal L α n

------------------------------------------------------

section Existblock
/--
An ExistBlock of a Language `L`, a Type `α`, and a number of free variables `m`
is a conjunction of literals with `m` free variables, with an imaginary "exist" in front, that is added during conversions.
-/
inductive Existblock (L : Language) (α : Type) (m : ℕ) : Type _
  | lit (l: Literal L α m)          : Existblock L α m
  | and (l1 l2 : Existblock L α m)  : Existblock L α m

alias ExistBlock := Existblock

/--
A disjunction of existblock blocks of a Language `L`, a Type `α`, and a number of free variables `n`
is a number of exist blocks connected with "or" `∨`.
-/
inductive disjunctionExistblocks (L : Language) (α : Type) : ℕ → Type _
  | existbl {m : ℕ} (r: Existblock L α m)                  : disjunctionExistblocks L α m
  | or      {m : ℕ} (f₁ f₂ :disjunctionExistblocks L α m ) : disjunctionExistblocks L α m

alias disjunctionExistBlocks := disjunctionExistblocks

/--
Models the conjunction `∧` to work with `disjunctionExistblocks`,
using the distribution laws of and over or:
`σ ∧ (φ ∨ ψ) ↔ (σ ∧ φ) ∨ (σ ∧ ψ)` and
`(φ ∨ ψ) ∧ σ ↔ (φ ∧ σ) ∨ (ψ ∧ σ)`.
-/
def disjunctionExistblocks.and
    {L : Language} {α : Type} {n : ℕ}
    (f₁ f₂ : disjunctionExistblocks L α n) : disjunctionExistblocks L α n :=
  match f₁, f₂ with
  | existbl a₁, existbl a₂ => existbl (Existblock.and a₁ a₂)
  | existbl a₁, or b₁ b₂ =>
      or (disjunctionExistblocks.and (existbl a₁) b₁)
        (disjunctionExistblocks.and (existbl a₁) b₂)
  | or a₁ a₂, b =>
      or (disjunctionExistblocks.and a₁ b)
        (disjunctionExistblocks.and a₂ b)

end Existblock

------------------------------------------------------

section Atomicblock
/--
A Atomicblock of a Language `L`, a Type `α`, and a number of free variables `n`
is a formula consisting solely of

  truth

  falsum

  equality of terms

  relations of terms

  and lastly, conjunctions (and) of two atomic blocks.
-/
inductive Atomicblock (L : Language) (α : Type) : ℕ → Type _
  | truth  {n} :  Atomicblock L α n
  | falsum {n} : Atomicblock L α n
  | equal  {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Atomicblock L α n
  | rel    {n} {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Atomicblock L α n
  | and    {n} (f₁ f₂ : Atomicblock L α n) : Atomicblock L α n

/--
A disjunction of atomicblock blocks of a Language `L`, a Type `α`, and a number of free variables `n`
is a number of atomic blocks connected with "or" `∨`.
-/
inductive disjunctionAtomicblocks (L : Language)  (α : Type) : ℕ → Type _
| atom  {m : ℕ} (a : Atomicblock L α m) : disjunctionAtomicblocks L α m
| or    {m : ℕ} (f₁ f₂ :disjunctionAtomicblocks L α m ) : disjunctionAtomicblocks L α m

alias disjunctionAtomicBlocks := disjunctionAtomicblocks

/--
Models the conjunction `∧` to work with `disjunctionAtomicblocks`,
using the distribution laws of and over or:
`σ ∧ (φ ∨ ψ) ↔ (σ ∧ φ) ∨ (σ ∧ ψ)` and
`(φ ∨ ψ) ∧ σ ↔ (φ ∧ σ) ∨ (ψ ∧ σ)`.
-/
def disjunctionAtomicblocks.and
    {L : Language} {α : Type} {n : ℕ}
    (f₁ f₂ : disjunctionAtomicblocks L α n) : disjunctionAtomicblocks L α n :=
  match f₁, f₂ with
  | atom a₁, atom a₂ => atom (Atomicblock.and a₁ a₂)
  | atom a₁, or b₁ b₂ =>
      or (disjunctionAtomicblocks.and (atom a₁) b₁)
        (disjunctionAtomicblocks.and (atom a₁) b₂)
  | or a₁ a₂, b =>
      or (disjunctionAtomicblocks.and a₁ b)
        (disjunctionAtomicblocks.and a₂ b)

end Atomicblock

------------------------------------------------------

section Relblock
/--
A Relblock of a Language `L`, a Type `α`, and a number of free variables `n`
is a formula consisting solely of

  truth

  falsum

  relations of terms

  and lastly, conjunctions (and) of two atomic blocks.
-/
inductive Relblock (L : Language) (α : Type) : ℕ → Type _
  | truth  {n} : Relblock L α n
  | falsum {n} : Relblock L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Relblock L α n
  | and    {n   : ℕ} (f₁ f₂ : Relblock L α n) : Relblock L α n

alias RelBlock := Relblock



/--
A disjunction of relblocks of a Language `L`, a Type `α`, and a number of free variables `n`
is a number of relblocks connected with "or" `∨`.
-/
inductive disjunctionRelblocks (L : Language) (α : Type) : ℕ → Type _
  | relb {m : ℕ} (r: Relblock L α m) : disjunctionRelblocks L α m
  | or   {m : ℕ} (f₁ f₂ :disjunctionRelblocks L α m ) : disjunctionRelblocks L α m

alias disjunctionRelBlocks := disjunctionRelblocks

/--
Models the conjunction `∧` to work with `disjunctionRelblocks`,
using the distribution laws of and over or:
`σ ∧ (φ ∨ ψ) ↔ (σ ∧ φ) ∨ (σ ∧ ψ)` and
`(φ ∨ ψ) ∧ σ ↔ (φ ∧ σ) ∨ (ψ ∧ σ)`.
-/
def disjunctionRelblocks.and
    {L : Language} {α : Type} {n : ℕ}
    (f₁ f₂ : disjunctionRelblocks L α n) : disjunctionRelblocks L α n :=
  match f₁, f₂ with
  | relb a₁, relb a₂ => relb (Relblock.and a₁ a₂)
  | relb a₁, or b₁ b₂ =>
      or (disjunctionRelblocks.and (relb a₁) b₁)
        (disjunctionRelblocks.and (relb a₁) b₂)
  | or a₁ a₂, b =>
      or (disjunctionRelblocks.and a₁ b)
        (disjunctionRelblocks.and a₂ b)

end Relblock

------------------------------------------------------

end Specific_Formulas
