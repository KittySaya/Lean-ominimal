import LeanOminimal.Basic

open FirstOrder
open Language

namespace FirstOrder
namespace Language

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
inductive Implication_ForAll_free_formula (L : Language) (α : Type) : ℕ → Type _
  /--Falsum is always evaluatued as false.-/
  | falsum {n : ℕ}                                                            : Implication_ForAll_free_formula L α n
  /--Equality of two terms.-/
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n)))                          : Implication_ForAll_free_formula L α n
  /--Relations of terms-/
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Implication_ForAll_free_formula L α n
  /--negation (`¬`) of other Implication_ForAll_free_formula.-/
  | not    {n : ℕ}   (f     : Implication_ForAll_free_formula L α n)          : Implication_ForAll_free_formula L α n
  /--disjunction (or, `∨`) of other Implication_ForAll_free_formula.-/
  | or     {n : ℕ}   (f₁ f₂ : Implication_ForAll_free_formula L α n)          : Implication_ForAll_free_formula L α n
  /--conjunction (and, `∧`) of other Implication_ForAll_free_formula.-/
  | and    {n : ℕ}   (f₁ f₂ : Implication_ForAll_free_formula L α n)          : Implication_ForAll_free_formula L α n
  /--existentials (exists, `∃`) of other Implication_ForAll_free_formula.-/
  | exists {n : ℕ}   (f : Implication_ForAll_free_formula L α (n + 1))        : Implication_ForAll_free_formula L α n

alias ImpAllFreeFormula := Implication_ForAll_free_formula



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
inductive Quantiefier_Implication_free_formula (L : Language) (α : Type) : ℕ → Type _
  /--Falsum is always evaluatued as false.-/
  | falsum {n : ℕ}                                                            : Quantiefier_Implication_free_formula L α n
  /--Equality of two terms.-/
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n)))                          : Quantiefier_Implication_free_formula L α n
  /--Relations of terms-/
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Quantiefier_Implication_free_formula L α n
  /--negation (`¬`) of other Quantiefier_Implication_free_formula.-/
  | not    {n : ℕ}   (f     : Quantiefier_Implication_free_formula L α n)     : Quantiefier_Implication_free_formula L α n
  /--disjunction (or, `∨`) of other Quantiefier_Implication_free_formula.-/
  | or     {n : ℕ}   (f₁ f₂ : Quantiefier_Implication_free_formula L α n)     : Quantiefier_Implication_free_formula L α n
  /--conjunction (and, `∧`) of other Quantiefier_Implication_free_formula.-/
  | and    {n : ℕ}   (f₁ f₂ : Quantiefier_Implication_free_formula L α n)     : Quantiefier_Implication_free_formula L α n

alias QFImpAllFreeFormula := Quantiefier_Implication_free_formula



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



/--
An ExistBlock of a Language `L`, a Type `α`, and a number of free variables `m`
is a conjunction of literals with `m` free variables, with an imaginary "exist" in front, that is added during conversions.
-/
inductive Existblock (L : Language) (α : Type) (m : ℕ) : Type _
  | lit (l: Literal L α m)          : Existblock L α m
  | and (l1 l2 : Existblock L α m)  : Existblock L α m

alias ExistBlock := Existblock



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
