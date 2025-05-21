import Mathlib
open FirstOrder
section order_definition

class order (X : Type) : Type where
  ord : (Fin 2 → X) → Prop

namespace order

variable {X : Type} [order X]

@[simp]
def lt (a b : X) [order X] : Prop :=
  ord (λ i => if i=0 then a else b)

infix:50 " <₀ " => lt
notation x " >₀ " y => y <₀ x

end order
end order_definition



class DLO (X : Type) extends order X where
  irrefl:   ∀x: X,     ¬(x<₀x)
  trans:    ∀x y z: X, x<₀y → y<₀z → x<₀z  --I changed this to be double implication, which Lean usually uses.
  total:    ∀x y: X,   x<₀y ∨ x=y ∨ y<₀x
  dense:    ∀x y: X,   x<₀y → ∃z: X, x<₀z ∧ z<₀y
  no_r_end: ∀x: X, ∃y: X, x<₀y
  no_l_end: ∀x: X, ∃w: X, w<₀x





 -- Section 3: Intervals

namespace DLO.interval

variable {X : Type} [DLO X]

@[simp]
def bounded (a b : X ): Set X :=
  { x:X | a<₀x ∧ x<₀b }

@[simp]
def lower (a : X): Set X :=
  { x:X | a<₀x }

@[simp]
def upper (b : X): Set X :=
  { x:X | x<₀b }

@[simp]
def singleton (a : X): Set X :=
  { x:X | x=a}


/--
This property expresses the fact that a subset of X is a finite union of intervals or singletons.
-/
inductive is_finite_union_of_intervalsP : Set X → Prop where
  | empty   : is_finite_union_of_intervalsP ∅
  -- | entire  : is_finite_union_of_intervalsP univ -- Not needed, logically follows from the others.
  | bounded : (a : X) → (b : X) → is_finite_union_of_intervalsP (bounded a b)
  | lower   : (a : X) → is_finite_union_of_intervalsP (lower a)
  | upper   : (a : X) → is_finite_union_of_intervalsP (upper a)
  | point   : (a : X) → is_finite_union_of_intervalsP (singleton a)
  | union   : ∀ U V : Set X, is_finite_union_of_intervalsP U → is_finite_union_of_intervalsP V → is_finite_union_of_intervalsP (U ∪ V)

end DLO.interval



section definability
open Set
open Language
@[simp]
def isDefinable {X : Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (Set.univ : Set X) L U

class Ominimal (X : Type) (L : Language) extends DLO X, Language.Structure L X  where
  definable_sets: ∀ (U: Set (X)), isDefinable L U  ↔ DLO.interval.is_finite_union_of_intervalsP U


--- Defining (ℝ ,<₀) as an Lstructure and trying to prove o-minimality
inductive ordsymbol : Type
| lt : ordsymbol

@[simp]
def order_language : Language where
   Functions := λ _ => Empty
   Relations := λ n => if n = 2 then ordsymbol else Empty


noncomputable section reals
namespace real_DLO
@[simp]
instance real_order : order ℝ where
  ord (f: Fin 2 → ℝ ) := f 0 < f 1


@[simp]
 instance Rstruc : Language.Structure order_language ℝ where
   funMap := λ empt => Empty.elim empt
   RelMap {n:ℕ }:= λ _ f =>
    match n with
    | 2 =>
      match f with
      | _ => real_order.ord f
    | _ => false


@[simp]
instance : DLO ℝ  where
  irrefl := by intros x h; exact lt_irrefl x h
  trans := by rintro x y z h1 h2; exact lt_trans h1 h2
  total := by intros x y; exact lt_trichotomy x y
  dense := by intros x y h; exact exists_between h
  no_r_end := by intro x; exact ⟨x + 1, by simp⟩
  no_l_end := by intro x; exact ⟨x - 1, by simp⟩

end real_DLO



--- Definition of all types:
/--
An `ImpAllFreeFormula`, short for `Implication_and_ForAll_free_formula`,
is a representation of some formula `φ` of a Language `L`, a Type `α` and a number of free variables `n`
written in such a way that it doesn't contain any → or ∀ symbols.
That is, it consists solely of:

  falsum, or falsehood.

  equality of terms.

  relations of terms.

  negation (¬) of other ImpAllFreeFormula.

  disjunction (or, ∨) of other ImpAllFreeFormula.

  conjunction (and, ∧) of other ImpAllFreeFormula.

  existentials (exists, ∃) of other ImpAllFreeFormula.

It should be noted that, in classical logic, every formula is equivalent to an ImpAllFreeFormula.
-/
inductive ImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n : ℕ} : ImpAllFreeFormula L α n
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  | not    {n : ℕ}   (f     : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | or     {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | and    {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | exists {n : ℕ}   (f : ImpAllFreeFormula L α (n + 1)) : ImpAllFreeFormula L α n

/--
An `QFImpAllFreeFormula`, short for `Quantiefier_and_Implication_and_ForAll_free_formula`,
is a squantifier-free formula `φ` of a Language `L`, a Type `α` and a number of free variables `n`
written in such a way that it doesn't contain any → symbols.
That is, it consists solely of:

  falsum, or falsehood.

  equality of terms.

  relations of terms.

  negation (¬) of other QFImpAllFreeFormula.

  disjunction (or, ∨) of other QFImpAllFreeFormula.

  conjunction (and, ∧) of other QFImpAllFreeFormula.

It should be noted that, in classical logic, every quantifier free formula is equivalent to a QFImpAllFreeFormula.
-/
inductive QFImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n : ℕ} : QFImpAllFreeFormula L α n
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  | not    {n : ℕ}   (f     : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n
  | or     {n : ℕ}   (f₁ f₂ : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n
  | and    {n : ℕ}   (f₁ f₂ : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n

/--
A Literal of a Language `L`, a Type `α`, and a number of free variables `n`
is a formula consisting solely of

  equality of terms

  relations of terms

  and lastly, negation of either of those
-/
inductive Literal (L : Language) (α : Type) (n : ℕ) : Type _
  | truth  : Literal L α n
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Literal L α n
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Literal L α n
  | not (f : Literal L α n) : Literal L α n

-- def Existblock (L : Language) (α : Type) (m : ℕ) := List (Literal L α m)
/--
An ExistBlock of a Language `L`, a Type `α`, and a number of free variables `m`
is a conjunction of literals with `m+1` free variables, with an imaginary "exist" in front, that is added during conversions.
-/
inductive Existblock (L : Language) (α : Type) (m : ℕ) : Type _
  | lit (l: Literal L α m) : Existblock L α m
  | and (l1 l2 : Existblock L α m)  : Existblock L α m

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
  | and    {n} (f1 f2 : Atomicblock L α n) : Atomicblock L α n

/--
A disjunction of atomicblock blocks of a Language `L`, a Type `α`, and a number of free variables `n`
is a number of atomic blocks connected with "or" `∨`.
-/
inductive disjunctionAtomicblocks (L : Language)  (α : Type) : ℕ → Type _
| atom  {m : ℕ} (a : Atomicblock L α m) : disjunctionAtomicblocks L α m
| or    {m : ℕ} (f1 f2 :disjunctionAtomicblocks L α m ) : disjunctionAtomicblocks L α m

/--
A Relblock of a Language `L`, a Type `α`, and a number of free variables `n`
is a formula consisting solely of

  truth

  falsum

  relations of terms

  and lastly, conjunctions (and) of two atomic blocks.
-/
inductive Relblock (L : Language) (α : Type) : ℕ → Type _
  | truth  {n}  :  Relblock L α n
  | falsum {n} : Relblock L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Relblock L α n
  | and    {n : ℕ} (f1 f2 : Relblock L α n) : Relblock L α n

/--
A disjunction of relblocks of a Language `L`, a Type `α`, and a number of free variables `n`
is a number of relblocks connected with "or" `∨`.
-/
inductive disjunctionRelblocks (L : Language)  (α : Type) : ℕ → Type _
| relb  {m:ℕ } (r: Relblock L α m): disjunctionRelblocks L α m
| or {m:ℕ } (f1 f2 :disjunctionRelblocks L α m ): disjunctionRelblocks L α m

inductive disjunctionExistblocks (L : Language)  (α : Type) : ℕ → Type _
| existbl  {m:ℕ } (r: Existblock L α m): disjunctionExistblocks L α m
| or {m:ℕ } (f1 f2 :disjunctionExistblocks L α m ): disjunctionExistblocks L α m

--- All inclusions of types:
section Inclusion_of_Types
/--
Sends a QFImpAllFreeFormula `φ` to their respective ImpAllFreeFormula by lifting the appropriate terms.
-/
def QFImpAllFreeFormula.toImpAllFreeFormula {L} {α} {n}: QFImpAllFreeFormula L α n→ ImpAllFreeFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => (f.toImpAllFreeFormula).not
  | .or  f₁ f₂   => (f₁.toImpAllFreeFormula).or  (f₂.toImpAllFreeFormula)
  | .and f₁ f₂   => (f₁.toImpAllFreeFormula).and (f₂.toImpAllFreeFormula)

/--
Sends a BoundedFormula `φ` to their ImpAllFreeFormula representation.
-/
def BoundedFormula.toImpAllFreeFormula {L : Language} {α : Type} {n : ℕ} : BoundedFormula L α n → ImpAllFreeFormula L α n
  | .falsum => .falsum
  | .equal t1 t2 => .equal t1 t2
  | .rel R ts => .rel R ts
  | .imp f₁ f₂ => ((BoundedFormula.toImpAllFreeFormula f₁).not).or (BoundedFormula.toImpAllFreeFormula f₂)
  | .all f => (((BoundedFormula.toImpAllFreeFormula f).not).exists).not

/--
Sends a Literal `φ` to their respective ImpAllFreeFormula by lifting the appropriate terms.
-/
def Literal.toImpAllFreeFormula {L} {α} {n} : Literal L α n → ImpAllFreeFormula L α n
  | truth => ImpAllFreeFormula.falsum.not
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => .not f.toImpAllFreeFormula

/--
Sends a Atomic Block `φ` to their respective ImpAllFreeFormula by lifting the appropriate terms.
-/
def Atomicblock.toImpAllFreeFormula {L} {α} {n} : (Atomicblock L α n) → ImpAllFreeFormula L α n
  | truth        => ImpAllFreeFormula.falsum.not
  | falsum       => ImpAllFreeFormula.falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel   R ts  => .rel R ts
  | .and   f₁ f₂ => f₁.toImpAllFreeFormula.and f₂.toImpAllFreeFormula

/--
Sends an AtomicBlock `a` to the disjunction of atomic blocks consisting solely of itself.
-/
def Atomicblock.todisjunctionAtomicblocks {m : ℕ}{L} {α} (a: Atomicblock L α m) :  disjunctionAtomicblocks L α m  :=
  disjunctionAtomicblocks.atom a

/--
Sends a RelBlock `φ` to their respective BoundedFormula by lifting the appropriate terms.
-/
def Relblock.toBoundedFormula {L} {α} {n}: Relblock L α n→ BoundedFormula L α n
  | truth => BoundedFormula.falsum.imp  BoundedFormula.falsum
  | falsum => BoundedFormula.falsum
  | rel R ts => .rel R ts
  | and t₁ t₂ => t₁.toBoundedFormula ⊓ t₂.toBoundedFormula
  -- | .and t1 t2 => (t1.toBoundedFormula.imp (t2.toBoundedFormula.imp BoundedFormula.falsum)).imp BoundedFormula.falsum

/--
Sends a disjunction of RelBlocks `φ` to their respective QFImpAllFreeFormula by lifting the appropriate terms.
-/
def disjunctionRelblocks.toBoundedFormula {L} {α} {n}: disjunctionRelblocks L α n → BoundedFormula L α n
  | relb r   => r.toBoundedFormula
  | or f₁ f₂ => f₁.toBoundedFormula ⊔ f₂.toBoundedFormula

/--
Sends a RelBlock `φ` to their respective QFImpAllFreeFormula by lifting the appropriate terms.
-/
def Relblock.toQFImpAllFreeFormula  {L} {α} {n} : Relblock L α n → QFImpAllFreeFormula L α n
 | truth     => QFImpAllFreeFormula.falsum.not
 | falsum    => .falsum
 | rel R ts  => .rel R ts
 | and f₁ f₂ => f₁.toQFImpAllFreeFormula.and f₂.toQFImpAllFreeFormula

/--
Sends a disjunction of RelBlocks `φ` to their respective QFImpAllFreeFormula by lifting the appropriate terms.
-/
def disjunctionRelblocks.toQFImpAllFreeFormula  {L} {α} {n} : disjunctionRelblocks L α n → QFImpAllFreeFormula L α n
  | relb r   => r.toQFImpAllFreeFormula
  | or f₁ f₂ => f₁.toQFImpAllFreeFormula.or f₂.toQFImpAllFreeFormula

/--
???
-/
def Relblock.toExistblock {L} {α} {n}: Relblock L α n → Existblock L α n
| truth => Existblock.lit Literal.truth
| falsum => Existblock.lit Literal.truth.not
| .rel R f => Existblock.lit (Literal.rel R f)
| .and t1 t2 => t1.toExistblock.and t2.toExistblock

/--
Sends an existblock `∃x [Lit₁, Lit₂, Lit₃, ...]` to the ImpAllFreeFormula
`Lit₁ ∧ Lit₂ ∧ Lit₃ ∧ Lit₄ ∧ ...`. Crucially, this does *not* add an ∃ in front of the
formula! For that, use `Existblock.toImpAllFreeFormula`.
-/
def Existblock.toImpAllFreeFormulaWithoutExists {L} {α} {n}: Existblock L α n → ImpAllFreeFormula L α n
  | .lit l => l.toImpAllFreeFormula -- Joos
  | .and l e => l.toImpAllFreeFormulaWithoutExists.and e.toImpAllFreeFormulaWithoutExists

/--
Sends an existblock `∃x [Lit₁, Lit₂, Lit₃, ...]` to the ImpAllFreeFormula
`∃x [Lit₁ ∧ Lit₂ ∧ Lit₃ ∧ Lit₄ ∧ ...]`.
-/
def Existblock.toImpAllFreeFormula {L} {α} {n}: Existblock L α (n + 1) → ImpAllFreeFormula L α n :=
  fun φ => ImpAllFreeFormula.exists (φ.toImpAllFreeFormulaWithoutExists) -- Origineel door Joos, overgenomen door Lily

/--
This lemma states that, for an existblock `eb`, calling `eb.toImpAllFreeFormulaWithoutExists` and then adding `.exists`
is the same as calling `eb.toImpAllFreeFormula`.
-/
@[simp]
lemma Existblock.toImpAllFreeFormula_equivalence {L} {α} {n} (eb : Existblock L α (n+1) ) : eb.toImpAllFreeFormula = eb.toImpAllFreeFormulaWithoutExists.exists :=
  rfl

/--
Sends ImpAllFreeFormula `φ` to their BoundedFormula representation.
-/
def ImpAllFreeFormula.toBoundedFormula {L} {α} {n} : ImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => (f.toBoundedFormula).not -- (f.toBounded).imp .falsum
  | .or  f₁ f₂   => f₁.toBoundedFormula ⊔ f₂.toBoundedFormula -- BoundedFormula.imp (f₁.toBoundedFormula.not) f₂.toBoundedFormula -- ((f₁.not).toBounded).imp f₂.toBounded
  | .and f₁ f₂   => f₁.toBoundedFormula ⊓ f₂.toBoundedFormula -- (BoundedFormula.imp f₁.toBoundedFormula f₂.toBoundedFormula.not).not -- ((f₁.not).or (f₂.not).not).toBounded
  | .exists f    => (f.toBoundedFormula).ex -- (((f.toBounded).not).all).not

/--
Sends an AtomicBlock `a` to their respective bounded formula.
-/
def Atomicblock.toBoundedFormula {L} {α} {n} : Atomicblock L α n → BoundedFormula L α n :=
  fun φ => φ.toImpAllFreeFormula.toBoundedFormula

-- Joos
/--
Sends QFImpAllFreeFormula `φ` to their BoundedFormula representation.
-/
def QFImpAllFreeFormula.toBoundedFormula {L} {α} {n}: QFImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum      => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts    => .rel R ts
  | .not f       => (f.toBoundedFormula).not -- (f.toBounded).imp .falsum
  | .or  f₁ f₂   => f₁.toBoundedFormula ⊔ f₂.toBoundedFormula -- BoundedFormula.imp (f₁.toBoundedFormula.not) f₂.toBoundedFormula -- ((f₁.not).toBounded).imp f₂.toBounded
  | .and f₁ f₂   => f₁.toBoundedFormula ⊓ f₂.toBoundedFormula -- (BoundedFormula.imp f₁.toBoundedFormula f₂.toBoundedFormula.not).not -- ((f₁.not).or (f₂.not).not).toBounded
-- disjunction and conjuction of disjunctionofatomicblocks

/--
For a QFImpAllFree Formula, there are two ways to convert it to a bounded formula;
either directly with `QFImpAllFreeFormula.toBoundedFormula`, or by first converting
it to an `ImpAllFreeFormula` and then a `BoundedFormula`.

This lemma states that both methods are the same.
-/
lemma QFImpAllFreeFormula.conversion_equivalence {L} {α} {n} (φ : QFImpAllFreeFormula L α n): φ.toImpAllFreeFormula.toBoundedFormula = φ.toBoundedFormula := by
  induction' φ
  repeat' rfl
  · dsimp!
    congr
  · dsimp!
    congr
  · dsimp!
    congr

end Inclusion_of_Types

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




/--
If not `n = 2` where `n` is a natural number, then
in the language `order_language[[ℝ]]`, the relations of arity `n`
are empty.
-/
lemma isEmpty_of_relationsOrderLanguageR_of_ne_2 {n : ℕ} (h : ¬n=2) : IsEmpty (order_language[[ℝ]].Relations n) := by
  have const_eq_empty: (constantsOn ℝ ).Relations n = Empty :=
    FirstOrder.Language.constantsOn_Relations ℝ n
  have rel_eq_empty:  order_language.Relations n = Empty := by
    simp
    intro ass
    contradiction
  have coerc : order_language[[ℝ]].Relations n = (order_language.Relations n ⊕ (constantsOn ℝ).Relations n) := by
    rfl
  rw [coerc]
  rw [const_eq_empty, rel_eq_empty]
  have isEmpty_of_Empty : IsEmpty Empty := Empty.instIsEmpty
  apply isEmpty_sum.mpr
  constructor
  · apply isEmpty_of_Empty
  · apply isEmpty_of_Empty

alias rel2empty := isEmpty_of_relationsOrderLanguageR_of_ne_2

/--
If not `n = 0` where `n` is a natural number, then
in the language `order_language[[ℝ]]`, the functions of arity `n`
are empty.
-/
lemma isEmpty_of_functionsOrderLanguageR_of_ne_0 {n : ℕ} (h : ¬n=0) : IsEmpty (order_language[[ℝ]].Functions n) := by
  have functions_eq_empty : order_language.Functions n = Empty := by
    simp
  have coerc : order_language[[ℝ]].Functions n = (order_language.Functions n ⊕ (constantsOn ℝ ).Functions n) := by
    rfl
  rw [coerc]
  rcases n with _ | k
  · exfalso
    trivial

  · have functions_is_empty : IsEmpty ((constantsOn ℝ ).Functions (k+1)) :=
      FirstOrder.Language.isEmpty_functions_constantsOn_succ
    rw [functions_eq_empty]
    apply isEmpty_sum.mpr
    constructor
    · have isEmpty_of_Empty : IsEmpty Empty := Empty.instIsEmpty
      apply isEmpty_of_Empty
    · apply functions_is_empty


def Literal.todisjunctionAtomicblocks {n:ℕ }(l : Literal (order_language[[ℝ]]) (Fin 1) n) : disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) n := by
  rcases l with ⟨ ⟩ | ⟨t1 ,t2⟩ | ⟨R, f⟩ | ⟨ ⟩ | ⟨t1, t2⟩ | ⟨R, f⟩ | f

  exact disjunctionAtomicblocks.atom (Atomicblock.truth)

  rcases t1 with ⟨a1 ⟩ | ⟨f, t1 ⟩
  rcases t2 with ⟨a2 ⟩  | ⟨g, t2⟩

  let QF :=  Atomicblock.equal (@Term.var  (order_language[[ℝ]]) (Fin 1 ⊕ Fin n) a1 ) (@Term.var  (order_language[[ℝ]]) ((Fin 1) ⊕ Fin n) a2)


  exact QF.todisjunctionAtomicblocks
  let ter := (@Term.var  (order_language[[ℝ]]) ((Fin 1) ⊕ Fin n) a1 )
  rename_i l
  by_cases neq : l=0
  rw [neq] at t2 g
  let const := Term.func g t2
  let QF:= Atomicblock.equal const ter
  exact QF.todisjunctionAtomicblocks

  have F_empty : IsEmpty (order_language[[ℝ]].Functions l)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
  apply F_empty.elim'
  apply g


  rename_i l


  by_cases neq : l=0
  rw [neq] at f t1
  let const1 := Term.func f t1
  let QF:= Atomicblock.equal const1 t2
  exact QF.todisjunctionAtomicblocks

  have F_empty : IsEmpty (order_language[[ℝ]].Functions l)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
  apply F_empty.elim'
  apply f

  let QF :=  Atomicblock.rel R f
  exact QF.todisjunctionAtomicblocks
  exact disjunctionAtomicblocks.atom (Atomicblock.falsum)
  let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (i:Fin 2)=>  if i=0 then t1 else t2  )
  let QF2 := Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (i:Fin 2)=> if i=0 then t2 else t1 )
  exact disjunctionAtomicblocks.or QF1.todisjunctionAtomicblocks QF2.todisjunctionAtomicblocks
  rename_i l
  by_cases neq: l=2
  let ter1:= f ⟨0, by linarith⟩
  let ter2 := f ⟨1, by linarith⟩
  let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (i:Fin 2)=>  if i=0 then ter2 else ter1  )
  let QF2 := Atomicblock.equal ter1 ter2
  exact disjunctionAtomicblocks.or QF1.todisjunctionAtomicblocks QF2.todisjunctionAtomicblocks
  exfalso
  have F_empty : IsEmpty (order_language[[ℝ]].Relations l)  := isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
  apply F_empty.elim'
  apply R


  exact f.todisjunctionAtomicblocks

def reindex{n} (i : Fin 1 ⊕ Fin (n+1)) : Fin 1 ⊕ Fin n  :=
 Sum.inl (match i with
  | Sum.inl x => x
  | Sum.inr x => x)



def varelimAtomicblock {n} (i: Fin 1 ⊕ Fin (n+1) ) (ter : order_language[[ℝ]].Term (Fin 1 ⊕ Fin n)): Atomicblock (order_language[[ℝ]]) (Fin 1) (n+1) →  Relblock (order_language[[ℝ]]) (Fin 1) n:= by
  intro rel
  rcases rel with ⟨ _⟩|  ⟨ _⟩|⟨t1,t2 ⟩ |  ⟨R,f ⟩ | ⟨t1,t2 ⟩

  exact Relblock.truth

  exact Relblock.falsum
  exact Relblock.truth


  rename_i l
  by_cases neq: l=2
  let t1:= f ⟨0, by linarith⟩
  let t2 := f ⟨1, by linarith⟩
  rcases t1 with ⟨a1 ⟩ | ⟨h, t_1 ⟩
  rcases t2 with ⟨a2 ⟩  | ⟨g, t_2⟩
  by_cases i=a1

  by_cases i=a2

  exact Relblock.falsum

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then ter else Term.var (reindex a2))

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else ter)
  rename_i p
  by_cases neq : p=0
  rw [neq] at g t_2

  by_cases ineqa : i=a1

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  ter else Term.func g (fun i: Fin 0=>  nomatch i))

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else Term.func g (fun i: Fin 0=>  nomatch i))

  have F_empty : IsEmpty (order_language[[ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
  apply F_empty.elim'
  apply g

  rename_i t
  by_cases neq2 : t=0
  rw [neq2] at h t_1
  rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩
  by_cases ineqa :i=a1
  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else ter)
  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex a1) )
  rename_i e
  by_cases neq2 : e=0
  rw [neq2] at g t_2
  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=>  nomatch i) )

  have F_empty : IsEmpty (order_language[[ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
  apply F_empty.elim'
  apply g

  have F_empty : IsEmpty (order_language[[ℝ]].Functions t)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
  apply F_empty.elim'
  apply h
  have F_empty : IsEmpty (order_language[[ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
  apply F_empty.elim'
  apply R


  exact (varelimAtomicblock i ter t1).and (varelimAtomicblock i ter t1)





def Atomicblock.toRelblock {n} : Atomicblock (order_language[[ℝ]]) (Fin 1) (n+1) → Relblock (order_language[[ℝ]]) (Fin 1) n
  | truth       => .truth
  | falsum      => .falsum
  | and f₁ f₂   => f₁.toRelblock.and f₂.toRelblock
  | equal t₁ t₂ => .truth --sorry --Originally it had "truth" but I don't know if that's right. Are you certain it's correct?

  | rel R ts    => by --I copied the original here.
    rename_i l
    by_cases neq: l=2
    · let t1 := ts ⟨0, by linarith⟩
      let t2 := ts ⟨1, by linarith⟩
      rcases t1 with ⟨a1 ⟩ | ⟨h, t_1 ⟩
      · rcases t2 with ⟨a2 ⟩  | ⟨g, t_2⟩
        exact Relblock.truth
        rename_i p
        by_cases neq : p=0
        rw [neq] at g t_2

        exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else Term.func g (fun i: Fin 0=>  nomatch i) )

        have F_empty : IsEmpty (order_language[[ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
        apply F_empty.elim'
        apply g

      · rename_i p
        by_cases neq : p=0
        · rw [neq] at h t_1

          rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩

          · exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex a1) )
          · rename_i e
            by_cases neq2 : e=0
            rw [neq2] at g t_2
            exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=> nomatch i) )

            have F_empty : IsEmpty (order_language[[ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
            apply F_empty.elim'
            apply g

        · have F_empty : IsEmpty (order_language[[ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
          apply F_empty.elim'
          apply h

    · have F_empty : IsEmpty (order_language[[ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
      apply F_empty.elim'
      apply R

  -- rcases block with ⟨ _⟩|⟨_ ⟩ | ⟨t1 ,t2⟩ | ⟨R, f⟩| ⟨ f⟩ |⟨ ⟩

  -- exact Relblock.truth

  -- exact Relblock.falsum
  -- exact Relblock.truth

  -- rename_i l
  -- by_cases neq: l=2
  -- let t1:= f ⟨0, by linarith⟩
  -- let t2 := f ⟨1, by linarith⟩
  -- rcases t1 with ⟨a1 ⟩ | ⟨h, t_1 ⟩
  -- rcases t2 with ⟨a2 ⟩  | ⟨g, t_2⟩
  -- exact Relblock.truth
  -- rename_i p
  -- by_cases neq : p=0
  -- rw [neq] at g t_2

  -- exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else Term.func g (fun i: Fin 0=>  nomatch i) )

  -- have F_empty : IsEmpty (order_language[[ℝ]].Functions p)  := func0empty neq
  -- apply F_empty.elim'
  -- apply g
  -- rename_i p
  -- by_cases neq : p=0
  -- rw [neq] at h t_1

  -- rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩

  -- exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex a1) )
  -- rename_i e
  -- by_cases neq2 : e=0
  -- rw [neq2] at g t_2
  -- exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=> nomatch i) )

  -- have F_empty : IsEmpty (order_language[[ℝ]].Functions e)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply g

  -- have F_empty : IsEmpty (order_language[[ℝ]].Functions p)  := func0empty neq
  -- apply F_empty.elim'
  -- apply h

  -- have F_empty : IsEmpty (order_language[[ℝ]].Relations l):= rel2empty neq
  -- apply F_empty.elim'
  -- apply R



  -- rename_i f
  -- exact f.toRelblock
  -- exact Relblock.falsum
  -- rename_i a t1 t2
  -- rcases t1 with ⟨i ⟩|  ⟨h,t_1 ⟩
  -- rcases t2 with ⟨j⟩|  ⟨g,t_2 ⟩

  -- exact (varelimAtomicblock i (Term.var (reindex j)) (a))
  -- rename_i l
  -- by_cases neq2 : l=0
  -- rw [neq2] at g t_2
  -- exact (varelimAtomicblock i (Term.func g (fun i: Fin 0=>  nomatch i)) (a))
  -- have F_empty : IsEmpty (order_language[[ℝ]].Functions l)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply g




  -- rename_i t
  -- by_cases neq2 : t=0
  -- rw [neq2] at h t_1
  -- rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩

  -- exact (varelimAtomicblock a1 (Term.func h (fun i: Fin 0=>  nomatch i)) (a))

  -- rename_i e
  -- by_cases neq2 : e=0
  -- rw [neq2] at g t_2
  -- by_cases h=g
  -- exact Relblock.truth
  -- exact Relblock.falsum


  -- have F_empty : IsEmpty (order_language[[ℝ]].Functions e)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply g
  -- have F_empty : IsEmpty (order_language[[ℝ]].Functions t)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply h

  -- rename_i a l R f
  -- exact (Atomicblock.rel R f).toRelblock.and a.toRelblock
  -- rename_i a1 a2 a3
  -- exact (a1.toRelblock.and a2.toRelblock).and a3.toRelblock


def Existblock.todisjunctionAtomicblocks {n : ℕ} : Existblock (order_language[[ℝ]]) (Fin 1) n → disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) n
  | lit l     => l.todisjunctionAtomicblocks
  | and e₁ e₂ => e₁.todisjunctionAtomicblocks.and e₂.todisjunctionAtomicblocks
  -- intro block
  -- rcases block with ⟨ l⟩ | ⟨l1, l2 ⟩
  -- exact l.todisjunctionAtomicblocks
  -- exact l1.todisjunctionAtomicblocks.and l2.todisjunctionAtomicblocks



def disjunctionAtomicblocks.todisjunctionRelblocks {n}:disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) (n+1)→ disjunctionRelblocks (order_language[[ℝ]]) (Fin 1) (n):= by
intro disA
rcases disA with ⟨atom ⟩ | ⟨d1, d2 ⟩
exact (disjunctionRelblocks.relb (Atomicblock.toRelblock atom))
exact disjunctionRelblocks.or (d1.todisjunctionRelblocks) (d2.todisjunctionRelblocks)

def Existblock.todisjunctionRelblocks {n}:Existblock (order_language[[ℝ]]) (Fin 1) (n+1)→ disjunctionRelblocks (order_language[[ℝ]]) (Fin 1) (n):= by
intro a
exact a.todisjunctionAtomicblocks.todisjunctionRelblocks








def Existblock.Realize {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Existblock L α (l + 1)) (v : α → M) (xs : Fin l → M) : Prop :=
  φ.toImpAllFreeFormula.toBoundedFormula.Realize v xs

@[simp]
lemma Existblock.Realize_equiv {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Existblock L α (l + 1)) (v : α → M) (xs : Fin l → M) : φ.Realize v xs ↔ φ.toImpAllFreeFormula.toBoundedFormula.Realize v xs := by
  rfl

def Relblock.Realize {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Relblock L α l) (v : α → M) (xs : Fin l → M) : Prop :=
  φ.toBoundedFormula.Realize v xs

@[simp]
lemma Relblock.Realize_equiv {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Relblock L α l) (v : α → M) (xs : Fin l → M) : φ.Realize v xs ↔ φ.toBoundedFormula.Realize v xs := by
  rfl

def disjunctionAtomicblocks.RealRealize (φ : disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) 1) (x: Fin 1 → ℝ ) : Prop :=
  φ.todisjunctionRelblocks.toBoundedFormula.Realize x (fun i : (Fin 0) => nomatch i)

@[simp]
lemma disjunctionAtomicblocks.RealRealize_equiv (φ : disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) 1) (x : Fin 1 → ℝ) : φ.RealRealize x ↔ φ.todisjunctionRelblocks.toBoundedFormula.Realize x (fun i : (Fin 0) => nomatch i) := by
  rfl


@[simp]
lemma compatible (eb: Existblock (order_language[[ℝ]]) (Fin 1) (1)) (x: Fin 1 → ℝ ) :
    eb.Realize x (fun i : (Fin 0) => nomatch i)
      ↔ @eb.todisjunctionAtomicblocks.todisjunctionRelblocks.toBoundedFormula.Realize (order_language[[ℝ]]) ℝ  _ _ _  x (fun i : Fin 0 => nomatch i) := by sorry


def disjunctionRelblocks.todisjunctionExistblocks {L} {α} {n}: disjunctionRelblocks L α n → disjunctionExistblocks L α n := by
  sorry

@[simp]
def disjunctionExistblocks.elim  {n:ℕ } : disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) (n):= by
  intro existbl
  rcases existbl with ⟨ ex⟩ | ⟨ex1,ex2⟩
  exact ex.todisjunctionRelblocks.todisjunctionExistblocks
  exact ex1.elim.or ex2.elim

def notExistblockelim {n : ℕ} : disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) (n):= by
  intro exbl
  rcases exbl with ⟨ exbl⟩ | ⟨ex1,ex2⟩

  rcases exbl with ⟨lit ⟩

  exact (disjunctionExistblocks.existbl (Existblock.lit lit )).elim
  rename_i ex1 ex2
  exact (notExistblockelim (disjunctionExistblocks.existbl ex1)).or (notExistblockelim (disjunctionExistblocks.existbl ex1))

  exact (notExistblockelim ex1).and (notExistblockelim ex2)



def disjunctionExistblocks.toQFImpAllFreeFormula  {L} {α} {n}: disjunctionExistblocks L α n→ QFImpAllFreeFormula L α n:= by
  sorry

def ImpAllFreeFormula.toQFImpAllFreeFormula  {n:ℕ } : ImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) (n) → QFImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) n:=
  let rec helper {n} : ImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) n →
      disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) n
    | .falsum => disjunctionExistblocks.existbl (Existblock.lit (Literal.truth.not))
    | .equal t1 t2 => disjunctionExistblocks.existbl (Existblock.lit (Literal.equal t1 t2))
    | .rel R f => disjunctionExistblocks.existbl (Existblock.lit (Literal.rel R f))
    | .and t1 t2=> (helper t1).and (helper t2)
    | .or t1 t2=> (helper t1).or (helper t2)
    | .not t => (helper t)
    | .exists φ  => match φ with
      | .falsum =>
          disjunctionExistblocks.existbl (Existblock.lit (Literal.truth.not))
      | .equal t1 t2 =>
          (disjunctionExistblocks.existbl (Existblock.lit (Literal.equal t1 t2))).elim
      | .rel R f =>
          (disjunctionExistblocks.existbl (Existblock.lit (Literal.rel R f))).elim
      | .not φ  =>
          notExistblockelim (helper  φ )
      | .or φ₁ φ₂ =>
          (helper φ₁).elim.or (helper φ₂).elim
      | .and φ₁ φ₂ =>
          ((helper φ₁).and (helper φ₂)).elim
      | .exists φ =>
          (helper φ).elim.elim

  fun φ =>
      match φ with
      | .falsum        => QFImpAllFreeFormula.falsum
      | .equal t1 t2   => QFImpAllFreeFormula.equal t1 t2
      | .rel R f       => QFImpAllFreeFormula.rel R f
      | .not φ         => φ.toQFImpAllFreeFormula.not
      | .or φ₁ φ₂      => φ₁.toQFImpAllFreeFormula.or φ₂.toQFImpAllFreeFormula
      | .and φ₁ φ₂     => φ₁.toQFImpAllFreeFormula.and φ₂.toQFImpAllFreeFormula
      | .exists φ      => (helper (.exists φ)).toQFImpAllFreeFormula





@[simp]
lemma compatible2 (φ : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 ) :
∀x:ℝ ,φ.Realize (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i)
 ↔ (QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)).Realize
    (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i) := by sorry -- Later



@[simp]
def Formulafiniteunion (ψ : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 ): Prop :=
 DLO.interval.is_finite_union_of_intervalsP
  ({x : ℝ | @ψ.Realize (order_language[[ℝ]]) ℝ  _ _ _  (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i)})

@[simp]
lemma QFimpAllFreeFormulafiniteunion (φ : QFImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) 0 ) :
    Formulafiniteunion φ.toBoundedFormula := by
  unfold Formulafiniteunion
  induction' φ with a b l R ts not_formula ih_not_formula or_left or_right orl_ih orr_ih and_left and_right andr_ih andl_ih
  · unfold QFImpAllFreeFormula.toBoundedFormula
    show DLO.interval.is_finite_union_of_intervalsP ∅
    exact DLO.interval.is_finite_union_of_intervalsP.empty

  · dsimp!
    by_cases h : Term.realize (Sum.elim (fun x_1 ↦ (0 : ℝ)) fun i ↦ nomatch i) a = Term.realize (Sum.elim (fun x_1 ↦ 0) fun i ↦ nomatch i) b
    · have is_entire : {x | @Term.realize (order_language[[ℝ]]) ℝ _ _ (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) a = Term.realize (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) b} = univ := by
        ext x
        constructor
        · intro h₁
          exact trivial
        · intro h
          clear h
          rw [Set.mem_setOf]
          sorry --!!! - Need assistance...

      rw [is_entire]
      have h : DLO.interval.is_finite_union_of_intervalsP (univ : Set ℝ) := by
        sorry -- Proven in the new documents.

      exact h

    · have is_empty : {x | @Term.realize (order_language[[ℝ]]) ℝ _ _ (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) a = Term.realize (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) b} = ∅ := by
        ext x
        constructor
        · intro h₁
          rw [Set.mem_setOf] at h₁
          exfalso
          apply h
          clear h
          sorry --!!! - Need assistance...
        · intro h₁
          exfalso
          exact h₁

      rw [is_empty]
      exact DLO.interval.is_finite_union_of_intervalsP.empty

  · unfold QFImpAllFreeFormula.toBoundedFormula

    by_cases h : l = 2
    · subst h
      let a := ts 0
      let b := ts 0
      -- have {x : ℝ} : (BoundedFormula.rel R ts).Realize (fun x_1 ↦ x) (fun i : Fin 0 ↦ nomatch i) ↔ a < b := by
        -- sorry
      simp!
      unfold Structure.RelMap
      sorry -- !!! - Need assistance...
    · exfalso
      have : IsEmpty (order_language[[ℝ]].Relations l) := by
        exact rel2empty h
      exact IsEmpty.false R


  · unfold QFImpAllFreeFormula.toBoundedFormula
    have this : {x : ℝ | (∼not_formula.toBoundedFormula).Realize (fun x_1 : Fin 1 ↦ x) fun i ↦ nomatch i} = {x | (not_formula.toBoundedFormula).Realize (fun x_1 ↦ x) fun i ↦ nomatch i}ᶜ := by
      exact rfl

    rw [this]
    have h {U} : DLO.interval.is_finite_union_of_intervalsP (U : Set ℝ) → DLO.interval.is_finite_union_of_intervalsP (Uᶜ : Set ℝ) := by
        sorry -- Proven in the new documents.

    apply h
    assumption


  · unfold QFImpAllFreeFormula.toBoundedFormula
    have this : {x : ℝ | (or_left.toBoundedFormula ⊔ or_right.toBoundedFormula).Realize (fun x_1 ↦ x) fun i ↦ nomatch i} =
                 {x | or_left.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} ∪ {x | or_right.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := by
      ext x
      rw [mem_union]
      repeat rw [mem_setOf]
      exact BoundedFormula.realize_sup

    rw [this]
    apply DLO.interval.is_finite_union_of_intervalsP.union
    assumption'


  · unfold QFImpAllFreeFormula.toBoundedFormula
    have this : {x : ℝ | (and_left.toBoundedFormula ⊓ and_right.toBoundedFormula).Realize (fun x_1 ↦ x) fun i ↦ nomatch i} =
                 {x | and_left.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} ∩ {x | and_right.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := by
      ext x
      rw [mem_inter_iff]
      repeat rw [mem_setOf]
      exact BoundedFormula.realize_inf

    rw [this]
    have h {U V} : DLO.interval.is_finite_union_of_intervalsP (U : Set ℝ) → DLO.interval.is_finite_union_of_intervalsP (V : Set ℝ) → DLO.interval.is_finite_union_of_intervalsP (U ∩ V : Set ℝ) := by
        sorry -- Sorry'd in the new documents.

    apply h
    assumption'
  -- Lily

@[simp]



-- Joos
lemma formulaequiv (φ ψ : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 ):
(∀ x:ℝ,  ψ.Realize (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i) ↔ φ.Realize (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i)) → (Formulafiniteunion φ ↔ Formulafiniteunion ψ) := by
  intro hyp
  unfold Formulafiniteunion at *

  have : {x | φ.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} =
         {x | ψ.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := ext (fun x ↦ (hyp x).symm)

  constructor
  · intro phi
    rw [← this]
    exact phi
  · intro psi
    rw [this]
    exact psi

def Formulaisbounded  (φ : Formula (order_language[[ℝ]]) (Fin 1)  ) : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 :=
  (by simp : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0  =Formula (order_language[[ℝ]]) (Fin 1)  ) ▸ φ


/--
Every set that is definable in the Language `(ℝ, <)` is a finite union of intervals.
-/
theorem definable_sets_left : ∀U : Set ℝ, isDefinable order_language U → DLO.interval.is_finite_union_of_intervalsP U := by
  intro U is_def_U
  rcases is_def_U with ⟨φ', set_eq⟩

  have langhom: order_language[[@univ ℝ]] = order_language[[ℝ]] := by
    sorry -- donderdag Johan
    -- Wat we *willen* is dat de formule `φ'` een `order_language[[ℝ]]` formule wordt.

  rw [langhom] at φ'
  expose_names
  -- have φ'_eq : φ' = φ'_1 := by
  --   sorry

  have set_eq_hom : (setOf φ'_1.Realize : Set (Fin 1 -> ℝ)) = setOf φ'.Realize := by
    sorry -- Eerst vragen over langhom.

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
        rw [<- set_eq_hom]
        apply set_eq.mp xf_in_setU

      rw [mem_setOf]
      rw [mem_setOf] at xf_in_setOf_φRealize
      exact (Formula.boundedFormula_realize_eq_realize φ (fun x_1 ↦ x) fun i ↦ nomatch i).mpr xf_in_setOf_φRealize

    · intro h
      show xf ∈ {x | x 0 ∈ U} --Suprised this works tbh. -Lily
      rw [mem_setOf] at h
      apply set_eq.mpr
      rw [set_eq_hom]
      rw [mem_setOf]
      exact (Formula.boundedFormula_realize_eq_realize φ (fun x_1 ↦ x) fun i ↦ nomatch i).mp h

  rw [seteq]
  exact φfin
