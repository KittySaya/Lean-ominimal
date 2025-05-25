import LeanOminimal.Definability.Definition
import LeanOminimal.intervals

open FirstOrder
open Language
open Set

namespace Definability

/--
The empty interval `∅` is definable.
-/
lemma isDefinable_emptyInterval : isDefinable order_language (∅ : Set ℝ) := by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]]) (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    @FirstOrder.Language.Term.equal _ (Fin 1) (constR 0) (constR 1)

  use φ
  ext x
  simp only [Fin.isValue, mem_empty_iff_false, setOf_false, order_language, top_eq_univ, Rstruc,
    ↓dreduceIte, real_order, Bool.false_eq_true, mem_setOf_eq, false_iff]
  by_contra h
  have zero_isnot_one : ¬((1 : ℝ) = 0) := by
    exact one_ne_zero
  apply zero_isnot_one
  exact Eq.symm ((fun {x} ↦ EReal.coe_eq_one.mp) (congrArg Real.toEReal h))


/--
The interval `(←, a)` is definable.
-/
lemma isDefinable_upperInterval (a : ℝ) : isDefinable order_language (DLO.interval.upper a):= by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]])  (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    Relations.formula (Sum.inl ordsymbol.lt) ![var, constR a]

  use φ
  ext x
  constructor
  · intro h
    apply h
  · intro h
    apply h


/--
The interval `(a, →)` is definable.
-/
lemma isDefinable_lowerInterval (b : ℝ) : isDefinable order_language (DLO.interval.lower b):= by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]])  (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    Relations.formula (Sum.inl ordsymbol.lt) ![constR b, var]

  use φ
  ext x
  constructor
  · intro h
    apply h
  · intro h
    apply h


/--
The interval `(a, b)` is definable.
-/
lemma isDefinable_boundInterval (a b : ℝ) : isDefinable order_language (DLO.interval.bounded a b) := by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable
  let var :=
    @Term.var (order_language[[univ (α := ℝ)]])  (Fin 1) 0

  let φ1 : order_language[[↑univ]].Formula (Fin 1) :=
    Relations.formula (Sum.inl ordsymbol.lt) (fun (n: Fin 2) => if n=0 then ( constR a ) else var)
  let φ2 : order_language[[↑univ]].Formula (Fin 1) :=
    Relations.formula (Sum.inl ordsymbol.lt) (fun (n: Fin 2) => if n=0 then var else ( constR b ))

  use φ1 ⊓ φ2
  ext x
  simp only [DLO.interval.bounded, order.lt, Real_DLO, real_order, Fin.isValue, ↓reduceIte, one_ne_zero,
    mem_setOf_eq, order_language, top_eq_univ, Rstruc, ↓dreduceIte, Bool.false_eq_true,
    Formula.realize_inf]

  constructor
  · simp
    intro h1 h2
    constructor
    · apply h1
    · apply h2
  · rintro ⟨h1, h2⟩
    constructor
    · apply h1
    · apply h2


/--
The interval `[a, a]` is definable.
-/
lemma isDefinable_singletonInterval (b : ℝ) : isDefinable order_language (singleton b):=  by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]])  (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    @FirstOrder.Language.Term.equal _ (Fin 1) var (constR b)

  use φ
  rfl


/--
The union of two definable intervals is definable.
-/
lemma isDefinable_unionInterval {X L} (U V : Set X) [DLO X] [Language.Structure L X] : isDefinable L U → isDefinable L V → isDefinable L (U ∪ V) := by
  simp
  unfold Definable₁
  unfold Definable
  intro U_definable
  intro V_definable
  rcases U_definable with ⟨φ, hφ⟩
  rcases V_definable with ⟨ψ, hψ⟩

  use φ ⊔ ψ

  ext x
  simp only [Fin.isValue, mem_union, mem_setOf_eq, Formula.realize_sup]
  constructor
  · apply Or.imp
    · intro x_in_U
      have x_in_phiset : x ∈ setOf φ.Realize := by
        rw [<- hφ]
        exact x_in_U
      exact x_in_phiset
    · intro x_in_V
      have x_in_psiset : x ∈ setOf ψ.Realize := by
        rw [<- hψ]
        exact x_in_V
      exact x_in_psiset

  · apply Or.imp
    · intro phi_realize_x
      have x_in_phiset : x ∈ setOf φ.Realize := by
        exact phi_realize_x
      rw [<- hφ] at x_in_phiset
      exact x_in_phiset
    · intro psi_realize_x
      have x_in_psiset : x ∈ setOf ψ.Realize := by
        exact psi_realize_x
      rw [<- hψ] at x_in_psiset
      exact x_in_psiset


/--
Every set of real numbers that is a finite union of intervals
is definable.
-/
theorem finite_unions_are_definable : ∀U : Set ℝ, DLO.interval.is_finite_union_of_intervalsP U → isDefinable order_language U := by
  intro U is_finite_union
  induction' is_finite_union with a b a b x A B _ _ A_ih B_ih
  · exact isDefinable_emptyInterval
  · exact isDefinable_boundInterval a b
  · exact isDefinable_lowerInterval a
  · exact isDefinable_upperInterval b
  · exact isDefinable_singletonInterval x
  · exact isDefinable_unionInterval A B A_ih B_ih

end Definability
