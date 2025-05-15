import LeanOminimal.DLO
import LeanOminimal.intervals
open FirstOrder
open Language
open Set

@[simp]
def isDefinable {X : Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U

class Ominimal (X : Type) (L : Language) extends DLO X, Language.Structure L X  where
  definable_sets: ∀ (U: Set (X)), isDefinable L U  ↔ DLO.interval.is_finite_union_of_intervalsP U

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
      | _ => real_order.ord f -- Why are we matching with something that only has one case?
    | _ => false


@[simp]
instance : DLO ℝ  where
  irrefl := by intros x h; exact lt_irrefl x h
  trans := by rintro x y z h1 h2; exact lt_trans h1 h2
  total := by intros x y; exact lt_trichotomy x y
  dense := by intros x y h; exact exists_between h
  no_r_end := by intro x; exact ⟨x + 1, by simp⟩
  no_l_end := by intro x; exact ⟨x - 1, by simp⟩


open FirstOrder.Language

@[simp]
def constantsOn_toFunctions0 {X : Type} (b : X) : (constantsOn X).Functions 0 :=
  (by simp : (constantsOn X).Functions 0 = X) ▸ b

def constterm {X : Type} (L : FirstOrder.Language) (b : X) : FirstOrder.Language.Term (L.withConstants X) (Fin 1) :=
  Term.func (Sum.inr (constantsOn_toFunctions0 b)) (λ i => nomatch i)

@[simp]
def constR  (b : ℝ ) : FirstOrder.Language.Term (order_language [[univ (α := ℝ)]]) (Fin 1) :=
 (Term.func (Sum.inr (constantsOn_toFunctions0 ⟨b, Set.mem_univ b⟩)) (λ i => nomatch i))




namespace definable

lemma emptyInterval : isDefinable order_language (∅ : Set ℝ):= by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]]) (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    @FirstOrder.Language.Term.equal _ (Fin 1) (constR 0) (constR 1)

  use φ
  ext x
  simp only [Fin.isValue, mem_empty_iff_false, setOf_false, order_language, top_eq_univ, real_DLO.Rstruc,
    ↓dreduceIte, real_DLO.real_order, Bool.false_eq_true, mem_setOf_eq, false_iff]
  by_contra h
  have zero_isnot_one : ¬((1 : ℝ) = 0) := by
    exact one_ne_zero
  apply zero_isnot_one
  exact Eq.symm ((fun {x} ↦ EReal.coe_eq_one.mp) (congrArg Real.toEReal h))


lemma upperInterval (a : ℝ) : isDefinable order_language (DLO.interval.upper a):= by
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


lemma lowerInterval (b : ℝ) : isDefinable order_language (DLO.interval.lower b):= by
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


lemma boundInterval (a b : ℝ) : isDefinable order_language (DLO.interval.bounded a b) := by
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
  simp only [DLO.interval.bounded, order.lt, real_DLO.instDLOReal, real_DLO.real_order, Fin.isValue, ↓reduceIte, one_ne_zero,
    mem_setOf_eq, order_language, top_eq_univ, real_DLO.Rstruc, ↓dreduceIte, Bool.false_eq_true,
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


lemma singletonInterval (b : ℝ) : isDefinable order_language (singleton b):=  by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]])  (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    @FirstOrder.Language.Term.equal _ (Fin 1) var (constR b)

  use φ
  rfl


lemma unionInterval {X L} (U V : Set X) [DLO X] [Language.Structure L X] : isDefinable L U → isDefinable L V → isDefinable L (U ∪ V) := by
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

end definable
open definable

theorem finite_unions_are_definable : ∀U : Set ℝ, DLO.interval.is_finite_union_of_intervalsP U → isDefinable order_language U := by
  intro U is_finite_union
  induction' is_finite_union with a b a b x A B _ _ A_ih B_ih
  · exact emptyInterval
  · exact boundInterval a b
  · exact lowerInterval a
  · exact upperInterval b
  · exact singletonInterval x
  · exact unionInterval A B A_ih B_ih

end real_DLO
end reals
