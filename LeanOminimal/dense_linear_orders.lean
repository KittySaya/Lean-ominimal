import Mathlib

open Set
open FirstOrder


-- What does this do?
def funcomb {n : ℕ} {m : ℕ} {X : Type} (f: Fin n → X) (b: Fin m → X): Fin (n+m) → X :=
  fun (k: Fin (n+m)) =>
    if  hk: (k.val: ℕ) < n then f ⟨k, hk⟩
    else b ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Fin.is_lt k)⟩


-- Step 10: Defining the dense linear order (DLO)
section DLO_definition

class order (X : Type) where
  ord : (Fin 2 → X) → Prop

namespace order
variable {X : Type} [order X]

@[simp]
def lt (a b : X) [order X] : Prop :=
  ord (λ i => if i=0 then a else b)
end order

infix:50 " <₀ " => order.lt
notation x " >₀ " y => y <₀ x

class DLO (X:Type) extends order X where
  irrefl:   ∀x: X,     ¬(x<₀x)
  trans:    ∀x y z: X, x<₀y → y<₀z → x<₀z  --I changed this to be double implication, which Lean usually uses.
  total:    ∀x y: X,   x<₀y ∨ x=y ∨ y<₀x
  dense:    ∀x y: X,   x<₀y → ∃z: X, x<₀z ∧ z<₀y
  no_r_end: ∀x: X, ∃y: X, x<₀y
  no_l_end: ∀x: X, ∃w: X, w<₀x

namespace DLO

-- Every dense linear order is asymetric.
@[simp]
lemma asymm {X : Type} [DLO X] (x y : X) : ¬(x <₀ y ∧ y <₀ x) := by
  by_contra h
  apply DLO.irrefl x
  apply DLO.trans x y x
  exact h.left
  exact h.right


-- A different way to characterise no end points.
@[simp]
lemma no_left_extrema {X} [DLO X] : ¬∃y : X, ∀z : X, y = z ∨ y <₀ z := by
  push_neg
  intro y
  have h : ∃w: X, w<₀y := DLO.no_l_end y
  rcases h with ⟨w, hw⟩
  use w
  constructor
  · intro y_is_w
    subst w
    apply DLO.irrefl y
    assumption
  · intro y_lt_w
    apply DLO.asymm y w
    trivial

@[simp]
lemma no_right_extrema {X} [DLO X] : ¬∃y : X, ∀z : X, y = z ∨ y >₀ z := by
  push_neg
  intro y
  have h : ∃w: X, w >₀ y := DLO.no_r_end y
  rcases h with ⟨w, hw⟩
  use w
  constructor
  · intro y_is_w
    subst w
    apply DLO.irrefl y
    assumption
  · intro y_lt_w
    apply DLO.asymm y w
    trivial


end DLO

-- I think this namespace might be done better. We will see. -- Lily
namespace intervals

variable {X : Type} [DLO X]

@[simp]
def boundInterval (a b : X ): Set X :=
  {x:X | a<₀x ∧ x<₀b }

@[simp]
def lowerInterval (a : X): Set X :=
  {x:X | a<₀x }

@[simp]
def upperInterval (b : X): Set X :=
  {x:X | x<₀b }

@[simp]
def singletonInterval (a : X): Set X :=
  {x:X | x=a}


-- Maybe making it map to Prop *is* better? ...I actually just rewrote what you already had, if only just slightly more clearly. - Lily
inductive is_finite_union_of_intervalsP : Set X → Prop where
  | empty   : is_finite_union_of_intervalsP ∅
  -- | entire  : is_finite_union_of_intervalsP univ -- Not needed, logically follows from the others.
  | bounded : (a : X) → (b : X) → is_finite_union_of_intervalsP (boundInterval a b)
  | lower   : (a : X) → is_finite_union_of_intervalsP (lowerInterval a)
  | upper   : (a : X) → is_finite_union_of_intervalsP (upperInterval a)
  | point   : (a : X) → is_finite_union_of_intervalsP (singletonInterval a)
  | union   : ∀ U V : Set X, is_finite_union_of_intervalsP U → is_finite_union_of_intervalsP V → is_finite_union_of_intervalsP (U ∪ V)


@[simp]
lemma union_preserves_finite_union {U V : Set X} (hu : is_finite_union_of_intervalsP U) (hv : is_finite_union_of_intervalsP V) : is_finite_union_of_intervalsP (U ∪ V) := by
  exact is_finite_union_of_intervalsP.union U V hu hv

lemma finite_sets_are_finite_union {U : Set X} (h: Finite U) : is_finite_union_of_intervalsP U := by
  -- induction Set.toFinset U using Finset.induction_on
  -- show (V : Finset X) : is_finite_union_of_intervalsP V
  rw [finite_iff_exists_equiv_fin] at h
  rcases h with ⟨n, hn⟩
  induction' n with n ih
  · have u_is_empty : U = ∅ := by
      sorry
    subst u_is_empty
    exact is_finite_union_of_intervalsP.empty
  .
    rcases hn

    sorry

end intervals

@[simp]
def isDefinable {X:Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U

class Ominimal (X:Type) (L : Language) extends DLO X, Language.Structure L X  where
  definable_sets: ∀ (U: Set (X)), isDefinable L U  ↔ intervals.is_finite_union_of_intervalsP U


--- Defining (ℝ ,<₀) as an Lstructure and trying to prove o-minimality
inductive ordsymbol : Type
| lt : ordsymbol

@[simp]
def order_language : Language where
   Functions := λ _ => Empty
   Relations := λ n => if n = 2 then ordsymbol else Empty


noncomputable section
namespace real_DLO
@[simp]
instance real_order : order ℝ where
  ord (f: Fin 2 → ℝ ) := f 0 < f 1


@[simp]
 instance Rstruc : Language.Structure order_language ℝ  where
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

end real_DLO

open FirstOrder.Language

@[simp]
def constantsOn_toFunctions0 {X : Type} (b : X) : (constantsOn X).Functions 0 :=
  (by simp : (constantsOn X).Functions 0 = X) ▸ b

def constterm {X : Type} (L : FirstOrder.Language) (b : X) : FirstOrder.Language.Term (L.withConstants X) (Fin 1) :=
  Term.func (Sum.inr (constantsOn_toFunctions0 b)) (λ i => nomatch i)

@[simp]
def constR  (b : ℝ ) : FirstOrder.Language.Term (order_language [[univ (α := ℝ)]]) (Fin 1) :=
 (Term.func (Sum.inr (constantsOn_toFunctions0 ⟨b, Set.mem_univ b⟩)) (λ i => nomatch i))





lemma definable_emptyInterval               : isDefinable order_language (∅ : Set ℝ):= by
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


lemma definable_upperInterval     (a   : ℝ) : isDefinable order_language (intervals.upperInterval a):= by
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


lemma definable_lowerInterval     (  b : ℝ) : isDefinable order_language (intervals.lowerInterval b):= by
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


lemma definable_boundInterval     (a b : ℝ) : isDefinable order_language (intervals.boundInterval a b) := by
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
  simp only [intervals.boundInterval, order.lt, real_DLO.instDLOReal, real_DLO.real_order, Fin.isValue, ↓reduceIte, one_ne_zero,
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


lemma definable_singletonInterval (b : ℝ) : isDefinable order_language (singleton b):=  by
  simp only [isDefinable]
  unfold Definable₁
  unfold Definable

  let var :=
    @Term.var (order_language[[univ (α := ℝ)]])  (Fin 1) 0
  let φ : order_language[[↑univ]].Formula (Fin 1) :=
    @FirstOrder.Language.Term.equal _ (Fin 1) var (constR b)

  use φ
  rfl


lemma definable_unionInterval {X L} (U V : Set X) [DLO X] [Language.Structure L X] : isDefinable L U → isDefinable L V → isDefinable L (U ∪ V):= by
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


theorem finite_unions_are_definable : ∀U : Set ℝ, intervals.is_finite_union_of_intervalsP U → isDefinable order_language U := by
  intro U is_finite_union
  induction' is_finite_union with a b a b x A B _ _ A_ih B_ih
  · exact definable_emptyInterval
  · exact definable_boundInterval a b
  · exact definable_lowerInterval a
  · exact definable_upperInterval b
  · exact definable_singletonInterval x
  · apply definable_unionInterval A B
    assumption'

end


namespace FirstOrder
namespace Language
variable (L : Language) (α)


inductive QFBoundedFormula  (L:Language)(α:Type) : ℕ → Type _
  | falsum {n} : QFBoundedFormula L α n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : QFBoundedFormula L α n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFBoundedFormula L α n
  /-- The implication between two bounded formulas -/
  | imp {n} (f₁ f₂ : QFBoundedFormula L α n) : QFBoundedFormula L α n

variable {L α}

def QFBoundedFormula.toBoundedFormula {n : ℕ} : (QFBoundedFormula L α n) → L.BoundedFormula α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .imp f₁ f₂ => .imp f₁.toBoundedFormula f₂.toBoundedFormula
  | .rel R ts => .rel R ts

def QFBoundedFormula.not {n : ℕ} (f : QFBoundedFormula L α n) : QFBoundedFormula L α n :=
  f.imp .falsum

def QFBoundedFormula.and {n : ℕ} (f₁ f₂ : QFBoundedFormula L α n) : QFBoundedFormula L α n :=
  (f₁.imp f₂.not).not

def QFBoundedFormula.or {n : ℕ} (f₁ f₂ : QFBoundedFormula L α n) : QFBoundedFormula L α n :=
  (f₁.and f₂).not


def QFBoundedFormula.Realize {n : ℕ} (f : QFBoundedFormula L α n) (X : Type*) (i : α → X) [L.Structure X](x:Fin n → X) :=
 f.toBoundedFormula.Realize i x

-------------------------------


-- lemma BoundedFormula.toQFBoundedFormula_iff {n}{X:Type} [Language.Structure L X]  (f: L.BoundedFormula α n) (i : α → X) (x:Fin n→ X) :
--  f.Realize i x ↔ (BoundedFormula.toQFBoundedFormula f).toBoundedFormula.Realize i x:= by sorry

instance Real_Ominimal : Ominimal ℝ order_language where
  definable_sets := by sorry

/--
BigAnd formalizes the notion of ∧ to work with an arbitrary number of propositions.
That is, if there's an empty list of propositions, it holds,
and if it's not empty, it holds if all values are evaluated to true.
-/
inductive BigAnd : (n : ℕ) → (Fin n → Prop) → Prop
  | zero (P : Fin 0 → Prop ) : BigAnd 0 P --Modified this; we want this to hold for arbitrary P, not just the specific λ _ => True.
  | succ {n : ℕ} (P : Fin (n + 1) → Prop) :
      P 0 → BigAnd n (fun i => P i.succ) → BigAnd (n + 1) P --If P 0 is true, and we know BigAnd of the list starting at index 1, it holds for the entire list.

section BigAnd

@[simp]
lemma BigAnd_empty (P : Fin 0 → Prop) : BigAnd 0 P := by
  exact BigAnd.zero P

-- @[simp] --Don't know if this would work
lemma BigAnd_succ {n : ℕ} (P : Fin (n + 1) → Prop) (h0 : P 0) (ih : BigAnd n (fun i => P i.succ)) : BigAnd (n + 1) P := by
  exact BigAnd.succ P h0 ih

@[simp]
lemma BigAnd_allTrue (n : ℕ) : BigAnd n fun _ => True := by
  induction' n with n ih
  · exact BigAnd_empty _
  · apply BigAnd_succ _ trivial
    exact ih

@[simp]
lemma BigAnd_allProven (n : ℕ) (P : Fin n → Prop) (all_proven : ∀ i : Fin n, P i) : BigAnd n P := by
  have P_is_essentially_truth_function : P = fun _ => True := by
    ext i
    exact iff_true_intro (all_proven i)
  subst P_is_essentially_truth_function
  exact BigAnd_allTrue n

lemma BigAnd_elimination {n : ℕ} {P : Fin n → Prop} (bigand_P : BigAnd n P) (i : Fin n) : P i := by
  induction' n with n ih
  · exfalso
    apply Nat.not_lt_zero i
    exact i.isLt

  · have i_cases : ↑i < n ∨ ↑i = n := by
      apply Nat.lt_succ_iff_lt_or_eq.mp
      exact i.isLt

    rcases i_cases with lt_n | is_n
    · sorry
    · sorry





lemma existential_over_equal {X : Type} (a : X) (P : X → Prop) : (∃ x : X,  (x=a ∧ P x)) ↔ P a := by
  constructor
  · intro h
    rcases h with ⟨x, ⟨x_eq_a, f_x⟩⟩
    subst x_eq_a
    apply f_x
  · intro h
    use a

/--
Given an array of n real numbers A and another array of m real numbers B, we have the following equivalence:

· There exists a real number x such that x is larger than every number in A but smaller than every number in B.

· Any number in A is smaller than any number in B.
-/
lemma existential_over_disjunction {n m : ℕ} (A : Fin n → ℝ) (B : Fin m → ℝ) : --The name makes little sense if I look at my interpretation of the formula. Also, why did it originally have an argument a? I don't see it.
    (∃x : ℝ, BigAnd _ (fun (i : Fin n) => A i < x) ∧ BigAnd _ (fun (i : Fin m) => x < B i)) ↔
              BigAnd _ (fun (i : Fin m) => (BigAnd _ fun (j : Fin n) => A j < B i)) := by

  constructor
  · intro h
    rcases h with ⟨x, ⟨x_beats_A, x_isbeatenby_B⟩⟩
    induction' m with m ihm
    · exact BigAnd_empty _
    · induction' n with n ihn
      · apply BigAnd_succ (fun i ↦ BigAnd 0 fun j ↦ A j < B i)
        · exact BigAnd_empty _
        · apply BigAnd_allProven
          intro i
          exact BigAnd_empty _

      · apply BigAnd_succ
        · apply BigAnd_succ
          · apply lt_trans (b := x)
            ·
              sorry
            · sorry
          · sorry
        ·
          sorry
  · intro h
    sorry
