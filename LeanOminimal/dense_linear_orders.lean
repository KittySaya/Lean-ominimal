import Mathlib

open Set
open FirstOrder


-- What does this do?
def funcomb {n : ℕ} {m : ℕ} {X : Type} (f: Fin n → X) (b: Fin m → X): Fin (n+m) → X :=
  fun (k: Fin (n+m)) =>
    if  hk: (k.val: ℕ) < n then f ⟨k, hk⟩
    else b ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Fin.is_lt k)⟩


-- Step 10: Defining the dense linear order (DLO)

class order (X : Type) where
  ord : (Fin 2 → X) → Prop

namespace order
variable {X : Type} [order X]

@[simp]
def lt (a b : X) [order X] : Prop :=
  ord (λ i => if i=0 then a else b)
end order

infix:50 " < " => order.lt
notation x " > " y => y < x

class DLO (X:Type) extends order X where
  irrefl:   ∀x: X,     ¬(x<x)
  trans:    ∀x y z: X, x<y → y<z → x<z  --I changed this to be double implication, which Lean usually uses.
  total:    ∀x y: X,   x<y ∨ x=y ∨ y<x
  dense:    ∀x y: X,   x<y → ∃z: X, x<z ∧ z<y
  no_r_end: ∀x: X, ∃y: X, x<y
  no_l_end: ∀x: X, ∃w: X, w<x

namespace DLO

-- Every dense linear order is asymetric.
@[simp]
lemma asymm {X : Type} [DLO X] (x y : X) : ¬(x < y ∧ y < x) := by
  by_contra h
  apply DLO.irrefl x
  apply DLO.trans x y x
  exact h.left
  exact h.right


-- A different way to characterise no end points.
@[simp]
lemma no_left_extrema {X} [DLO X] : ¬∃y : X, ∀z : X, y = z ∨ y < z := by
  push_neg
  intro y
  have h : ∃w: X, w<y := DLO.no_l_end y
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
lemma no_right_extrema {X} [DLO X] : ¬∃y : X, ∀z : X, y = z ∨ y > z := by
  push_neg
  intro y
  have h : ∃w: X, w>y := DLO.no_r_end y
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
def boundint (a b : X ): Set X :=
  {x:X | a<x ∧ x<b }

@[simp]
def lowerint (a : X): Set X :=
  {x:X | a<x }

@[simp]
def upperint (b : X): Set X :=
  {x:X | x<b }

@[simp]
def singletons (a : X): Set X :=
  {x:X | x=a}

-- @[simp]
-- def interval_union (U : Set X) (V : Set X) :=
--   U ∪ V

-- infix:50 " ∪ " => interval_union

-- lemma interval_union_symm (U : Set X) (V : Set X) : U ∪ V = V ∪ U := by
--   sorry


-- Should this really be Prop? I'm not sure myself.
-- We want to express the idea that something is a finite union of intervals.
-- Will need to think how to properly express that.
-- Also I changed the name, but now it might be too long. - Lily
-- inductive fintervals {X : Type} [DLO X] : Set X → Prop
--   | bound (a b : X) : fintervals (boundint a b)
--   | lower (a : X)   : fintervals (lowerint a)
--   | upper (b : X)   : fintervals (upperint b)
--   | point (a : X)   : fintervals (singletons a)
--   | union : ∀ U V : Set X , fintervals U → fintervals V → fintervals (U ∪ V)

-- I rewrote the finite_unions_of_intervals to be more apparant, but am missing the property that makes them what they are. Will see what I can do.
-- inductive is_finite_unions_of_intervals {X : Type} [DLO X] where
--   | empty  : finite_unions_of_intervals
--   | entire : finite_unions_of_intervals
--   | simple : X -> X ->  finite_unions_of_intervals
--   | lower  : X -> finite_unions_of_intervals
--   | upper  : X -> finite_unions_of_intervals
--   | point  : X -> finite_unions_of_intervals
--   | union  : finite_unions_of_intervals → finite_unions_of_intervals → finite_unions_of_intervals

-- Maybe making it map to Prop *is* better? ...I actually just rewrote what you already had, if only just slightly more clearly. - Lily
inductive is_finite_union_of_intervalsP : Set X → Prop where
  | empty   : is_finite_union_of_intervalsP ∅
  -- | entire  : is_finite_union_of_intervalsP univ -- Not needed, logically follows from the others.
  | bounded : (a : X) → (b : X) → is_finite_union_of_intervalsP (boundint a b)
  | lower   : (a : X) → is_finite_union_of_intervalsP (lowerint a)
  | upper   : (a : X) → is_finite_union_of_intervalsP (upperint a)
  | point   : (a : X) → is_finite_union_of_intervalsP (singletons a)
  | union   : ∀ U V : Set X, is_finite_union_of_intervalsP U → is_finite_union_of_intervalsP V → is_finite_union_of_intervalsP (U ∪ V)

@[simp]
lemma union_preserves_finite_union {U V : Set X} (hu : is_finite_union_of_intervalsP U) (hv : is_finite_union_of_intervalsP V) : is_finite_union_of_intervalsP (U ∪ V) := by
  exact is_finite_union_of_intervalsP.union U V hu hv

lemma finite_sets_are_finite_union {U : Set X} (h: Finite U) : is_finite_union_of_intervalsP U := by
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

@[simp]
def isDefinable {X:Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U

class Ominimal (X:Type) (L : Language) extends DLO X, Language.Structure L X  where
  definable_sets: ∀ (U: Set (X)), isDefinable L U  ↔ is_finite_union_of_intervalsP U


--- Defining (ℝ ,<) as an Lstructure and trying to prove o-minimality
--Inductive??? - Lily
inductive ordsymbol : Type
| geq : ordsymbol

@[simp]
def order_language : Language where
   Functions := λ _ => Empty
   Relations := λ n => if n = 2 then ordsymbol else Empty


noncomputable section
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



lemma definable_emptyInterval     {X L}         [DLO X] [Language.Structure L X] : isDefinable L (∅ : Set X):=    by
  sorry

lemma definable_upperInterval     {X L} (b:X)   [DLO X] [Language.Structure L X] : isDefinable L (upperint b):=   by
  sorry

lemma definable_lowerInterval     {X L} (b:X)   [DLO X] [Language.Structure L X] : isDefinable L (lowerint b):=   by
  sorry

lemma definable_boundInterval     {X L} (a b:X) [DLO X] [Language.Structure L X] : isDefinable L (boundint a b):= by
  sorry

lemma definable_singletonInterval {X L} (b:X)   [DLO X] [Language.Structure L X] : isDefinable L (singleton b):=  by
  simp
  unfold Definable₁
  unfold Definable
  sorry

lemma definable_unionInterval {X L} (U V : Set X) [DLO X] [Language.Structure L X] : isDefinable L U → isDefinable L V → isDefinable L (U ∪ V):= by
 simp
 unfold Definable₁
 unfold Definable
 intro U_definable
 intro V_definable
 rcases U_definable with ⟨φ, hφ⟩
 rcases V_definable with ⟨ψ, hψ⟩
--  use (φ ∨ ψ)

 sorry


-- This errors without the sorry. Why?
theorem finite_unions_are_definable {X L} [DLO X] [Language.Structure L X] : ∀U : Set X, is_finite_union_of_intervalsP U → isDefinable L U := by
  intro U is_finite_union
  rcases is_finite_union with _ | ⟨a, b⟩ | a | b | x | ⟨U, V, hU, hV⟩
  · exact definable_emptyInterval
  · exact definable_boundInterval a b
  · exact definable_lowerInterval a
  · exact definable_upperInterval b
  · exact definable_singletonInterval x
  ·
    sorry
    -- apply definable_unionInterval U V
    -- exact finite_unions_are_definable U hU
    -- exact finite_unions_are_definable V hV




instance RealOmin : Ominimal ℝ order_language where
  definable_sets := by sorry
