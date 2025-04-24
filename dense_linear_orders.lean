import mathlib

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
  irrefl: ∀x: X,     ¬(x<x)
  trans:  ∀x y z: X, x<y → y<z → x<z  --I changed this to be double implication, which Lean usually uses.
  total:  ∀x y: X,   x<y ∨ x=y ∨ y<x
  dense:  ∀x y: X,   x<y → ∃z: X, x<z ∧ z<y
  no_r_end: ∀x: X, ∃y: X, x<y
  no_l_end: ∀x: X, ∃w: X, w<x


@[simp]
def boundint {X: Type} [DLO X] (a b : X ): Set X :=
  {x:X | a<x ∧ x<b }

@[simp]
def lowerint {X: Type} [DLO X] (a : X): Set X :=
  {x:X | a<x }

@[simp]
def upperint {X: Type} [DLO X] (b : X): Set X :=
  {x:X | x<b }

@[simp]
def singletons {X: Type} [DLO X] (a : X): Set X :=
  {x:X | x=a}


-- Should this really be Prop? I'm not sure myself.
-- We want to express the idea that something is a finite union of intervals.
-- Will need to think how to properly express that.
-- Also I changed the name, but now it might be too long. - Lily
inductive finite_unions_of_intervals {X : Type} [DLO X] : Set X → Prop
  | bound (a b : X) : finite_unions_of_intervals (boundint a b)
  | lower (a : X)   : finite_unions_of_intervals (lowerint a)
  | upper (b : X)   : finite_unions_of_intervals (upperint b)
  | point (a : X)   : finite_unions_of_intervals (singletons a)
  | union : ∀ U V : Set X , finite_unions_of_intervals U → finite_unions_of_intervals V → finite_unions_of_intervals (U ∪ V)

@[simp]
def isDefinable {X:Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U

class Ominimal (X:Type) (L : Language) extends DLO X, Language.Structure L X  where
  definable_sets: ∀ (U: Set (X)), isDefinable L U  ↔ finite_unions_of_intervals U


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
  ord (f: Fin 2 → ℝ ):= f 0 < f 1


@[simp]
 instance Rstruc : Language.Structure order_language ℝ  where
   funMap:= λ  empt=> Empty.elim empt
   RelMap {n:ℕ }:= λ _ f =>
    match n with
    | 2=>
      match f with
      | _ => real_order.ord f
    | _ => false


@[simp]
instance : DLO ℝ  where
  irrefl := by intros x h; exact lt_irrefl x h
  trans := by
    rintro x y z h1 h2
    exact lt_trans h1 h2
  total := by intros x y; exact lt_trichotomy x y
  dense := by intros x y h; exact exists_between h
  no_r_end := by intro x; exact ⟨x + 1, by simp⟩
  no_l_end := by intro x; exact ⟨x - 1, by simp⟩



lemma upperintdef {X L} (b:X) [DLO X] [Language.Structure L X] : isDefinable L (upperint b):= by
  sorry

lemma lowerintdef {X L} (b:X) [DLO X] [Language.Structure L X] : isDefinable L (lowerint b):= by
 sorry

lemma boundintdef {X L} (a b:X) [DLO X] [Language.Structure L X] : isDefinable L (boundint a b):= by
 sorry

lemma singletontdef {X L} (b:X) [DLO X] [Language.Structure L X] : isDefinable L (singleton b):= by
 simp
 unfold Definable₁
 unfold Definable
 sorry




instance RealOmin : Ominimal ℝ order_language where
  definable_sets := by sorry
