import mathlib



open Set
open FirstOrder


def funcomb {n:ℕ }{m:ℕ }{X:Type} (f : Fin n → X) (b: Fin m → X): Fin (n+m)→ X :=
fun (k: Fin (n+m)) =>  if  hk: (k.val:ℕ ) < n then  f ⟨k, hk⟩
   else b ⟨k.val  - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Fin.is_lt k)⟩


-- Step 10: Defining the dense linear order (DLO)

class order (X : Type) where
  ord : (Fin 2 → X)→ Prop

namespace order
variable {X : Type} [order X]

@[simp]
def lt (a b : X) [order X] : Prop :=
  ord (λ i => if i=0 then a else b)
end order

infix:50 " < " => order.lt
notation x " > " y => y < x

class DLO (X:Type) extends order X where
antirefl: ∀ x:X, ¬(x<x)
transitiv: ∀x y z: X, (x<y ∧ y<z )→x<z
total: ∀x y:X, x<y ∨ x= y∨ y<x
dense: ∀x y:X, x<y→∃z:X, x<z ∧ z <y
nre: ∀x:X, ∃y:X, x<y
nle: ∀x: X, ∃w:X, w<x

@[simp]
def boundint {X: Type} [DLO X] (a b : X ): Set X:=
{x:X | a<x ∧ x<b}
@[simp]
def lowerint {X: Type} [DLO X] (a : X ): Set X:=
{x:X | a<x }
@[simp]
def upperint {X: Type} [DLO X] (b : X ): Set X:=
{x:X | x<b }
@[simp]
def singletons {X:Type } [DLO X] (a:X): Set X := {x:X | x=a}

inductive fintervals {X:Type } [DLO X] : Set X → Prop
| bound (a b : X) : fintervals (boundint a b)
| lower (a : X)   : fintervals (lowerint a)
| upper (b : X)   : fintervals (upperint b)
| point (a : X)   : fintervals (singletons a)
| union : ∀ U V : Set X , fintervals U→  fintervals V→ fintervals (U∪ V)


@[simp]
def isDefinable {X:Type} (L:Language) (U:Set X) [Language.Structure L X] : Prop :=
Definable₁ (⊤ : Set X ) L U

class Ominimal (X:Type)(L: Language) extends DLO X, Language.Structure L X  where
defsets: ∀ (U: Set (X)), isDefinable L U  ↔ fintervals U


--- Defining (ℝ ,<) as an Lstructure and trying to prove o-minimality
inductive ordsymbol : Type
| geq : ordsymbol

@[simp]
def Lord : Language where
   Functions := λ _ => Empty
   Relations := λ n => if n = 2 then ordsymbol else Empty



noncomputable section
@[simp]
instance Rord : order ℝ where
  ord (f: Fin 2 → ℝ ):= f 0 < f 1


@[simp]
 instance Rstruc : Language.Structure Lord ℝ  where
   funMap:= λ  empt=> Empty.elim empt
   RelMap {n:ℕ }:= λ _ f =>
    match n with
    | 2=>
      match f with
      | _ => Rord.ord f
    | _ => false


@[simp]
instance : DLO ℝ  where
  antirefl := by intros x h; exact lt_irrefl x h
  transitiv := by
    rintro x y z ⟨h1, h2⟩
    simp at h1 h2
    simp
    linarith
  total := by intros x y; exact lt_trichotomy x y
  dense := by intros x y h; exact exists_between h
  nre := by intro x; exact ⟨x + 1, by simp⟩
  nle := by intro x; exact ⟨x - 1, by simp⟩



lemma upperintdef (b:X)[DLO X] [Language.Structure L X] : isDefinable L (upperint b):= by
 sorry
lemma lowerintdef (b:X)[DLO X] [Language.Structure L X] : isDefinable L (lowerint b):= by
 sorry
lemma boundintdef (a b:X)[DLO X] [Language.Structure L X] : isDefinable L (boundint a b):= by
 sorry

lemma singletontdef (b:X)[DLO X] [Language.Structure L X] : isDefinable L (singleton b):= by
 simp
 unfold Definable₁
 unfold Definable
 sorry




instance RealOmin : Ominimal ℝ Lord where
defsets := by  sorry
