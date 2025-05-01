import Mathlib



open Set
open FirstOrder


def funcomb {n:ℕ }{m:ℕ }{X:Type} (f : Fin n → X) (b: Fin m → X): Fin (n+m)→ X :=
fun (k: Fin (n+m)) =>  if  hk: (k.val:ℕ ) < n then  f ⟨k, hk⟩
   else b ⟨k.val  - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Fin.is_lt k)⟩



class order (X : Type) where
  ord : (Fin 2 → X)→ Prop

namespace order
variable {X : Type} [order X]

@[simp]
def lt (a b : X) [order X] : Prop :=
  ord (λ i => if i=0 then a else b)
end order

infix:50 " <₀ " => order.lt
notation x " >₀ " y => y <₀ x

class DLO (X:Type) extends order X where
antirefl: ∀ x:X, ¬(x<₀x)
transitiv: ∀x y z: X, (x<₀y ∧ y<₀z )→x<₀z
total: ∀x y:X, x<₀y ∨ x= y∨ y<₀x
dense: ∀x y:X, x<₀y→∃z:X, x<₀z ∧ z <₀y
nre: ∀x:X, ∃y:X, x<₀y
nle: ∀x: X, ∃w:X, w<₀x

@[simp]
def boundint {X: Type} [DLO X] (a b : X ): Set X:=
{x:X | a<₀x ∧ x<₀b}
@[simp]
def lowerint {X: Type} [DLO X] (a : X ): Set X:=
{x:X | a<₀x }
@[simp]
def upperint {X: Type} [DLO X] (b : X ): Set X:=
{x:X | x<₀b }
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
Definable₁ (univ : Set X ) L U

class Ominimal (X:Type)(L: Language) extends DLO X, Language.Structure L X  where
defsets: ∀ (U: Set (X)), isDefinable L U  ↔ fintervals U


--- Defining (ℝ ,<) as an Lstructure and trying to prove o-minimality


inductive ordsymbol : Type
| lt : ordsymbol

inductive FuncSymbol : ℕ → Type
| const : ℝ → FuncSymbol 0


@[simp]
def Lord : Language where
   Functions := FuncSymbol
   Relations := λ n => if n = 2 then ordsymbol else Empty


open FirstOrder.Language
noncomputable section

@[simp]
instance Rord : order ℝ where
  ord (f: Fin 2 → ℝ ):= f 0 < f 1


@[simp]
 instance Rstruc : Language.Structure Lord ℝ  where
   funMap {n} := λ f =>
    match f with
    | FuncSymbol.const r => λ _ => r
   RelMap {n:ℕ } := λ _ f =>
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

--set_option pp.explicit true



@[simp]
def constantsOn.toFunctions0 {X : Type} (b : X) : (constantsOn X).Functions 0 :=
  (by simp : (constantsOn X).Functions 0 = X) ▸ b

def constterm {X : Type} (L : FirstOrder.Language) (b : X) : FirstOrder.Language.Term (L.withConstants X) (Fin 1) :=
  Term.func (Sum.inr (constantsOn.toFunctions0 b)) (λ i => nomatch i)
@[simp]
def constR  (b : ℝ ) : FirstOrder.Language.Term (Lord[[univ (α := ℝ)]]) (Fin 1) :=
 (Term.func (Sum.inr (constantsOn.toFunctions0 ⟨b, Set.mem_univ b⟩)) (λ i => nomatch i))

@[simp]
lemma singletontdefR (b:ℝ  ) : isDefinable Lord (singleton b):= by
 simp only [isDefinable]
 unfold Definable₁
 unfold Definable
 let var := @Term.var (Lord[[univ (α := ℝ)]])  (Fin 1) 0
 let φ : Lord[[↑univ]].Formula (Fin 1) := @FirstOrder.Language.Term.equal _ (Fin 1 ) var
  (constR b)
 use φ
 exact rfl

 @[simp]
lemma boundintdefR (a b:ℝ): isDefinable Lord (boundint a b):= by
 simp only [isDefinable]
 unfold Definable₁
 unfold Definable
 let var := @Term.var (Lord[[univ (α := ℝ)]])  (Fin 1) 0
 let φ1 : Lord[[↑univ]].Formula (Fin 1) := Relations.formula (Sum.inl ordsymbol.lt) (fun (n: Fin 2) => if n=0 then (constR a ) else var)

 let φ2 : Lord[[↑univ]].Formula (Fin 1) := Relations.formula (Sum.inl ordsymbol.lt) (fun (n: Fin 2) => if n=0 then var else (constR b ))
 use φ1 ⊓ φ2

 ext x
 simp

 constructor
 simp
 intro ass1 ass2
 constructor
 apply ass1
 apply ass2
 rintro ⟨ass1, ass2⟩
 constructor
 apply ass1
 apply ass2


--set_option pp.explicit true
lemma upperintdef (b:ℝ ) : isDefinable Lord  (upperint b):= by
 simp only [isDefinable]
 unfold Definable₁
 unfold Definable
 let var := @Term.var (Lord[[univ (α := ℝ)]])  (Fin 1) 0
 let φ : Lord[[↑univ]].Formula (Fin 1) := Relations.formula (Sum.inl ordsymbol.lt) ![var, constR b]
 use φ
 ext x
 constructor
 intro ass
 apply ass
 intro ass
 apply ass


lemma lowerintdef (a:ℝ ) : isDefinable Lord  (lowerint a):= by
 simp only [isDefinable]
 unfold Definable₁
 unfold Definable
 let var := @Term.var (Lord[[univ (α := ℝ)]])  (Fin 1) 0
 let φ : Lord[[↑univ]].Formula (Fin 1) := Relations.formula (Sum.inl ordsymbol.lt) (fun (n: Fin 2) => if n=0 then (constR a ) else var)
 use φ
 simp
 ext x
 simp
 constructor
 intro ass
 apply ass
 intro ass
 apply ass




instance RealOmin : Ominimal ℝ Lord where
defsets := by  sorry
