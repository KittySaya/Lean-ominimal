import Mathlib

open Set
open FirstOrder


-- What does this do?
def funcomb {n : ℕ} {m : ℕ} {X : Type} (f: Fin n → X) (b: Fin m → X): Fin (n+m) → X :=
  fun (k: Fin (n+m)) =>
    if  hk: (k.val: ℕ) < n then f ⟨k, hk⟩
    else b ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Fin.is_lt k)⟩


-- Section 1: Defining the order
section order_definition

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

end order_definition



-- Section 2: Defining a dense linear order (DLO)
section DLO_definition
class DLO (X:Type) extends order X where
  irrefl:   ∀x: X,     ¬(x<₀x)
  trans:    ∀x y z: X, x<₀y → y<₀z → x<₀z  --I changed this to be double implication, which Lean usually uses.
  total:    ∀x y: X,   x<₀y ∨ x=y ∨ y<₀x
  dense:    ∀x y: X,   x<₀y → ∃z: X, x<₀z ∧ z<₀y
  no_r_end: ∀x: X, ∃y: X, x<₀y
  no_l_end: ∀x: X, ∃w: X, w<₀x


namespace DLO

-- Basic lemma's.
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
  have h : ∃w: X, w <₀ y := DLO.no_l_end y
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
end DLO_definition


-- Section 3: Intervals
section intervals
namespace DLO.interval

variable {X : Type} [DLO X]

@[simp]
def bounded (a b : X ): Set X :=
  {x:X | a<₀x ∧ x<₀b }

@[simp]
def lower (a : X): Set X :=
  {x:X | a<₀x }

@[simp]
def upper (b : X): Set X :=
  {x:X | x<₀b }

@[simp]
def singleton (a : X): Set X :=
  {x:X | x=a}


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


@[simp]
lemma union_preserves_finite_union {U V : Set X} (hu : is_finite_union_of_intervalsP U) (hv : is_finite_union_of_intervalsP V) : is_finite_union_of_intervalsP (U ∪ V) := by
  exact is_finite_union_of_intervalsP.union U V hu hv

-- -- Maybe skip this one? If we can't find a proof; it's not mandatory.
-- lemma finite_sets_are_finite_union {U : Set X} (h: Finite U) : is_finite_union_of_intervalsP U := by
--   -- induction Set.toFinset U using Finset.induction_on
--   -- show (V : Finset X) : is_finite_union_of_intervalsP V
--   rw [finite_iff_exists_equiv_fin] at h
--   rcases h with ⟨n, hn⟩
--   induction' n with n ih
--   · have u_is_empty : U = ∅ := by
--       sorry
--     subst u_is_empty
--     exact is_finite_union_of_intervalsP.empty
--   .
--     rcases hn

--    sorry

end DLO.interval
end intervals


-- Section 4: Definability
section definability
@[simp]
def isDefinable {X:Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U

class Ominimal (X:Type) (L : Language) extends DLO X, Language.Structure L X  where
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


lemma definable_upperInterval     (a   : ℝ) : isDefinable order_language (DLO.interval.upper a):= by
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


lemma definable_lowerInterval     (  b : ℝ) : isDefinable order_language (DLO.interval.lower b):= by
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


lemma definable_boundInterval     (a b : ℝ) : isDefinable order_language (DLO.interval.bounded a b) := by
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


lemma definable_unionInterval {X L} (U V : Set X) [DLO X] [Language.Structure L X] : isDefinable L U → isDefinable L V → isDefinable L (U ∪ V) := by
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


theorem finite_unions_are_definable : ∀U : Set ℝ, DLO.interval.is_finite_union_of_intervalsP U → isDefinable order_language U := by
  intro U is_finite_union
  induction' is_finite_union with a b a b x A B _ _ A_ih B_ih
  · exact definable_emptyInterval
  · exact definable_boundInterval a b
  · exact definable_lowerInterval a
  · exact definable_upperInterval b
  · exact definable_singletonInterval x
  · exact definable_unionInterval A B A_ih B_ih

end real_DLO
end reals
end definability

-- Other sections?
-- namespace MyFirstOrder -- I would personally prefer not using an already existing name. -Lily
namespace FirstOrder
namespace Language



inductive Literal (L : Language) (α : Type) : ℕ → Type _
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Literal L α n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Literal L α n
  | not {n} (f:Literal L α n) : Literal L α n


inductive ImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n : ℕ} : ImpAllFreeFormula L α n
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n

  | not    {n : ℕ}   (f     : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | or     {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | and    {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n

  | exists {n : ℕ}   (f : ImpAllFreeFormula L α (n + 1)) : ImpAllFreeFormula L α n

/-
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : BoundedFormula n
  /-- The implication between two bounded formulas -/
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  /-- The universal quantifier over bounded formulas -/
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n
-/

def ImpAllFreeFormula.toBounded {L} {α} {n} : ImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => (f.toBounded).imp .falsum
  | .or f₁ f₂ => ((f₁.not).toBounded).imp f₂.toBounded
  | .and f₁ f₂ => ((f₁.not).or (f₂.not).not).toBounded
  | .exists f => (((f.toBounded).not).all).not

variable {L α}

def BoundedFormula.toImpAllFreeFormula {L}{α} {n} : BoundedFormula L α n → ImpAllFreeFormula L α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .imp f₁ f₂ => ((f₁.toImpAllFreeFormula).not).or f₂.toImpAllFreeFormula
  | .all f => (((f.toImpAllFreeFormula).not).exists).not

/- lemma f.Realize i x ↔ (BoundedFormula.toImpAllFreeFormula f).toBoundedFormula.Realize i x:= by sorry -/

/--
The type of Quantifier Free bounded formulae without implications.
-/
inductive QFImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n} : QFImpAllFreeFormula L α n
  | equal  {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  | not    {n} (f : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n
  | or     {n} (f₁ f₂ : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n
  | and    {n} (f₁ f₂ : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n



-------------------------------


-- lemma BoundedFormula.toQFBoundedFormula_iff {n}{X:Type} [Language.Structure L X]  (f: L.BoundedFormula α n) (i : α → X) (x:Fin n→ X) :
--  f.Realize i x ↔ (BoundedFormula.toQFBoundedFormula f).toBoundedFormula.Realize i x:= by sorry


/--
Given an array of n real numbers A and another array of m real numbers B, we have the following equivalence:

· There exists a real number x such that x is larger than every number in A but smaller than every number in B.

· Any number in A is smaller than any number in B.
-/
def Literal.toImpAllFreeFormula {L}{α} {n} : Literal L α n → ImpAllFreeFormula L α n
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => .not f.toImpAllFreeFormula



def BigAndFormula {L : Language} {α : Type} {m : ℕ} :
    ∀ (n : ℕ), (Fin n → Literal L α m) → ImpAllFreeFormula L α m
  | 0, _ => .falsum
  | n+1, f =>
    let head := f 0
    let tail := fun i : Fin n => f i.succ
    head.toImpAllFreeFormula.and (BigAndFormula n tail)

def reducible_formula {n:ℕ }{α:Type }{m:ℕ }(f: Fin (n) → Literal order_language α (m+1)): ImpAllFreeFormula order_language α m:=
 (BigAndFormula (n) f).exists



def ImpAllFreeFormula.Realize {L : Language} : ∀ {l} (_f : BoundedFormula L α l) (_v : α → ℝ) (_xs : Fin l → ℝ), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => Realize f₁ v xs → Realize f₂ v xs
  | _, all f, v, xs => ∀ x : M, Realize f v (snoc xs x)

variable (L : Language) (α)

/- lemma f.Realize i x ↔ (BoundedFormula.toImpAllFreeFormula f).toBoundedFormula.Realize i x:= by sorry -/

/--
The type of Quantifier Free bounded formulae
-/
inductive QFBoundedFormula (L:Language) (α:Type) : ℕ → Type _
  | falsum {n} : QFBoundedFormula L α n
  | equal  {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : QFBoundedFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFBoundedFormula L α n
  /-- The implication between two bounded formulas -/
  | imp    {n} (f₁ f₂ : QFBoundedFormula L α n) : QFBoundedFormula L α n


variable {L α}

namespace QFBoundedFormula

def toBoundedFormula {n : ℕ} : (QFBoundedFormula L α n) → L.BoundedFormula α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .imp f₁ f₂ => .imp f₁.toBoundedFormula f₂.toBoundedFormula
  | .rel R ts => .rel R ts

def not {n : ℕ} (f : QFBoundedFormula L α n) : QFBoundedFormula L α n :=
  f.imp .falsum

def and {n : ℕ} (f₁ f₂ : QFBoundedFormula L α n) : QFBoundedFormula L α n :=
  (f₁.imp f₂.not).not

def or {n : ℕ} (f₁ f₂ : QFBoundedFormula L α n) : QFBoundedFormula L α n :=
  (f₁.and f₂).not


def Realize {n : ℕ} (f : QFBoundedFormula L α n) (X : Type*) (i : α → X) [L.Structure X](x:Fin n → X) :=
 f.toBoundedFormula.Realize i x

end QFBoundedFormula


def Big_and.toQFImpAllFreeFormula {α : Type} {n m : ℕ} (f : Fin n → Literal order_language α m) : QFImpAllFreeFormula order_language α m := by
  induction' n with k ih
  · exact QFImpAllFreeFormula.not QFImpAllFreeFormula.falsum

  -- Split f into head and tail:
  let f0 : Literal order_language α m := f 0
  let g : Fin k → Literal order_language α m :=
    λ i => f (Fin.succ i)

  rcases f0
  · exact ih g
  · exact ih g
  · exact ih g


inductive Literalblock (L : Language) (α : Type) : ℕ → Type _
  | truth {n} : Literalblock L α n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Literalblock L α n
  | rel   {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Literalblock L α n

  | and   {n : ℕ} (f1 f2 : Literalblock L α n) : Literalblock L α n
  | or    {n : ℕ} (f1 f2 : Literalblock L α n) : Literalblock L α n

def Literalblock.toImpAllFreeFormula {n : ℕ} : (Literalblock L α n) → L.ImpAllFreeFormula α n
  | .truth  => ImpAllFreeFormula.falsum.not
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel   R ts => .rel R ts
  | .or    f₁ f₂ => f₁.toImpAllFreeFormula.or f₂.toImpAllFreeFormula
  | .and   f₁ f₂ => f₁.toImpAllFreeFormula.and f₂.toImpAllFreeFormula




def Big_and.toLiteralblock {α : Type} {m : ℕ} {n : ℕ} (f : Fin n → Literal order_language α m) : Literalblock order_language α m := by
 induction n with
  | zero =>
    exact Literalblock.truth
  | succ n ih =>

    -- Split f into head and tail:
    let f0 : Literal order_language α (m ) := f 0
    let g : Fin n → Literal order_language α (m ) :=
      λ i => f (Fin.succ i)

    have qf_tail := ih g



    rcases f0 with ⟨f1 ,f2⟩ | ⟨R, f⟩ | ⟨t1, t2⟩ | ⟨R, f⟩ | f

    · let QF :=  Literalblock.equal f1 f2
      exact QF.and qf_tail

    · let QF :=  Literalblock.rel R f
      exact QF.and qf_tail

    · rcases t1 with ⟨a1 ⟩ | ⟨_, _ ⟩ | ⟨_, _ ⟩
      rcases t2 with ⟨a2 ⟩  | ⟨_, _ ⟩ | ⟨_, _ ⟩
      let or1 :=  @Term.var (order_language) (α ⊕ Fin m) a1
      let or2 :=  @Term.var (order_language) (α ⊕ Fin m) a2
      let QF1 := Literalblock.rel (ordsymbol.lt) (fun (i:Fin 2)=>  if i=0 then or1 else or2  )
      let QF2 := Literalblock.rel (ordsymbol.lt) (fun (i:Fin 2)=> if i=0 then or2 else or1 )
      let QF := QF1.or QF2
      exact QF.and qf_tail

    · rename_i l
      by_cases neq: l=2
      let ter1:= f ⟨0, by linarith⟩
      let ter2 := f ⟨1, by linarith⟩
      let QF1 := Literalblock.rel (ordsymbol.lt) (fun (i:Fin 2)=>  if i=0 then ter2 else ter1  )
      let QF2 := Literalblock.equal ter1 ter2
      let QF := QF1.or QF2
      exact QF.and qf_tail
      exfalso
      have R_empty : order_language.Relations l = Empty := by
        dsimp [order_language]
        simp only [ne_eq] at neq
        simp [dif_neg neq]
        intro l_is_2
        exfalso
        trivial

      rw [R_empty] at R
      exact R.elim

    · exact  (ih (λ i:Fin n=> f  )).and qf_tail


def existblock (L : Language) (α : Type) (length : ℕ) :=
  -- FirstOrder.Language.BoundedFormula.ex (
  --   fun n : ℕ =>
  --   | zero =>
  --   | succ =>
  -- )
  sorry


def existblock.toQFImpAllFreeFormula {α : Type} {n : ℕ} {m : ℕ} (f : Fin n → Literal order_language α (m+1)) : QFImpAllFreeFormula order_language α (m) := by
  have existblock := (Big_and.toLiteralblock f).toImpAllFreeFormula.exists
  dsimp [Big_and.toLiteralblock, QFImpAllFreeFormula.toImpAllFreeFormula] at existblock
  cases existblock
  repeat' sorry


end Language
end FirstOrder
-------------------------------

section QuantifierELimination

def isExistBlock {L : Language} {α : Type} {n : ℕ} (φ : FirstOrder.Language.BoundedFormula L α n) : Prop :=

  sorry

def has_quantifierfreefromula {L : Language} {α : Type} {n : ℕ} (φ : FirstOrder.Language.BoundedFormula L α n) :=
  ∃ ψ : FirstOrder.Language.QFBoundedFormula L α n,
    φ.iff (Language.QFBoundedFormula.toBoundedFormula ψ) = Language.BoundedFormula.falsum.not
    -- This definition needs to be better. Something with ∃'?

def admits_quantifier_elimination (L : Language) (α : Type) :=
  ∀n : ℕ, ∀ φ : FirstOrder.Language.BoundedFormula L α n, has_quantifierfreefromula φ
  -- Is this a proper definition?

theorem of_exist_bigand_blocks {L : Language} {α : Type} (for_existsblocks : ∀n : ℕ, ∀φ : FirstOrder.Language.BoundedFormula L α n, isExistBlock φ → has_quantifierfreefromula φ) : admits_quantifier_elimination L α := by
  intro n φ
  induction' φ with _ _ eq_t₁ eq_t₂ _ _ rel_R rel_ts _ imp_f₁ imp_f₂
  repeat1' expose_names
  · use Language.QFBoundedFormula.falsum
    sorry
  · use Language.QFBoundedFormula.equal eq_t₁ eq_t₂
    sorry
  · use Language.QFBoundedFormula.rel rel_R rel_ts
    sorry
  · use Language.QFBoundedFormula.imp imp_f₁ imp_f₂
    sorry
  · sorry

end QuantifierELimination

-- lemma BoundedFormula.toQFBoundedFormula_iff {n}{X:Type} [Language.Structure L X]  (f: L.BoundedFormula α n) (i : α → X) (x:Fin n→ X) :
--  f.Realize i x ↔ (BoundedFormula.toQFBoundedFormula f).toBoundedFormula.Realize i x:= by sorry


section Big_And_section

/--
BigAnd formalizes the notion of ∧ to work with an arbitrary number of propositions.
That is, if there's an empty list of propositions, it holds;
and if it's not empty, it holds if all values are evaluated to true.
-/
inductive BigAnd : (n : ℕ) → (Fin n → Prop) → Prop
  | zero (P : Fin 0 → Prop) : BigAnd 0 P --Modified this; we want this to hold for arbitrary P, not just the specific λ _ => True.
  | succ {m : ℕ} (P : Fin (m + 1) → Prop) :
      P 0 → BigAnd m (fun i => P i.succ) → BigAnd (m + 1) P --If P 0 is true, and we know BigAnd of the list starting at index 1, it holds for the entire list.

namespace BigAnd

@[simp]
lemma ofEmpty (P : Fin 0 → Prop) : BigAnd 0 P := by
  exact BigAnd.zero P

/--
In order to prove that BigAnd (n + 1) P holds,
where P is a function from Fin (n + 1) to Prop,
it suffices to show that:

· P 0 holds

· BigAnd n (fun i => P i.succ) holds
-/
-- @[simp] --Don't know if this would work
lemma SuccDef {n : ℕ} (P : Fin (n + 1) → Prop) (h0 : P 0) (ih : BigAnd n (fun i => P i.succ)) : BigAnd (n + 1) P := by
  exact BigAnd.succ P h0 ih

@[simp]
lemma ofAllTrue (n : ℕ) : BigAnd n fun _ => True := by
  induction' n with n ih
  · exact BigAnd.ofEmpty _
  · apply BigAnd.SuccDef _ trivial
    exact ih

@[simp]
lemma ofAllProven (n : ℕ) (P : Fin n → Prop) (all_proven : ∀ i : Fin n, P i) : BigAnd n P := by
  have P_is_essentially_truth_function : P = fun _ => True := by
    ext i
    exact iff_true_intro (all_proven i)
  subst P_is_essentially_truth_function
  exact BigAnd.ofAllTrue n

lemma eliminationAtIndex {n : ℕ} {P : Fin n → Prop} (bigand_P : BigAnd n P) (i : Fin n) : P i := by
  induction' n with n ih
  · exfalso
    apply Nat.not_lt_zero i
    exact i.isLt

  · have i_cases : i = 0 ∨ 0 < i := by
      convert Nat.eq_zero_or_pos i
      exact Iff.symm Fin.val_eq_zero_iff

    rcases bigand_P with _ | ⟨_, P_zero, bigand_succ⟩
    rcases i_cases with is_nill | is_pos
    · subst is_nill
      assumption

    · clear n
      specialize ih (P := (fun j => P j.succ)) bigand_succ

      let j := i.pred (ne_of_gt is_pos)

      have jsucc_eq_i : j.succ = i := by
        refine Eq.symm (Fin.eq_of_val_eq ?_)
        unfold j
        symm
        apply Nat.succ_pred (ne_of_gt is_pos)

      specialize ih j
      rw [jsucc_eq_i] at ih
      trivial

end BigAnd


namespace existential_elimination
namespace steps
lemma of_equal {X : Type} (a : X) (P : X → Prop) : (∃ x : X,  (x=a ∧ P x)) ↔ P a := by
  constructor
  · intro h
    rcases h with ⟨x, ⟨x_eq_a, f_x⟩⟩
    subst x_eq_a
    apply f_x
  · intro h
    use a

@[simp]
lemma nonempty_finset_of_nezero {k : ℕ} (k_nonzero : ¬(k = 0)) : Nonempty (Fin k) := by
  exact Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero k_nonzero)

/--
Given an array of n real numbers A and another array of m real numbers B, we have the following equivalence:

· There exists a real number x such that x is larger than every number in A but smaller than every number in B.

· Any number in A is smaller than any number in B.
-/
theorem of_inequals {n m : ℕ} (A : Fin n → ℝ) (B : Fin m → ℝ) : --The name makes little sense if I look at my interpretation of the formula. Also, why did it originally have an argument a? I don't see it.
    (∃x : ℝ, BigAnd _ (fun (i : Fin n) => A i < x) ∧ BigAnd _ (fun (i : Fin m) => x < B i)) ↔
              BigAnd _ (fun (i : Fin m) => (BigAnd _ fun (j : Fin n) => A j < B i)) := by

  constructor
  · intro h
    rcases h with ⟨x, ⟨x_beats_A, x_isbeatenby_B⟩⟩
    induction' m with m ihm
    · exact BigAnd.ofEmpty _
    · induction' n with n ihn
      · apply BigAnd.SuccDef (fun i ↦ BigAnd 0 fun j ↦ A j < B i)
        · exact BigAnd.ofEmpty _
        · apply BigAnd.ofAllProven
          intro i
          exact BigAnd.ofEmpty _

      · apply BigAnd.SuccDef
        · apply BigAnd.SuccDef
          · apply lt_trans (b := x)
            · exact BigAnd.eliminationAtIndex x_beats_A 0
            · exact BigAnd.eliminationAtIndex x_isbeatenby_B 0
          · refine BigAnd.ofAllProven n (fun i ↦ A i.succ < B 0) ?_
            intro i
            · apply lt_trans (b := x)
              · exact BigAnd.eliminationAtIndex x_beats_A i.succ
              · exact BigAnd.eliminationAtIndex x_isbeatenby_B 0

        · apply ihm (fun j => B j.succ)
          apply BigAnd.ofAllProven m _
          intro i
          apply BigAnd.eliminationAtIndex x_isbeatenby_B i.succ


  · intro h
    by_cases n_val : n = 0
    · subst n_val
      by_cases m_val : m = 0
      · subst m_val
        use 2.71828182846 * 3.14159
        exact ⟨BigAnd.ofEmpty _, BigAnd.ofEmpty _⟩

      · let B_min := Finset.min' (Finset.image B Finset.univ) (by simp [nonempty_finset_of_nezero, m_val])

        have B_min_is_minimum (i: Fin m) : B_min ≤ B i := by
          apply Finset.min'_le _ (B i) (mem_image_univ_iff_mem_range.mpr (mem_range_self i))

        rcases DLO.no_l_end B_min with ⟨B_min', B_min'_lt_B_min⟩
        dsimp at B_min'_lt_B_min
        use B_min'
        constructor
        · exact BigAnd.ofEmpty _

        · apply BigAnd.ofAllProven
          intro i
          apply lt_of_lt_of_le B_min'_lt_B_min
          exact B_min_is_minimum i

    · let A_max := Finset.max' (Finset.image A Finset.univ) (by simp [nonempty_finset_of_nezero, n_val])
      have A_max_is_maximum (i: Fin n) : A i ≤ A_max := by
          apply Finset.le_max' _ _ (mem_image_univ_iff_mem_range.mpr (mem_range_self i))

      by_cases m_val : m = 0
      · subst m_val
        rcases DLO.no_r_end A_max with ⟨A_max', A_max'_gt_A_max⟩
        dsimp at A_max'_gt_A_max
        use A_max'
        constructor
        · apply BigAnd.ofAllProven
          intro i
          apply lt_of_le_of_lt _ A_max'_gt_A_max
          exact A_max_is_maximum i

        · exact BigAnd.ofEmpty _

      · let B_min := Finset.min' (Finset.image B Finset.univ) (by simp [nonempty_finset_of_nezero, m_val])
        have B_min_is_minimum (i: Fin m) : B_min ≤ B i := by
          apply Finset.min'_le _ _ (mem_image_univ_iff_mem_range.mpr (mem_range_self i))

        have index_A_max_existence : ∃ i : Fin n, A i = A_max := by
          have this : A_max ∈ (Finset.image A Finset.univ) := by
            exact Finset.max'_mem _ _

          rw [Finset.mem_image] at this
          rcases this with ⟨i, ⟨hi_left, hi_right⟩⟩
          use i

        have index_B_min_existence : ∃ i : Fin m, B i = B_min := by
          have this : B_min ∈ (Finset.image B Finset.univ) := by
            exact Finset.min'_mem _ _

          rw [Finset.mem_image] at this
          rcases this with ⟨i, ⟨hi_left, hi_right⟩⟩
          use i

        have A_max_lt_B_min : A_max < B_min := by
          rcases index_A_max_existence with ⟨index_A_max, hiA⟩
          rcases index_B_min_existence with ⟨index_B_min, hiB⟩
          apply lt_of_eq_of_lt hiA.symm
          apply lt_of_lt_of_eq _ hiB
          apply BigAnd.eliminationAtIndex (BigAnd.eliminationAtIndex h index_B_min) index_A_max

        rcases DLO.dense A_max B_min A_max_lt_B_min with ⟨middlevalue, ⟨mid_gt_A, mid_lt_B⟩⟩
        dsimp at mid_gt_A
        dsimp at mid_lt_B

        use middlevalue
        constructor
        · apply BigAnd.ofAllProven
          intro i
          exact lt_of_le_of_lt (A_max_is_maximum i) mid_gt_A

        · apply BigAnd.ofAllProven
          intro i
          exact lt_of_lt_of_le mid_lt_B (B_min_is_minimum i)


end steps

namespace formula_conversion
def to_BoundedFormula {k : ℕ} : ((n : ℕ) → (P : Fin n → Prop) → Prop) → ((m : ℕ) → (Fin m → FirstOrder.Language.BoundedFormula order_language ℝ k) → Prop) :=
  sorry
  -- (n : ℕ) → (Fin n → FirstOrder.Language.toBoundedFormula order_language ℝ k) → Prop


def to_ImpAllFreeFormula {k : ℕ} : ((n : ℕ) → (P : Fin n → FirstOrder.Language.BoundedFormula order_language ℝ k) → Prop) → ((m : ℕ) → (Fin m → FirstOrder.Language.ImpAllFreeFormula order_language ℝ k) → Prop) :=
  sorry
  -- (n : ℕ) → (Fin n → FirstOrder.Language.toImpAllFreeFormula order_language ℝ k) → Prop


end formula_conversion

open steps


def TotalExistentionalElimination {k : ℕ} : ((n : ℕ) → (P : Fin n → Prop) → Prop) → ((m : ℕ) → (Fin m → FirstOrder.Language.QFBoundedFormula order_language ℝ k) → Prop) := by
  intro f
  let f' := formula_conversion.to_ImpAllFreeFormula (k := 0) (formula_conversion.to_BoundedFormula f)
  -- Case distinction:
  --  If there is a formula of form x = y, where either x or y is an existential, use subsitution.
  --  Else, use the of_disjunction lemma.
  sorry


end existential_elimination
end Big_And_section


theorem RealDLO_admits_quantifier_elimination :


/--
The master plan
-/
instance Real_Ominimal : Ominimal ℝ order_language where
  definable_sets := by sorry
