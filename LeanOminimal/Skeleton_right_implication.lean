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
  Definable₁ (Set.univ : Set X ) L U

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

inductive ImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n : ℕ} : ImpAllFreeFormula L α n
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  | not    {n : ℕ}   (f     : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | or     {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | and    {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | exists {n : ℕ}   (f : ImpAllFreeFormula L α (n + 1)) : ImpAllFreeFormula L α n

inductive QFImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n : ℕ} : QFImpAllFreeFormula L α n
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFImpAllFreeFormula L α n
  | not    {n : ℕ}   (f     : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n
  | or     {n : ℕ}   (f₁ f₂ : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n
  | and    {n : ℕ}   (f₁ f₂ : QFImpAllFreeFormula L α n) : QFImpAllFreeFormula L α n


inductive Literal (L : Language) (α : Type) (n : ℕ) : Type _
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Literal L α n
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Literal L α n
  | not (f : Literal L α n) : Literal L α n

inductive Existblock (L : Language) (α : Type) (m : ℕ) : Type _
| lit (l: Literal L α m) : Existblock L α m
| and (l1 l2: Literal L α m) : Existblock L α m



inductive Atomicblock (L : Language) (α : Type) : ℕ → Type _
  | truth {n} : Atomicblock L α n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Atomicblock L α n
  | rel   {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Atomicblock L α n
  | and   {n : ℕ} (f1 f2 : Atomicblock L α n) : Atomicblock L α n


inductive disjunctionAtomicblocks (L : Language)  (α : Type) : ℕ → Type _
| atom  {m:ℕ } (a:Atomicblock L α m): disjunctionAtomicblocks L α m
| or {m:ℕ } (  f1 f2 :disjunctionAtomicblocks L α m ): disjunctionAtomicblocks L α m


inductive Relblock (L : Language) (α : Type) : ℕ → Type _
  | truth {n} : Relblock L α n
  | rel   {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Relblock L α n
  | and   {n : ℕ} (f1 f2 : Relblock L α n) : Relblock L α n

inductive disjunctionRelblocks (L : Language)  (α : Type) : ℕ → Type _
| relb  {m:ℕ } (r: Relblock L α m): disjunctionRelblocks L α m
| or {m:ℕ } (f1 f2 :disjunctionRelblocks L α m ): disjunctionRelblocks L α m


--- All inclusions of types:
def QFImpAllFreeFormula.toImpAllFreeFormula {L} {α} {n}: QFImpAllFreeFormula L α n→ ImpAllFreeFormula L α n
| .falsum => .falsum
| .equal t₁ t₂ => .equal t₁ t₂
| .rel R ts => .rel R ts
| .not f => (QFImpAllFreeFormula.toImpAllFreeFormula f).not
| .or  f₁ f₂  => (QFImpAllFreeFormula.toImpAllFreeFormula f₁).or (QFImpAllFreeFormula.toImpAllFreeFormula f₂)
| .and f₁ f₂  => (QFImpAllFreeFormula.toImpAllFreeFormula f₁).and (QFImpAllFreeFormula.toImpAllFreeFormula f₂)



def BoundedFormula.toImpAllFreeFormula {L : Language} {α : Type} {n : ℕ} : BoundedFormula L α n → ImpAllFreeFormula L α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .imp f₁ f₂ => ((BoundedFormula.toImpAllFreeFormula f₁).not).or (BoundedFormula.toImpAllFreeFormula f₂)
  | .all f => (((BoundedFormula.toImpAllFreeFormula f).not).exists).not


def Literal.toImpAllFreeFormula {L} {α} {n} : Literal L α n → ImpAllFreeFormula L α n

  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => .not f.toImpAllFreeFormula
def Atomicblock.toImpAllFreeFormula {L} {α} {n} : (Atomicblock L α n) → ImpAllFreeFormula L α n

  | .truth  => ImpAllFreeFormula.falsum.not
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel   R ts => .rel R ts
  | .and   f₁ f₂ => f₁.toImpAllFreeFormula.and f₂.toImpAllFreeFormula
def Atomicblock.todisjunctionAtomicblocks {m : ℕ}{L} {α} (a: Atomicblock L α m) :  disjunctionAtomicblocks L α m  :=
disjunctionAtomicblocks.atom a

def Relblock.toBoundedFormula {L} {α} {n}: Relblock L α n→ BoundedFormula L α n
 | truth => BoundedFormula.falsum.imp BoundedFormula.falsum
 | .rel R ts => .rel R ts
 | .and t1 t2 => (t1.toBoundedFormula.imp (t2.toBoundedFormula.imp BoundedFormula.falsum)).imp BoundedFormula.falsum

def disjunctionRelblocks.toBoundedFormula {L} {α} {n}: disjunctionRelblocks L α n→ BoundedFormula L α n := by
  intro disj
  rcases disj with ⟨ ⟩ | ⟨ rel, dis⟩
  exact BoundedFormula.falsum
  exact (rel.toBoundedFormula.imp BoundedFormula.falsum).imp dis.toBoundedFormula

def Existblock.toImpAllFreeFormula {L} {α} {n}: Existblock L α n→ ImpAllFreeFormula L α n:= by sorry -- Joos

def ImpAllFreeFormula.toBoundedFormula {L} {α} {n} : ImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => (f.toBoundedFormula).not -- (f.toBounded).imp .falsum
  | .or f₁ f₂ => BoundedFormula.imp (f₁.toBoundedFormula.not) f₂.toBoundedFormula -- ((f₁.not).toBounded).imp f₂.toBounded
  | .and f₁ f₂ => (BoundedFormula.imp f₁.toBoundedFormula f₂.toBoundedFormula.not).not -- ((f₁.not).or (f₂.not).not).toBounded
  | .exists f => (f.toBoundedFormula).ex-- (((f.toBounded).not).all).not

def QFImpAllFreeFormula.toBoundedFormula {L} {α} {n}: QFImpAllFreeFormula L α n→ BoundedFormula L α n:= by sorry -- Joos

-- disjunction and conjuction of disjunctionofatomicblocks


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



def Literal.todisjunctionAtomicblocks {n:ℕ }(l : Literal (order_language[[ℝ]]) (Fin 1) n) : disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) n := by
 rcases l with ⟨t1 ,t2⟩ | ⟨R, f⟩ | ⟨t1, t2⟩ | ⟨R, f⟩ | f


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

 have F_empty : order_language[[ℝ]].Functions l = Empty := by
    have is_empty : IsEmpty (order_language[[ℝ]].Functions l) := by
      unfold withConstants
      unfold Language.sum
      simp only [order_language, constantsOn_Functions, constantsOnFunc, isEmpty_sum]
      constructor
      · exact Empty.instIsEmpty
      · have l_pred : ∃p : ℕ, p.succ = l := by
          refine Nat.exists_add_one_eq.mpr ?_
          exact Nat.zero_lt_of_ne_zero neq
        rcases l_pred with ⟨l₁, hl⟩
        subst hl
        dsimp
        exact PEmpty.instIsEmpty

    have eq_empty_iff_is_empty {t : Type} : IsEmpty t ↔ t = Empty := by
      constructor
      · intro h
        sorry
      · intro h
        subst h
        exact Empty.instIsEmpty


    apply eq_empty_iff_is_empty.mp
    exact is_empty
    -- Lily

 rw[F_empty] at g
 exact g.elim

 rename_i l


 by_cases neq : l=0
 rw [neq] at f t1
 let const1 := Term.func f t1
 let QF:= Atomicblock.equal const1 t2
 exact QF.todisjunctionAtomicblocks

 have F_empty : order_language[[ℝ]].Functions l = Empty := by sorry -- Lily
 rw [F_empty] at f
 exact f.elim
 let QF :=  Atomicblock.rel R f
 exact QF.todisjunctionAtomicblocks

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
 have R_empty : order_language[[ℝ]].Relations l = Empty := by sorry -- Lily


 rw [R_empty] at R
 exact R.elim
 exact f.todisjunctionAtomicblocks


def Existblock.todisjunctionAtomicblocks {n:ℕ } (block : Existblock (order_language[[ℝ]]) (Fin 1) n ) : disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) n:= by
 rcases block with ⟨ l⟩ | ⟨l1, l2 ⟩
 exact l.todisjunctionAtomicblocks
 exact l1.todisjunctionAtomicblocks.and l2.todisjunctionAtomicblocks



def Atomicblock.toRelblock  (block : Atomicblock (order_language[[ℝ]]) (Fin 1) (1)) : Relblock (order_language[[ℝ]]) (Fin 1) 0 := by sorry -- Niels

def disjunctionAtomicblocks.todisjunctionRelblocks :disjunctionAtomicblocks (order_language[[ℝ]]) (Fin 1) (1)→ disjunctionRelblocks (order_language[[ℝ]]) (Fin 1) (0):= by
intro disA
rcases disA with ⟨atom ⟩ | ⟨d1, d2 ⟩
exact (disjunctionRelblocks.relb (Atomicblock.toRelblock atom))

exact disjunctionRelblocks.or (d1.todisjunctionRelblocks) (d2.todisjunctionRelblocks)

@[simp]
lemma compatible (block: Existblock (order_language[[ℝ]]) (Fin 1) (1)) (x: Fin 1→ ℝ ) :
  (block.toImpAllFreeFormula.exists).toBoundedFormula.Realize x (fun i:(Fin 0) => nomatch i)
   ↔ @block.todisjunctionAtomicblocks.todisjunctionRelblocks.toBoundedFormula.Realize (order_language[[ℝ]]) ℝ  _ _ _  x (fun i:Fin 0 => nomatch i) := by sorry -- Lily

@[simp]
def ImpAllFreeFormula.toQFImpAllFreeFormula  : ImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) 0 → QFImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) 0:= by sorry -- Joos

@[simp]
lemma compatible2  (φ : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 ) :
∀x:ℝ ,φ.Realize (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i)
 ↔ (QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)).Realize
    (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i) := by sorry -- Later



@[simp]
def Formulafiniteunion (ψ : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 ): Prop :=
 @DLO.interval.is_finite_union_of_intervalsP ℝ _
  ({ x:ℝ   | @ψ.Realize (order_language[[ℝ]]) ℝ  _ _ _  (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i)  } )

@[simp]
lemma QFimpAllFreeFormulafiniteunion (φ :QFImpAllFreeFormula (order_language[[ℝ]]) (Fin 1) 0 ):
    Formulafiniteunion φ.toBoundedFormula := by
  unfold Formulafiniteunion
  induction' φ with a b c d e f g h i j k l m n o p q r s t u v w x y z
  · unfold QFImpAllFreeFormula.toBoundedFormula

    sorry
  repeat1' sorry -- Lily

@[simp]



lemma formulaequiv (φ ψ : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 ):
(∀ x:ℝ,  ψ.Realize (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i) ↔ φ.Realize (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i)) → (Formulafiniteunion φ ↔ Formulafiniteunion ψ) := by sorry -- Joos


def Formulaisbounded  (φ : Formula (order_language[[ℝ]]) (Fin 1)  ) : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0 :=
  (by simp : BoundedFormula (order_language[[ℝ]]) (Fin 1) 0  =Formula (order_language[[ℝ]]) (Fin 1)  ) ▸ φ


theorem definable_sets_left:  ∀ (U: Set (ℝ )), isDefinable order_language U  → DLO.interval.is_finite_union_of_intervalsP U:= by
intro u def_u
rcases def_u with ⟨φ', set_eq  ⟩

have langhom: order_language[[@univ ℝ]] = order_language[[ℝ]] := by sorry -- donderdag Johan

rw [langhom] at φ'

let φ := Formulaisbounded φ'
let ψ := QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)

have ψfin : Formulafiniteunion ψ :=
    QFimpAllFreeFormulafiniteunion ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)


have φfin : Formulafiniteunion φ := ((formulaequiv  ψ φ  (compatible2 φ))).1 ψfin

unfold Formulafiniteunion at φfin
have  seteq :u = {x | φ.Realize (fun x_1 ↦ x) fun i ↦ nomatch i}:=by sorry --
rw[seteq]
exact φfin
