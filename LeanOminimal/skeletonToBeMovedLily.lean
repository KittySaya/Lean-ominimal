import Mathlib
import LeanOminimal.intervals
import LeanOminimal.Definability.Definition
open FirstOrder
section order_definition



section definability
open Set
open Language

--- All inclusions of types:






-- Docstring missing
def varelimAtomicblock {n} (i: Fin 1 ⊕ Fin (n+1) ) (ter : order_language[[@univ ℝ]].Term (Fin 1 ⊕ Fin n)): Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) →  Relblock (order_language[[@univ ℝ]]) (Fin 1) n:= by
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

  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
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

  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
  apply F_empty.elim'
  apply g

  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
  apply F_empty.elim'
  apply h
  have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
  apply F_empty.elim'
  apply R


  exact (varelimAtomicblock i ter t1).and (varelimAtomicblock i ter t1)




-- Docstring missing
def Atomicblock.toRelblock {n} : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → Relblock (order_language[[@univ ℝ]]) (Fin 1) n
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

        have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
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

            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
            apply F_empty.elim'
            apply g

        · have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
          apply F_empty.elim'
          apply h

    · have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
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

  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := func0empty neq
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

  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply g

  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := func0empty neq
  -- apply F_empty.elim'
  -- apply h

  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= rel2empty neq
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
  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l)  := func0empty neq2
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


  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply g
  -- have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := func0empty neq2
  -- apply F_empty.elim'
  -- apply h

  -- rename_i a l R f
  -- exact (Atomicblock.rel R f).toRelblock.and a.toRelblock
  -- rename_i a1 a2 a3
  -- exact (a1.toRelblock.and a2.toRelblock).and a3.toRelblock


-- Docstring missing
def Existblock.todisjunctionAtomicblocks {n : ℕ} : Existblock (order_language[[@univ ℝ]]) (Fin 1) n → disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | lit l     => l.todisjunctionAtomicblocks
  | and e₁ e₂ => e₁.todisjunctionAtomicblocks.and e₂.todisjunctionAtomicblocks
  -- intro block
  -- rcases block with ⟨ l⟩ | ⟨l1, l2 ⟩
  -- exact l.todisjunctionAtomicblocks
  -- exact l1.todisjunctionAtomicblocks.and l2.todisjunctionAtomicblocks


-- Docstring missing
def disjunctionAtomicblocks.todisjunctionRelblocks {n} : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | atom a   => disjunctionRelblocks.relb (Atomicblock.toRelblock a)
  | or f₁ f₂ => disjunctionRelblocks.or (f₁.todisjunctionRelblocks) (f₂.todisjunctionRelblocks)

  -- intro disA
  -- rcases disA with ⟨atom ⟩ | ⟨d1, d2 ⟩
  -- exact (disjunctionRelblocks.relb (Atomicblock.toRelblock atom))
  -- exact disjunctionRelblocks.or (d1.todisjunctionRelblocks) (d2.todisjunctionRelblocks)


-- Docstring missing
def Existblock.todisjunctionRelblocks {n} : Existblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) n :=
  fun a => a.todisjunctionAtomicblocks.todisjunctionRelblocks








/--
Proves that the Realize of an existblock equals that of the realize by mapping it to a bounded formula.
-/
@[simp]
lemma Existblock.Realize_equiv {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Existblock L α (l + 1)) (v : α → M) (xs : Fin l → M) : φ.Realize v xs ↔ φ.toImpAllFreeFormula.toBoundedFormula.Realize v xs := by
  rfl

-- Docstring missing
def Relblock.Realize {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Relblock L α l) (v : α → M) (xs : Fin l → M) : Prop :=
  φ.toBoundedFormula.Realize v xs

-- Docstring missing
@[simp]
lemma Relblock.Realize_equiv {L : Language} {α : Type} {M} [L.Structure M] {l} (φ : Relblock L α l) (v : α → M) (xs : Fin l → M) : φ.Realize v xs ↔ φ.toBoundedFormula.Realize v xs := by
  rfl

-- Docstring missing
def disjunctionAtomicblocks.RealRealize (φ : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) 1) (x: Fin 1 → ℝ ) : Prop :=
  φ.todisjunctionRelblocks.toBoundedFormula.Realize x (fun i : (Fin 0) => nomatch i)

-- Docstring missing
@[simp]
lemma disjunctionAtomicblocks.RealRealize_equiv (φ : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) 1) (x : Fin 1 → ℝ) : φ.RealRealize x ↔ φ.todisjunctionRelblocks.toBoundedFormula.Realize x (fun i : (Fin 0) => nomatch i) := by
  rfl


-- Docstring missing
def disjunctionRelblocks.todisjunctionExistblocks {L} {α} {n}: disjunctionRelblocks L α n → disjunctionExistblocks L α n := by
  sorry

-- Docstring missing
@[simp]
def disjunctionExistblocks.elim  {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | existbl eb => eb.todisjunctionRelblocks.todisjunctionExistblocks
  | or f₁ f₂ => f₁.elim.or f₂.elim
  -- intro existbl
  -- rcases existbl with ⟨ ex⟩ | ⟨ex1,ex2⟩
  -- exact ex.todisjunctionRelblocks.todisjunctionExistblocks
  -- exact ex1.elim.or ex2.elim

-- Docstring missing
def notExistblockelim {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n):= by
  intro exbl
  rcases exbl with ⟨ exbl⟩ | ⟨ex1,ex2⟩

  rcases exbl with ⟨lit ⟩

  exact (disjunctionExistblocks.existbl (Existblock.lit lit )).elim
  rename_i ex1 ex2
  exact (notExistblockelim (disjunctionExistblocks.existbl ex1)).or (notExistblockelim (disjunctionExistblocks.existbl ex1))

  exact (notExistblockelim ex1).and (notExistblockelim ex2)


-- Docstring missing
def disjunctionExistblocks.toQFImpAllFreeFormula  {L} {α} {n}: disjunctionExistblocks L α n→ QFImpAllFreeFormula L α n:= by
  sorry

-- Docstring missing
def ImpAllFreeFormula.toQFImpAllFreeFormula  {n:ℕ } : ImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) (n) → QFImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) n:=
  let rec helper {n} : ImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) n →
      disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) n
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




-- Docstring missing
@[simp]
lemma compatible2 (φ : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 ) :
∀x:ℝ ,φ.Realize (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i)
 ↔ (QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)).Realize
    (fun i: Fin 1=> x) (fun i:Fin 0 => nomatch i) := by sorry -- Later




@[simp]


-- Docstring missing
-- Joos
lemma formulaequiv (φ ψ : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0) :
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

--moved to Definability.Left
-- Docstring missing
def Formulaisbounded  (φ : Formula (order_language[[@univ ℝ]]) (Fin 1)  ) : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 :=
  (by simp : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 = Formula (order_language[[@univ ℝ]]) (Fin 1)) ▸ φ

--moved to Definability.Left
/--
Every set that is definable in the Language `(ℝ, <)` is a finite union of intervals.
-/
theorem definable_sets_left : ∀U : Set ℝ, isDefinable order_language U → DLO.interval.is_finite_union_of_intervalsP U := by
  intro U is_def_U
  rcases is_def_U with ⟨φ', set_eq⟩

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
        apply set_eq.mp xf_in_setU

      rw [mem_setOf]
      rw [mem_setOf] at xf_in_setOf_φRealize
      exact (Formula.boundedFormula_realize_eq_realize φ (fun x_1 ↦ x) fun i ↦ nomatch i).mpr xf_in_setOf_φRealize

    · intro h
      show xf ∈ {x | x 0 ∈ U} --Suprised this works tbh. -Lily
      rw [mem_setOf] at h
      apply set_eq.mpr
      rw [mem_setOf]
      exact (Formula.boundedFormula_realize_eq_realize φ (fun x_1 ↦ x) fun i ↦ nomatch i).mp h

  rw [seteq]
  exact φfin
