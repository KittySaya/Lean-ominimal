import LeanOminimal.Formula.Compatible
import LeanOminimal.intervals
import LeanOminimal.Definability.Definition


open FirstOrder
open Language
open Set


namespace Definability

/--
A proposition that states whenever a BoundedFormula can be written as a finite union of points and intervals.
-/
@[simp]
def BoundedFormula_setOf_is_FiniteUnion (ψ : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0) : Prop :=
 DLO.interval.is_finite_union_of_intervalsP ({x : ℝ | @ψ.Realize (order_language[[@univ ℝ]]) ℝ  _ _ _  (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i)})

alias Formulafiniteunion := BoundedFormula_setOf_is_FiniteUnion

/--
A QFImpAllFreeFormula is a finite union of intervals.
-/
@[simp]
theorem QFImpAllFreeFormula_setOf_is_FiniteUnion (φ : QFImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) 0 ) :
    BoundedFormula_setOf_is_FiniteUnion φ.toBoundedFormula := by

  induction' φ with a b l R ts not_formula ih_not_formula or_left or_right orl_ih orr_ih and_left and_right andr_ih andl_ih
  · unfold QFImpAllFreeFormula.toBoundedFormula
    show DLO.interval.is_finite_union_of_intervalsP ∅
    exact DLO.interval.is_finite_union_of_intervalsP.empty

  · dsimp!

    by_cases h : a = b
    · have is_entire : {x | @Term.realize (order_language[[@univ ℝ]]) ℝ _ _ (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) a = Term.realize (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) b} = univ := by
        ext x
        constructor
        · intro h₁
          exact trivial
        · intro _
          rw [Set.mem_setOf]
          rw [h]

      rw [is_entire]
      exact DLO.interval.is_finite_union_of_intervalsP.entire

    · have is_empty : {x | @Term.realize (order_language[[@univ ℝ]]) ℝ _ _ (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) a = Term.realize (Sum.elim (fun x_1 : Fin 1 ↦ x) (fun i : Fin 0 ↦ nomatch i)) b} = ∅ := by
        ext x
        constructor
        · intro h₁
          rw [Set.mem_setOf] at h₁
          exfalso
          apply h
          clear h
          simp [h₁]
          -- rw [<- BoundedFormula.realize_bdEqual] at h₁
          -- simp at h₁

          sorry --!!!
        · intro h₁
          exfalso
          exact h₁

      rw [is_empty]
      exact DLO.interval.is_finite_union_of_intervalsP.empty

  · unfold QFImpAllFreeFormula.toBoundedFormula

    by_cases h : l = 2
    · subst h
      let a := ts 0
      let b := ts 1
      -- have {x : ℝ} : (BoundedFormula.rel R ts).Realize (fun x_1 ↦ x) (fun i : Fin 0 ↦ nomatch i) ↔ a < b := by
        -- sorry
      simp!
      unfold Structure.RelMap
      sorry -- !!!
    · exfalso
      have : IsEmpty (order_language[[@univ ℝ]].Relations l) := by
        exact rel2empty h
      exact IsEmpty.false R


  · unfold QFImpAllFreeFormula.toBoundedFormula
    have this : {x : ℝ | (∼not_formula.toBoundedFormula).Realize (fun x_1 : Fin 1 ↦ x) fun i ↦ nomatch i} = {x | (not_formula.toBoundedFormula).Realize (fun x_1 ↦ x) fun i ↦ nomatch i}ᶜ := by
      exact rfl

    dsimp
    rw [this]
    apply DLO.interval.is_finite_union_of_intervalsP.complement
    assumption


  · unfold QFImpAllFreeFormula.toBoundedFormula
    have this : {x : ℝ | (or_left.toBoundedFormula ⊔ or_right.toBoundedFormula).Realize (fun x_1 ↦ x) fun i ↦ nomatch i} =
                 {x | or_left.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} ∪ {x | or_right.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := by
      ext x
      rw [mem_union]
      repeat rw [mem_setOf]
      exact BoundedFormula.realize_sup

    dsimp
    rw [this]
    apply DLO.interval.is_finite_union_of_intervalsP.union
    assumption'


  · unfold QFImpAllFreeFormula.toBoundedFormula
    have this : {x : ℝ | (and_left.toBoundedFormula ⊓ and_right.toBoundedFormula).Realize (fun x_1 ↦ x) fun i ↦ nomatch i} =
                 {x | and_left.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} ∩ {x | and_right.toBoundedFormula.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := by
      ext x
      rw [mem_inter_iff]
      repeat rw [mem_setOf]
      exact BoundedFormula.realize_inf

    dsimp
    rw [this]
    apply DLO.interval.is_finite_union_of_intervalsP.intersection
    assumption'

alias QFimpAllFreeFormulafiniteunion := QFImpAllFreeFormula_setOf_is_FiniteUnion

/--
Two formulas that are true precisely if the other is true define a finite union of intervals precisely when the other one does.
-/
lemma formulaequiv (φ ψ : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 ) : (∀ x:ℝ,  ψ.Realize (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i) ↔ φ.Realize (fun _: Fin 1=> x) (fun i:Fin 0 => nomatch i)) → (Formulafiniteunion φ ↔ Formulafiniteunion ψ) := by
  intro hyp
  unfold Formulafiniteunion at *

  have : {x | φ.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} =
         {x | ψ.Realize (fun x_1 ↦ x) fun i ↦ nomatch i} := ext (fun x ↦ (hyp x).symm)

  constructor
  · intro phi
    dsimp
    rw [← this]
    exact phi
  · intro psi
    dsimp
    rw [this]
    exact psi

/--
Type coercion from a Formula to a BoundedFormula.
-/
def Formula_to_BoundedFormula  (φ : Formula (order_language[[@univ ℝ]]) (Fin 1)  ) : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 :=
  (by simp : BoundedFormula (order_language[[@univ ℝ]]) (Fin 1) 0 = Formula (order_language[[@univ ℝ]]) (Fin 1)) ▸ φ

alias Formulaisbounded := Formula_to_BoundedFormula

/--
Every set that is definable in the Language `(ℝ, <)` is a finite union of intervals.
-/
theorem definable_sets_are_finite_unions : ∀U : Set ℝ, isDefinable order_language U → DLO.interval.is_finite_union_of_intervalsP U := by
  intro U is_def_U
  rcases is_def_U with ⟨φ', set_eq⟩

  let φ := Formula_to_BoundedFormula φ'
  let ψ := QFImpAllFreeFormula.toBoundedFormula ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)

  have ψfin : BoundedFormula_setOf_is_FiniteUnion ψ :=
      QFImpAllFreeFormula_setOf_is_FiniteUnion ((BoundedFormula.toImpAllFreeFormula φ).toQFImpAllFreeFormula)


  have φfin : BoundedFormula_setOf_is_FiniteUnion φ :=
    ((formulaequiv ψ φ (compatible₂ φ))).mp ψfin

  unfold BoundedFormula_setOf_is_FiniteUnion at φfin
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

end Definability
