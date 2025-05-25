import LeanOminimal.Basic
import LeanOminimal.DLO

-- NOTE - LIKELY DEPRECATED

open FirstOrder
open Language

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

/--
For an `n : ℕ`, if `P : Fin n → Prop` is a formula, such that for any `i ∈ Fin n`,
the proposition `P i` is proven, then `BigAnd n P` holds
-/
@[simp]
lemma ofAllProven (n : ℕ) (P : Fin n → Prop) (all_proven : ∀ i : Fin n, P i) : BigAnd n P := by
  have P_is_essentially_truth_function : P = fun _ => True := by
    ext i
    exact iff_true_intro (all_proven i)
  subst P_is_essentially_truth_function
  exact BigAnd.ofAllTrue n

/--
For a natural number `n`, a function `P : Fin n → Prop`,
if `BigAnd n P` holds, then for any `i : Fin n`, `P i` holds.
-/
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


open Set

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


  · have nonempty_finset_of_nezero {k : ℕ} (k_nonzero : ¬(k = 0)) : Nonempty (Fin k) := by
      refine Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero k_nonzero)

    intro h
    by_cases n_val : n = 0
    · subst n_val
      by_cases m_val : m = 0
      · subst m_val
        use 2.71828182846 * 3.14159
        exact ⟨BigAnd.ofEmpty _, BigAnd.ofEmpty _⟩

      · -- let B_min := Finset.inf' (Finset.image B Finset.univ) (by simp [nonempty_finset_of_nezero, m_val]) id
        let B_min := Finset.min' (Finset.image B Finset.univ) (by simp [nonempty_finset_of_nezero, m_val])

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
