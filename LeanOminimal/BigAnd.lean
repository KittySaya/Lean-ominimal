import LeanOminimal.Basic
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
