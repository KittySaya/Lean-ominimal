import LeanOminimal.DLO

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
