import LeanOminimal.DLO
open FirstOrder
open Set

namespace DLO.interval

variable {X : Type} [DLO X]

omit [DLO X] in
theorem eqCompl_of_entireUnion_of_emptyIntersection {U V : Set X} (entireUnion : U ∪ V = univ) (emptyIntersection : U ∩ V = ∅) : U = Vᶜ := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    show x ∉ V
    by_contra h'x
    apply Set.not_mem_empty x
    rw [<- emptyIntersection]
    trivial
  · refine compl_subset_iff_union.mpr ?_
    rw [Set.union_comm]
    assumption

/--
The interval `(a, b)`.
-/
@[simp]
def bounded (a b : X ): Set X :=
  { x:X | a<₀x ∧ x<₀b }

/--
The interval `(a, →)`.
-/
@[simp]
def lower (a : X): Set X :=
  { x:X | a<₀x }

/--
The interval `(←, b)`.
-/
@[simp]
def upper (b : X): Set X :=
  { x:X | x<₀b }

/--
The interval `[a, a]`, i.e., the interval set `{a}`.
-/
@[simp]
def singleton (a : X): Set X :=
  { x:X | x=a}


@[simp]
lemma mem_bounded_iff {a b : X} (x : X) : x ∈ bounded a b ↔ a<₀x ∧ x<₀b := by
  exact mem_def

@[simp]
lemma mem_lower_iff {a : X} (x : X) : x ∈ lower a ↔ a<₀x := by
  exact mem_def

@[simp]
lemma mem_upper_iff {b : X} (x : X) : x ∈ upper b ↔ x<₀b := by
  exact mem_def

omit [DLO X] in
@[simp]
lemma mem_singleton_iff {a : X} (x : X) : x ∈ singleton a ↔ x = a := by
  exact mem_def

/--
This property expresses the fact that a subset of X is a finite union of (open) intervals or singletons.
-/
inductive is_finite_union_of_intervalsP : Set X → Prop where
  | empty   : is_finite_union_of_intervalsP ∅
  | bounded : (a : X) → (b : X) → is_finite_union_of_intervalsP (bounded a b)
  | lower   : (a : X) → is_finite_union_of_intervalsP (lower a)
  | upper   : (a : X) → is_finite_union_of_intervalsP (upper a)
  | point   : (a : X) → is_finite_union_of_intervalsP (singleton a)
  | union   : ∀ U V : Set X, is_finite_union_of_intervalsP U → is_finite_union_of_intervalsP V → is_finite_union_of_intervalsP (U ∪ V)


/--
The entire set is a finite union of intervals.
-/
@[simp]
lemma is_finite_union_of_intervalsP.entire : is_finite_union_of_intervalsP (@univ X : Set X) := by
  by_cases inhabited_X : ∃x : X, True
  · rcases inhabited_X with ⟨x, _⟩
    let x_lower := interval.lower x
    let x_single := interval.singleton x
    let x_upper := interval.upper x

    let x_full := x_lower ∪ x_single ∪ x_upper
    have x_full_is_univ : x_full = univ := by
      ext t
      apply iff_of_true
      · rcases DLO.total x t with less | equal | more
        · have t_in_lower : t ∈ x_lower := by
            exact less
          apply Set.mem_union_left
          apply Set.mem_union_left
          assumption
        · have t_in_single : t ∈ x_single := by
            exact equal.symm
          apply Set.mem_union_left
          apply Set.mem_union_right
          assumption
        · have t_in_upper : t ∈ x_upper := by
            exact more
          apply Set.mem_union_right
          assumption
      · expose_names
        exact h

    rw [<- x_full_is_univ]
    apply is_finite_union_of_intervalsP.union
    · apply is_finite_union_of_intervalsP.union
      · exact is_finite_union_of_intervalsP.lower x
      · exact is_finite_union_of_intervalsP.point x
    · exact is_finite_union_of_intervalsP.upper x

  · have empty_is_univ : (∅ : Set X) = univ := by
      ext x
      constructor
      · intro h
        exfalso
        exact h
      · intro h
        exfalso
        have contradiction : ∃ x : X, True := by
          use x
        contradiction
    rw [<- empty_is_univ]
    exact empty


/--
Given two finite union of intervals `U` and `V`, their intersection
`U ∩ V` is also a finite union of intervals.
-/
@[simp]
lemma is_finite_union_of_intervalsP.intersection {U V : Set X} (hU : is_finite_union_of_intervalsP U) (hV : is_finite_union_of_intervalsP V) : is_finite_union_of_intervalsP (U ∩ V) := by
  have point_right {c : X} {U : Set X} : is_finite_union_of_intervalsP (U ∩ singleton c) := by
    by_cases h : c ∈ U
    · have : U ∩ singleton c = singleton c := by
        refine inter_eq_right.mpr ?_
        intro x hx
        rw [mem_singleton_iff] at hx
        subst hx
        assumption
      rw [this]
      exact point c

    · have : U ∩ singleton c = ∅ := by
        refine Disjoint.inter_eq ?_
        exact disjoint_singleton_right.mpr h
      rw [this]
      exact empty

  induction' hU with a b a a a U₁ U₂ hU₁ hU₂ U₁_ih U₂_ih
  · rw [empty_inter V]
    exact is_finite_union_of_intervalsP.empty

  case point =>
    by_cases h : a ∈ V
    · have : singleton a ∩ V = singleton a := by
        refine inter_eq_left.mpr ?_
        intro x hx
        rw [mem_singleton_iff] at hx
        subst hx
        assumption
      rw [this]
      exact point a

    · have : singleton a ∩ V = ∅ := by
        refine Disjoint.inter_eq ?_
        exact disjoint_singleton_left.mpr h
      rw [this]
      exact empty

  case union =>
    rw [union_inter_distrib_right]
    apply union
    assumption'

  repeat' induction' hV with c d c c c V₁ V₂ hV₁ hV₂ V₁_ih V₂_ih
  repeat' case empty =>
    rw [inter_empty]
    exact is_finite_union_of_intervalsP.empty

  repeat' case point =>
    apply point_right

  repeat' case union =>
    rw [inter_union_distrib_left]
    apply union
    assumption'

  · rcases DLO.total a c with ac_less | ac_eq | ac_more
    · have this : interval.bounded a b ∩ interval.bounded c d = interval.bounded c b ∩ interval.bounded c d := by
        refine inter_congr_right ?_ ?_
        · intro x hx
          rw [mem_inter_iff] at hx
          repeat rw [mem_bounded_iff] at *
          rcases hx with ⟨⟨c_lt, lt_b⟩, ⟨c_lt, lt_d⟩⟩
          constructor
          · apply DLO.trans a c x
            assumption'
          · assumption
        · intro x hx
          rw [mem_inter_iff] at hx
          repeat rw [mem_bounded_iff] at *
          rcases hx with ⟨⟨a_lt, lt_b⟩, ⟨c_lt, lt_d⟩⟩
          trivial

      rw [this]
      rcases DLO.total b d with bd_less | bd_eq | bd_more
      · have thiss : interval.bounded c b ∩ interval.bounded c d = interval.bounded c b := by
          refine inter_eq_left.mpr ?_
          intro x hx
          repeat rw [mem_bounded_iff] at *
          rcases hx with ⟨c_lt, lt_b⟩
          constructor
          · assumption
          · apply DLO.trans x b d
            assumption'

        rw [thiss]
        exact bounded c b

      repeat1' sorry

    repeat1' sorry

  repeat1' sorry
  -- The statement is largely obvious but tedious to implement.
  -- Unless either of you is keen on proving all 30 different cases.
  -- The other strategy is to proof it works for complement, and use
  -- (U ∩ V) = (U ∩ V)ᶜᶜ = (Uᶜ ∪ Vᶜ)ᶜ
  -- And use; it holds for U and V, so for Uᶜ and Vᶜ, so for their union, so for their complement.
  -- But I couldn't find a way to prove it holds for the complement of a union
  -- without proving it holds for an intersection.



/--
Given a finite union of intervals `U`, their complement
`Uᶜ` is also a finite union of intervals.
-/
@[simp]
lemma is_finite_union_of_intervalsP.complement {U : Set X} (hU : is_finite_union_of_intervalsP U) : is_finite_union_of_intervalsP Uᶜ := by
  induction' hU with a b a a a V W hV hU V_ih W_ih
  · rw [compl_empty]
    exact is_finite_union_of_intervalsP.entire


  · let a_singleton := interval.singleton a
    let a_upper     := interval.upper     a
    let b_singleton := interval.singleton b
    let b_lower     := interval.lower     b

    let combi := a_upper ∪ a_singleton ∪ b_singleton ∪ b_lower

    have this : combi = (interval.bounded a b)ᶜ := by
      have union_is_univ : (interval.bounded a b) ∪ combi = univ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          show x ∈ (interval.bounded a b) ∨ x ∈ combi
          rcases DLO.total x a with a_less | a_equal | a_more
          · right
            unfold combi
            apply Set.mem_union_left
            apply Set.mem_union_left
            apply Set.mem_union_left
            exact a_less

          · right
            unfold combi
            apply Set.mem_union_left
            apply Set.mem_union_left
            apply Set.mem_union_right
            exact a_equal

          · rcases DLO.total x b with b_less | b_equal | b_more
            · left
              rw [mem_bounded_iff]
              trivial

            · right
              unfold combi
              apply Set.mem_union_left
              apply Set.mem_union_right
              exact b_equal

            · right
              unfold combi
              apply Set.mem_union_right
              exact b_more

      have intersection_is_empty : (interval.bounded a b) ∩ combi = ∅ := by
        ext x
        constructor
        · intro ⟨in_bounded, in_combi⟩
          exfalso
          rw [mem_bounded_iff] at in_bounded
          rcases in_combi with ((h_ahigh | h_asing) | h_bsing) | h_blow
          · rw [mem_upper_iff x] at h_ahigh
            apply DLO.asymm x a
            exact And.imp_left (fun a ↦ h_ahigh) (id (And.symm in_bounded))
          · rw [mem_singleton_iff x] at h_asing
            apply DLO.irrefl x
            subst h_asing
            exact in_bounded.left
          · rw [mem_singleton_iff x] at h_bsing
            apply DLO.irrefl x
            subst h_bsing
            exact in_bounded.right
          · rw [mem_lower_iff x] at h_blow
            apply DLO.asymm x b
            exact And.symm (And.imp_left (fun a ↦ h_blow) in_bounded)

        · intro hx
          exfalso
          trivial

      apply eqCompl_of_entireUnion_of_emptyIntersection
      · rw [Set.union_comm]
        assumption
      · rw [Set.inter_comm]
        assumption

    rw [<- this]
    apply is_finite_union_of_intervalsP.union
    apply is_finite_union_of_intervalsP.union
    apply is_finite_union_of_intervalsP.union
    exact upper a
    exact point a
    exact point b
    exact lower b


  · let a_singleton := interval.singleton a
    let a_upper     := interval.upper     a

    let combi := a_upper ∪ a_singleton

    have this : combi = (interval.lower a)ᶜ := by
      have union_is_univ : (interval.lower a) ∪ combi = univ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          show x ∈ (interval.lower a) ∨ x ∈ combi
          rcases DLO.total x a with a_less | a_equal | a_more
          · right
            unfold combi
            apply Set.mem_union_left
            exact a_less

          · right
            unfold combi
            apply Set.mem_union_right
            exact a_equal

          · left
            rw [mem_lower_iff]
            trivial

      have intersection_is_empty : (interval.lower a) ∩ combi = ∅ := by
        ext x
        constructor
        · intro ⟨in_lower, in_combi⟩
          exfalso
          rw [mem_lower_iff] at in_lower
          rcases in_combi with (h_ahigh | h_asing)
          · rw [mem_upper_iff x] at h_ahigh
            apply DLO.asymm x a
            exact ⟨h_ahigh, in_lower⟩
          · rw [mem_singleton_iff x] at h_asing
            apply DLO.irrefl x
            subst h_asing
            exact in_lower

        · intro hx
          exfalso
          trivial

      apply eqCompl_of_entireUnion_of_emptyIntersection
      · rw [Set.union_comm]
        assumption
      · rw [Set.inter_comm]
        assumption

    rw [<- this]
    apply is_finite_union_of_intervalsP.union
    exact upper a
    exact point a


  · let a_singleton := interval.singleton a
    let a_lower     := interval.lower     a

    let combi := a_lower ∪ a_singleton

    have this : combi = (interval.upper a)ᶜ := by
      have union_is_univ : (interval.upper a) ∪ combi = univ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          show x ∈ (interval.upper a) ∨ x ∈ combi
          rcases DLO.total x a with a_less | a_equal | a_more
          · left
            rw [mem_upper_iff]
            trivial

          · right
            unfold combi
            apply Set.mem_union_right
            exact a_equal

          · right
            unfold combi
            apply Set.mem_union_left
            assumption

      have intersection_is_empty : (interval.upper a) ∩ combi = ∅ := by
        ext x
        constructor
        · intro ⟨in_upper, in_combi⟩
          exfalso
          rw [mem_upper_iff] at in_upper
          rcases in_combi with (h_ahigh | h_asing)
          · rw [mem_lower_iff x] at h_ahigh
            apply DLO.asymm x a
            exact ⟨in_upper, h_ahigh⟩
          · rw [mem_singleton_iff x] at h_asing
            apply DLO.irrefl x
            subst h_asing
            exact in_upper

        · intro hx
          exfalso
          trivial

      apply eqCompl_of_entireUnion_of_emptyIntersection
      · rw [Set.union_comm]
        assumption
      · rw [Set.inter_comm]
        assumption

    rw [<- this]
    apply is_finite_union_of_intervalsP.union
    exact lower a
    exact point a


  · let a_lower := interval.lower a
    let a_upper := interval.upper a

    let combi := a_lower ∪ a_upper

    have this : combi = (interval.singleton a)ᶜ := by
      have union_is_univ : (interval.singleton a) ∪ combi = univ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          show x ∈ (interval.singleton a) ∨ x ∈ combi
          rcases DLO.total x a with a_less | a_equal | a_more
          · right
            unfold combi
            apply Set.mem_union_right
            assumption

          · left
            rw [mem_singleton_iff]
            trivial

          · right
            unfold combi
            apply Set.mem_union_left
            assumption

      have intersection_is_empty : (interval.singleton a) ∩ combi = ∅ := by
        ext x
        constructor
        · intro ⟨in_point, in_combi⟩
          exfalso
          rw [mem_singleton_iff] at in_point
          rcases in_combi with (h_alow | h_ahigh)
          · rw [mem_lower_iff x] at h_alow
            apply DLO.irrefl a
            rw [in_point] at h_alow
            trivial
          · rw [mem_upper_iff x] at h_ahigh
            apply DLO.irrefl a
            rw [in_point] at h_ahigh
            trivial

        · intro hx
          exfalso
          trivial

      apply eqCompl_of_entireUnion_of_emptyIntersection
      · rw [Set.union_comm]
        assumption
      · rw [Set.inter_comm]
        assumption

    rw [<- this]
    apply is_finite_union_of_intervalsP.union
    exact lower a
    exact upper a


  · have : (V ∪ W)ᶜ = Vᶜ ∩ Wᶜ := by
      apply compl_union
    rw [this]
    apply is_finite_union_of_intervalsP.intersection
    assumption'

end DLO.interval
