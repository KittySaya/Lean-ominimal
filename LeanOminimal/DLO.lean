import LeanOminimal.Basic
open FirstOrder

/--
A dense linear order is a dense linear order that has no left or right end point.
-/
class DLO (X : Type) extends order X where
  irrefl:   ∀x: X,     ¬(x<₀x)
  trans:    ∀x y z: X, x<₀y → y<₀z → x<₀z  --I changed this to be double implication, which Lean usually uses.
  total:    ∀x y: X,   x<₀y ∨ x=y ∨ y<₀x
  dense:    ∀x y: X,   x<₀y → ∃z: X, x<₀z ∧ z<₀y
  no_r_end: ∀x: X, ∃y: X, x<₀y
  no_l_end: ∀x: X, ∃w: X, w<₀x


namespace DLO

variable {X : Type} [DLO X]

-- Basic lemma's of DLOs.
-- Every dense linear order is asymetric.
@[simp]
lemma asymm (x y : X) : ¬(x <₀ y ∧ y <₀ x) := by
  by_contra h
  apply DLO.irrefl x
  apply DLO.trans x y x
  exact h.left
  exact h.right

-- A different way to characterise no end points.
@[simp]
lemma no_left_extrema : ¬∃y : X, ∀z : X, y = z ∨ y <₀ z := by
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
lemma no_right_extrema : ¬∃y : X, ∀z : X, y = z ∨ y >₀ z := by
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

/--
The model `(ℚ, <)` of rational numbers with the stadard order,
is a dense linear order.
-/
@[simp]
instance Rational_DLO : DLO ℚ  where
  irrefl := by intros x h; exact lt_irrefl x h
  trans := by rintro x y z h1 h2; exact lt_trans h1 h2
  total := by intros x y; exact lt_trichotomy x y
  dense := by intros x y h; exact exists_between h
  no_r_end := by intro x; exact ⟨x + 1, by simp⟩
  no_l_end := by intro x; exact ⟨x - 1, by simp⟩

/--
The model `(ℝ, <)` of real numbers with the stadard order,
is a dense linear order.
-/
@[simp]
instance Real_DLO : DLO ℝ  where
  irrefl := by intros x h; exact lt_irrefl x h
  trans := by rintro x y z h1 h2; exact lt_trans h1 h2
  total := by intros x y; exact lt_trichotomy x y
  dense := by intros x y h; exact exists_between h
  no_r_end := by intro x; exact ⟨x + 1, by simp⟩
  no_l_end := by intro x; exact ⟨x - 1, by simp⟩
