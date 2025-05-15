import Mathlib.ModelTheory.Basic

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

class DLO (X : Type) extends order X where
  irrefl:   ∀x: X,     ¬(x<₀x)
  trans:    ∀x y z: X, x<₀y → y<₀z → x<₀z  --I changed this to be double implication, which Lean usually uses.
  total:    ∀x y: X,   x<₀y ∨ x=y ∨ y<₀x
  dense:    ∀x y: X,   x<₀y → ∃z: X, x<₀z ∧ z<₀y
  no_r_end: ∀x: X, ∃y: X, x<₀y
  no_l_end: ∀x: X, ∃w: X, w<₀x


namespace DLO

-- Basic lemma's of DLOs.
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
