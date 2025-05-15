import LeanOminimal.Basic
open FirstOrder
open Language


/--
A Literal of a Language `L`, a Type `α`, and a number of free variables `n`
is a formula consisting solely of

  equality of terms

  relations of terms

  and lastly, negation of either of those
-/
inductive Literal (L : Language) (α : Type) (n : ℕ) : Type _
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : Literal L α n
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : Literal L α n
  | not (f : Literal L α n) : Literal L α n


namespace Literal

/--
This function removes any instances of double negation in a Literal.

e.g., it turns
           x = y  into x = y,
         ¬(x = y) into ¬(x = y),
        ¬¬(x = y) into x = y
¬¬ ¬¬ ¬¬ ¬(x = y) into ¬(x = y)
-/
def remove_doubleneg {L : Language} {α : Type} {n : ℕ} : Literal L α n → Literal L α n
  | equal t₁ t₂ => equal t₁ t₂
  | rel R ts => rel R ts
  | not f => match f with
    | equal t₁ t₂ => not (equal t₁ t₂)
    | rel R ts => not (rel R ts)
    | not f' => Literal.remove_doubleneg f'

namespace remove_doubleneg

@[simp]
lemma removes_doubleneg {L : Language} {α : Type} {n : ℕ} (φ : Literal L α n) (ψ : Literal L α n) (h : ψ = φ.not.not) : Literal.remove_doubleneg ψ = Literal.remove_doubleneg φ := by
  subst h
  rfl

@[simp]
lemma maintains_equal  {L : Language} {α : Type} {n : ℕ} {t₁ t₂} (φ : Literal L α n) (h : φ = Literal.equal t₁ t₂) : Literal.remove_doubleneg φ = φ := by
  subst h
  rfl

@[simp]
lemma maintains_notequal  {L : Language} {α : Type} {n : ℕ} {t₁ t₂} (φ : Literal L α n) (h : φ = (Literal.equal t₁ t₂).not) : Literal.remove_doubleneg φ = φ := by
  subst h
  rfl

end remove_doubleneg
end Literal

/--
An `ImpAllFreeFormula`, short for `Implication_and_ForAll_free_formula`,
is a representation of some formula φ of a Language `L`, a Type `α` and a number of free variables `n`
written in such a way that it doesn't contain any → or ∀ symbols.
That is, it consists solely of:

  falsum, or falsehood.

  equality of terms.

  relations of terms.

  negation (¬) of other ImpAllFreeFormula.

  disjunction (or, ∨) of other ImpAllFreeFormula.

  conjunction (and, ∧) of other ImpAllFreeFormula.

  existentials (exists, ∃) of other ImpAllFreeFormula.

It should be noted that, in classical logic, every formula is equivalent to an ImpAllFreeFormula.
-/
inductive ImpAllFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n : ℕ} : ImpAllFreeFormula L α n
  | equal  {n : ℕ}   (t₁ t₂ : L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : ImpAllFreeFormula L α n

  | not    {n : ℕ}   (f     : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | or     {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n
  | and    {n : ℕ}   (f₁ f₂ : ImpAllFreeFormula L α n) : ImpAllFreeFormula L α n

  | exists {n : ℕ}   (f : ImpAllFreeFormula L α (n + 1)) : ImpAllFreeFormula L α n


namespace ImpAllFreeFormula

/--
Gives a meaning to a formula.
-/
def Realize {α} : ∀ {l} (_f : ImpAllFreeFormula order_language α l) (_v : α → ℝ) (_xs : Fin l → ℝ), Prop
  | _, FirstOrder.Language.ImpAllFreeFormula.falsum, _v, _xs => False
  | _, FirstOrder.Language.ImpAllFreeFormula.equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, FirstOrder.Language.ImpAllFreeFormula.rel R ts, v, xs => real_DLO.Rstruc.RelMap R fun i => (ts i).realize (Sum.elim v xs)

  | _, FirstOrder.Language.ImpAllFreeFormula.not f, v, xs => ¬ Realize f v xs
  | _, FirstOrder.Language.ImpAllFreeFormula.and f₁ f₂, v, xs => Realize f₁ v xs ∧ Realize f₂ v xs
  | _, FirstOrder.Language.ImpAllFreeFormula.or  f₁ f₂, v, xs => Realize f₁ v xs ∨ Realize f₂ v xs

  | _, FirstOrder.Language.ImpAllFreeFormula.exists f, v, xs => ∃ x : ℝ, Realize f v (Fin.snoc xs x)


section Realize_theorems
variable {L : Language} [L.Structure ℝ]
variable {α : Type}
variable {l : ℕ} {φ ψ : ImpAllFreeFormula order_language α l} {θ : ImpAllFreeFormula order_language α l.succ}
variable {v : α → ℝ} {xs : Fin l → ℝ}

@[simp]
theorem realize_falsum : ImpAllFreeFormula.Realize (FirstOrder.Language.ImpAllFreeFormula.falsum : ImpAllFreeFormula order_language α l) v xs ↔ False := by
  exact Iff.rfl

@[simp]
theorem realize_notfalsum : ImpAllFreeFormula.Realize (ImpAllFreeFormula.not ImpAllFreeFormula.falsum) v xs := by
  exact fun a ↦ a

-- @[simp]
-- theorem realize_bdEqual (t₁ t₂ : order_language.Term (α ⊕ (Fin l))) :
--     (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) := by
--   exact BoundedFormula.realize_bdEqual t₁ t₂

@[simp]
theorem realize_rel {k : ℕ} {R : order_language.Relations k} {ts : Fin k → order_language.Term _} :
    (R.boundedFormula ts).Realize v xs ↔ real_DLO.Rstruc.RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs := by
  exact Iff.rfl

@[simp]
theorem realize_and : (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [order_language, ImpAllFreeFormula.Realize]

@[simp]
theorem realize_or : (φ.or ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [order_language, ImpAllFreeFormula.Realize]

@[simp]
theorem realize_rel₁ {R : order_language.Relations 1} {t : order_language.Term _} :
    (R.boundedFormula₁ t).Realize v xs ↔ real_DLO.Rstruc.RelMap R ![t.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_rel₂ {R : order_language.Relations 2} {t₁ t₂ : order_language.Term _} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
      real_DLO.Rstruc.RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
theorem realize_exists : (ImpAllFreeFormula.exists θ).Realize v xs ↔ ∃ a : ℝ, θ.Realize v (Fin.snoc xs a) := by
  simp only [ImpAllFreeFormula.Realize, Nat.succ_eq_add_one]


end Realize_theorems

/- Deprecated
def RealOrder.ImpAllFreeFormula.Realize {α} : ∀ {l} (_f : ImpAllFreeFormula order_language α l) (_v : α → ℝ) (_xs : Fin l → ℝ), Prop
  | _, FirstOrder.Language.ImpAllFreeFormula.falsum, _v, _xs => False
  | _, FirstOrder.Language.ImpAllFreeFormula.equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, FirstOrder.Language.ImpAllFreeFormula.rel R ts, v, xs => real_DLO.Rstruc.RelMap R fun i => (ts i).realize (Sum.elim v xs)
  -- We try to realize an ImpAllFreeFormula here, why do we have imp and all???
  | _, FirstOrder.Language.ImpAllFreeFormula.imp f₁ f₂, v, xs => Realize f₁ v xs → Realize f₂ v xs
  | _, FirstOrder.Language.ImpAllFreeFormula.all f, v, xs => ∀ x : M, Realize f v (snoc xs x)
-/

/--
Changes an ImpAllFreeFormula into a bounded one.
-/
def toBounded {L : Language} {α : Type} {n : ℕ} : ImpAllFreeFormula L α n → BoundedFormula L α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .not f => (f.toBounded).not -- (f.toBounded).imp .falsum
  | .or f₁ f₂ => BoundedFormula.imp (f₁.toBounded.not) f₂.toBounded -- ((f₁.not).toBounded).imp f₂.toBounded
  | .and f₁ f₂ => (BoundedFormula.imp f₁.toBounded f₂.toBounded.not).not -- ((f₁.not).or (f₂.not).not).toBounded
  | .exists f => (f.toBounded).ex-- (((f.toBounded).not).all).not

end ImpAllFreeFormula

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

def BoundedFormula.toImpAllFreeFormula {L : Language} {α : Type} {n : ℕ} : BoundedFormula L α n → ImpAllFreeFormula L α n
  | .falsum => .falsum
  | .equal t₁ t₂ => .equal t₁ t₂
  | .rel R ts => .rel R ts
  | .imp f₁ f₂ => ((f₁.toImpAllFreeFormula).not).or f₂.toImpAllFreeFormula
  | .all f => (((f.toImpAllFreeFormula).not).exists).not


namespace ImpAllFreeFormula
open BoundedFormula

lemma toBoundedFormula.when_realized_is_left_identity {α : Type} {m : ℕ} :
    ∀ φ : ImpAllFreeFormula order_language α m, ∀ v : α → ℝ, ∀ xs : Fin m → ℝ, (BoundedFormula.toImpAllFreeFormula (ImpAllFreeFormula.toBounded φ)).Realize v xs ↔ φ.Realize v xs := by
  intro φ v xs
  induction' φ with _ _ _ _ _ _ _ _ n not_formula ih_not_formula n or₁ or₂ or₁_ih or₂_ih n and₁ and₂ and₁_ih and₂_ih o p q r s t u v w x y z
  repeat' rfl

  · specialize ih_not_formula xs
    unfold toBounded toImpAllFreeFormula
    simp only [order_language, realize_or, realize_not, ih_not_formula, or_iff_left_iff_imp]
    intro h
    exfalso
    exact h

  · specialize or₁_ih xs
    specialize or₂_ih xs
    unfold toBounded toImpAllFreeFormula
    have this : ¬((or₁.toBounded.not).toImpAllFreeFormula.Realize v xs) ↔ (or₁.toBounded).toImpAllFreeFormula.Realize v xs := by
      sorry

    simp only [order_language, realize_or, realize_not, or₁_ih, or₂_ih, this]

  · specialize and₁_ih xs
    specialize and₂_ih xs
    unfold toBounded toImpAllFreeFormula
    simp? [and₁_ih, and₂_ih]

    sorry
  · sorry


lemma toBoundedFormula.is_right_identity {L : Language} {α : Type} {n : ℕ} :
    ∀ φ : BoundedFormula L α n, ImpAllFreeFormula.toBounded (BoundedFormula.toImpAllFreeFormula φ) = φ := by

  sorry


/- lemma f.Realize i x ↔ (BoundedFormula.toImpAllFreeFormula f).toBoundedFormula.Realize i x:= by sorry -/

end ImpAllFreeFormula

/--
The type of Quantifier Free bounded formulae without implications.
That is, a formula φ is considered to be quantifier free if it doesn't contain and ∀ or ∃ quantifiers,
and is implication free if it contains no → connective.

That is, a QF Imp formula is solely built up on falsum, equality of terms, relations of terms,
and the connectives not, or, and.
-/
inductive QFImpFreeFormula (L : Language) (α : Type) : ℕ → Type _
  | falsum {n} : QFImpFreeFormula L α n
  | equal  {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : QFImpFreeFormula L α n
  | rel    {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : QFImpFreeFormula L α n
  | not    {n} (f : QFImpFreeFormula L α n) : QFImpFreeFormula L α n
  | or     {n} (f₁ f₂ : QFImpFreeFormula L α n) : QFImpFreeFormula L α n
  | and    {n} (f₁ f₂ : QFImpFreeFormula L α n) : QFImpFreeFormula L α n
