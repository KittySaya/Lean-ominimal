import LeanOminimal.Basic
open FirstOrder
open Language


def is_quantifierfree_alternative {L : Language} {M : Type} [L.Structure M] {α : Type*} {n : ℕ} (v : α → M) (xs : Fin n → M) (φ : FirstOrder.Language.BoundedFormula L M n) (ψ : FirstOrder.Language.QFBoundedFormula L M n) : Prop :=
  φ.Realize v xs ↔ ψ.Realize v xs
  I worry that something is wrong here, mainly in confusing X and α.
  Also, what are the the arguments of Realize? - Lily

def has_quantifierfreefromula {L : Language} {M : Type} [L.Structure M] {α : Type*} {n : ℕ} (φ : FirstOrder.Language.BoundedFormula L α n) (v : α → M) (xs : Fin n → M) :=
  ∃ ψ : FirstOrder.Language.QFBoundedFormula L M n,
    is_quantifierfree_alternative v xs φ ψ
    -- This definition needs to be better.

def admits_quantifier_elimination (L : Language) (α : Type) [L.Structure α] :=
  ∀n : ℕ, ∀vars : Fin n → α, ∀ φ : FirstOrder.Language.BoundedFormula L α n, has_quantifierfreefromula φ vars
  -- Is this a proper definition?

-- WARNING: Volatile.
-- Editing this theorem may lead to your computer slowing down, even to the point of freezing, and crashing in the worst case.
-- theorem of_exist_bigand_blocks {L : Language} {α : Type} [L.Structure α] (for_existsblocks : ∀n : ℕ, ∀vars : Fin n → α, ∀φ : FirstOrder.Language.BoundedFormula L α n, isExistBlock φ → has_quantifierfreefromula φ vars) : admits_quantifier_elimination L α := by
--   intro n vars φ
--   induction' φ with _ _ eq_t₁ eq_t₂ _ _ rel_R rel_ts _ imp_bounded_f₁ imp_bounded_f₂ imp_ih_f₁ imp_ih_f₂
--   -- repeat1' expose_names
--   · use Language.QFBoundedFormula.falsum
--     unfold is_quantifierfree_alternative
--     sorry
--   · use Language.QFBoundedFormula.equal eq_t₁ eq_t₂
--     sorry
--   · use Language.QFBoundedFormula.rel rel_R rel_ts
--     sorry
--   · -- use Language.QFBoundedFormula.imp imp_f₁ imp_f₂
--     sorry
--   · sorry
