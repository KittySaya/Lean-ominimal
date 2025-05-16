import LeanOminimal.DLO
import LeanOminimal.intervals

open FirstOrder
open Language
open Set

@[simp]
def isDefinable {X : Type} (L : Language) (U : Set X) [Language.Structure L X] : Prop :=
  Definable₁ (⊤ : Set X ) L U

noncomputable section reals
namespace real_DLO
-- @[simp]
-- instance real_order : order ℝ where
--   ord (f: Fin 2 → ℝ ) := f 0 < f 1


-- @[simp]
--  instance Rstruc : Language.Structure order_language ℝ where
--    funMap := λ empt => Empty.elim empt
--    RelMap {n:ℕ }:= λ _ f =>
--     match n with
--     | 2 =>
--       match f with
--       | _ => real_order.ord f -- Why are we matching with something that only has one case?
--     | _ => false


-- @[simp]
-- instance : DLO ℝ  where
--   irrefl := by intros x h; exact lt_irrefl x h
--   trans := by rintro x y z h1 h2; exact lt_trans h1 h2
--   total := by intros x y; exact lt_trichotomy x y
--   dense := by intros x y h; exact exists_between h
--   no_r_end := by intro x; exact ⟨x + 1, by simp⟩
--   no_l_end := by intro x; exact ⟨x - 1, by simp⟩


open FirstOrder.Language

-- @[simp]
-- def constantsOn_toFunctions0 {X : Type} (b : X) : (constantsOn X).Functions 0 :=
--   (by simp : (constantsOn X).Functions 0 = X) ▸ b

-- def constterm {X : Type} (L : FirstOrder.Language) (b : X) : FirstOrder.Language.Term (L.withConstants X) (Fin 1) :=
--   Term.func (Sum.inr (constantsOn_toFunctions0 b)) (λ i => nomatch i)

-- @[simp]
-- def constR  (b : ℝ ) : FirstOrder.Language.Term (order_language [[univ (α := ℝ)]]) (Fin 1) :=
--  (Term.func (Sum.inr (constantsOn_toFunctions0 ⟨b, Set.mem_univ b⟩)) (λ i => nomatch i))






end real_DLO
end reals
