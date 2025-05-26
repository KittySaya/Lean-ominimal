import Mathlib --Sadly, we weren't able to isolate what we needed from Mathlib, and imported it all.

open FirstOrder

/--
An `order` is a class with a single binary relation symbol, `ord`.
-/
class order (X : Type) : Type where
  ord : (Fin 2 → X) → Prop

namespace order

variable {X : Type} [order X]

/--
This function translates `lt x y` to `ord F`, where `F` is the function
that sends `0` to `x` and `1` to `y`.
-/
@[simp]
def lt (x y : X) [order X] : Prop :=
  ord (λ i => match i with
    | 0 => x
    | 1 => y)


infix:50 " <₀ " => lt
notation x " >₀ " y => y <₀ x

end order

inductive ordsymbol : Type
  | lt : ordsymbol

/--
The language of orders consist of a single binary relation symbol.
-/
@[simp]
def order_language : FirstOrder.Language where
  Functions := λ _ => Empty
  Relations := λ n => if n = 2 then ordsymbol else Empty


/--
The model `(ℚ, <)` of `order_language = (<₀)` equipped with
the rational numbers and the standard `<`, i.e., `less than` order.
-/
@[simp]
instance rational_order : order ℚ where
  ord (f: Fin 2 → ℚ ) := f 0 < f 1


noncomputable section reals
/--
The model `(ℝ, <)` of `order_language = (<₀)` equipped with
the real numbers and the standard `<`, i.e., `less than` order.
-/
@[simp]
instance real_order : order ℝ where
  ord (f: Fin 2 → ℝ ) := f 0 < f 1

/--
Proof that `(ℝ, <)` is a structure with language `order_language = (<₀)`
-/
@[simp]
instance Rstruc : Language.Structure order_language ℝ where
  funMap := λ empt => Empty.elim empt
  RelMap {n : ℕ} := λ _ f =>
    match n with
    | 2 => real_order.ord f
    | _ => false

end reals


section Const

open FirstOrder.Language
open Set

@[simp]
def constantsOn_toFunctions0 {X : Type} (b : X) : (constantsOn X).Functions 0 :=
  (by simp : (constantsOn X).Functions 0 = X) ▸ b

def constterm {X : Type} (L : FirstOrder.Language) (b : X) : FirstOrder.Language.Term (L.withConstants X) (Fin 1) :=
  Term.func (Sum.inr (constantsOn_toFunctions0 b)) (λ i => nomatch i)

@[simp]
def constR  (b : ℝ ) : FirstOrder.Language.Term (order_language [[univ (α := ℝ)]]) (Fin 1) :=
  Term.func (Sum.inr (constantsOn_toFunctions0 ⟨b, Set.mem_univ b⟩)) (λ i => nomatch i)

end Const

section order_language_ℝ

open FirstOrder
open Language
open Set

/--
If not `n = 2` where `n` is a natural number, then
in the language `order_language[[@univ ℝ]]`, the set relations of arity `n`
is empty.
-/
lemma isEmpty_of_relationsOrderLanguageR_of_ne_2 {n : ℕ} (h : ¬n=2) : IsEmpty (order_language[[@univ ℝ]].Relations n) := by
  have const_eq_empty: (constantsOn ℝ ).Relations n = Empty :=
    FirstOrder.Language.constantsOn_Relations ℝ n
  have rel_eq_empty:  order_language.Relations n = Empty := by
    simp
    intro ass
    contradiction
  have coerc : order_language[[@univ ℝ]].Relations n = (order_language.Relations n ⊕ (constantsOn ℝ).Relations n) := by
    rfl
  rw [coerc]
  rw [const_eq_empty, rel_eq_empty]
  have isEmpty_of_Empty : IsEmpty Empty := Empty.instIsEmpty
  apply isEmpty_sum.mpr
  constructor
  · apply isEmpty_of_Empty
  · apply isEmpty_of_Empty

alias rel2empty := isEmpty_of_relationsOrderLanguageR_of_ne_2

/--
If not `n = 0` where `n` is a natural number, then
in the language `order_language[[@univ ℝ]]`, the set of functions of arity `n`
is empty.
-/
lemma isEmpty_of_functionsOrderLanguageR_of_ne_0 {n : ℕ} (h : ¬n=0) : IsEmpty (order_language[[@univ ℝ]].Functions n) := by
  have functions_eq_empty : order_language.Functions n = Empty := by
    simp
  have coerc : order_language[[@univ ℝ]].Functions n = (order_language.Functions n ⊕ (constantsOn (@univ ℝ) ).Functions n) := by
    rfl
  rw [coerc]
  rcases n with _ | k
  · exfalso
    trivial

  · have functions_is_empty : IsEmpty ((constantsOn ℝ ).Functions (k+1)) :=
      FirstOrder.Language.isEmpty_functions_constantsOn_succ
    rw [functions_eq_empty]
    apply isEmpty_sum.mpr
    constructor
    · have isEmpty_of_Empty : IsEmpty Empty := Empty.instIsEmpty
      apply isEmpty_of_Empty
    · apply functions_is_empty

alias func0empty := isEmpty_of_functionsOrderLanguageR_of_ne_0

end order_language_ℝ

section some_section

/--
This function takes two indices and a proposition that the indices are not equal. The function eliminates the variable indexed by i, if it is of type Fin (n+1)
and shuffles all other variables accordingly, i.e., it shifts every element above i down by 1. If i is in Fin 1, we eliminate the variable indexed by a. 
-/
def reindex {n : ℕ} (i : Fin 1 ⊕ Fin (n + 1))  (h : ¬ i=Sum.inr ⟨n, (by simp) ⟩) : Fin 1 ⊕ Fin n :=by
rcases i with ⟨ inli ,hypi⟩ | ⟨inli,hypi ⟩
exact Sum.inl ⟨inli, hypi ⟩ 
simp at h
have hypi': inli <n:= by 
 by_contra con
 push_neg at con
 have : inli =n := by
  linarith
 contradiction 
exact Sum.inr ⟨inli, hypi' ⟩ 
end some_section
