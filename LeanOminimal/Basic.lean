import Mathlib

open FirstOrder

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
    | 2 => real_order.ord f -- Why are we matching with something that only has one case?
    | _ => false


section SomeSectionName

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

end SomeSectionName
