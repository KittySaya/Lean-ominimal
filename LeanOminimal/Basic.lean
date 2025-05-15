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

@[simp]
instance real_order : order ℝ where
  ord (f: Fin 2 → ℝ ) := f 0 < f 1

@[simp]
 instance Rstruc : Language.Structure order_language ℝ where
   funMap := λ empt => Empty.elim empt
   RelMap {n:ℕ }:= λ _ f =>
    match n with
    | 2 =>
      match f with
      | _ => real_order.ord f -- Why are we matching with something that only has one case?
    | _ => false
