import LeanOminimal.Formula.Simple_Conversions

open FirstOrder
open Language
open Set

namespace FirstOrder
namespace Language


----------------------------------------------------------

-- Docstring missing
def varelimAtomicblock {n} (i: Fin 1 ⊕ Fin (n+1) ) (ter : order_language[[@univ ℝ]].Term (Fin 1 ⊕ Fin n)): Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) →  Relblock (order_language[[@univ ℝ]]) (Fin 1) n:= by
  intro rel
  rcases rel with ⟨ _⟩|  ⟨ _⟩|⟨t1,t2 ⟩ |  ⟨R,f ⟩ | ⟨t1,t2 ⟩

  exact Relblock.truth

  exact Relblock.falsum
  exact Relblock.truth


  rename_i l
  by_cases neq: l=2
  let t1:= f ⟨0, by linarith⟩
  let t2 := f ⟨1, by linarith⟩
  rcases t1 with ⟨a1 ⟩ | ⟨h, t_1 ⟩
  rcases t2 with ⟨a2 ⟩  | ⟨g, t_2⟩
  by_cases i=a1

  by_cases i=a2

  exact Relblock.falsum

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then ter else Term.var (reindex a2))

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else ter)
  rename_i p
  by_cases neq : p=0
  rw [neq] at g t_2

  by_cases ineqa : i=a1

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  ter else Term.func g (fun i: Fin 0=>  nomatch i))

  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else Term.func g (fun i: Fin 0=>  nomatch i))

  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
  apply F_empty.elim'
  apply g

  rename_i t
  by_cases neq2 : t=0
  rw [neq2] at h t_1
  rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩
  by_cases ineqa :i=a1
  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else ter)
  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex a1) )
  rename_i e
  by_cases neq2 : e=0
  rw [neq2] at g t_2
  exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=>  nomatch i) )

  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
  apply F_empty.elim'
  apply g

  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
  apply F_empty.elim'
  apply h
  have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
  apply F_empty.elim'
  apply R


  exact (varelimAtomicblock i ter t1).and (varelimAtomicblock i ter t1)


----------------------------------------------------------


def Atomicblock.toRelblock {n} : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → Relblock (order_language[[@univ ℝ]]) (Fin 1) n
  | truth       => .truth
  | falsum      => .falsum
  | and f₁ f₂   => f₁.toRelblock.and f₂.toRelblock
  | equal t₁ t₂ => .truth --sorry --Originally it had "truth" but I don't know if that's right. Are you certain it's correct?
  | rel R ts    => by
    rename_i l
    by_cases neq: l=2
    · let t1 := ts ⟨0, by linarith⟩
      let t2 := ts ⟨1, by linarith⟩
      rcases t1 with ⟨a1 ⟩ | ⟨h, t_1 ⟩
      · rcases t2 with ⟨a2 ⟩  | ⟨g, t_2⟩
        exact Relblock.truth
        rename_i p
        by_cases neq : p=0
        rw [neq] at g t_2

        exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1) else Term.func g (fun i: Fin 0=>  nomatch i) )

        have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
        apply F_empty.elim'
        apply g

      · rename_i p
        by_cases neq : p=0
        · rw [neq] at h t_1

          rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩

          · exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex a1) )
          · rename_i e
            by_cases neq2 : e=0
            rw [neq2] at g t_2
            exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=> nomatch i) )

            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
            apply F_empty.elim'
            apply g

        · have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
          apply F_empty.elim'
          apply h

    · have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
      apply F_empty.elim'
      apply R


-- !!! - Docstring missing
def disjunctionAtomicblocks.todisjunctionRelblocks {n} : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) (n)
  | atom  a  => disjunctionRelblocks.relb (Atomicblock.toRelblock a)
  | or f₁ f₂ => disjunctionRelblocks.or (f₁.todisjunctionRelblocks) (f₂.todisjunctionRelblocks)

-----------------------------------------------------------

-- Docstring missing
def Literal.todisjunctionAtomicblocks {n : ℕ} : Literal (order_language[[@univ ℝ]]) (Fin 1) n → disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | Literal.truth =>
      disjunctionAtomicblocks.atom Atomicblock.truth

  | Literal.equal (.var a1) (.var a2) =>
      let QF := Atomicblock.equal (@Term.var _ ((Fin 1) ⊕ Fin n) a1)
                                  (@Term.var _ ((Fin 1) ⊕ Fin n) a2)
      QF.todisjunctionAtomicblocks

  | Literal.equal (.var a1) (.func g t2) =>
      by
          rename_i l
          by_cases neq : l = 0
          case pos =>
            rw [neq] at g t2
            let const := Term.func g t2
            let ter := @Term.var (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a1
            let QF := Atomicblock.equal const ter
            exact QF.todisjunctionAtomicblocks
          case neg =>
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
            apply F_empty.elim'
            apply g

  | Literal.equal (.func f t1) (.var a2) =>
      by
          rename_i l
          by_cases neq : l = 0
          case pos =>
            rw [neq] at f t1
            let const1 := Term.func f t1
            let ter := @Term.var (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a2
            let QF := Atomicblock.equal const1 ter
            exact QF.todisjunctionAtomicblocks
          case neg =>
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
            apply F_empty.elim'
            apply f

  | Literal.equal (.func h t1) (.func g t2) =>
      by
          rename_i l t
          by_cases neq : l = 0
          case pos =>
            by_cases neq2 : t = 0
            case pos =>
              rw [neq] at h t1
              let const1 := Term.func h t1
              let const2 := Term.func g t2
              exact disjunctionAtomicblocks.atom (Atomicblock.equal const1 const2)
            case neg =>
              have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
              apply F_empty.elim'
              apply g
          case neg =>
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
            apply F_empty.elim'
            apply h

  | Literal.rel R f =>
      let QF := Atomicblock.rel R f
      QF.todisjunctionAtomicblocks

  -- Match on all .not variants explicitly
  | Literal.not (Literal.rel R f) =>
      by
          rename_i l
          by_cases neq: l = 2
          case pos =>
            let ter1 := f ⟨0, by linarith⟩
            let ter2 := f ⟨1, by linarith⟩
            let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![ter2, ter1]
            let QF2 := Atomicblock.equal ter1 ter2
            exact disjunctionAtomicblocks.or QF1.todisjunctionAtomicblocks QF2.todisjunctionAtomicblocks
          case neg =>
            exfalso
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l) := isEmpty_of_relationsOrderLanguageR_of_ne_2 neq
            apply F_empty.elim'
            apply R

  | Literal.not (Literal.equal (.var a1) (.var a2)) =>
      by
            let ter1:= @Term.var (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a1
            let ter2 := @Term.var (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a2
            let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![ter1, ter2]
            let QF2 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![ter2, ter1]
            exact (disjunctionAtomicblocks.atom QF1).or (disjunctionAtomicblocks.atom QF2)


  | Literal.not (Literal.equal (.var a1) (.func g t2)) =>
      by
          rename_i l
          by_cases neq : l = 0
          case pos =>
            rw [neq] at g t2
            let const := Term.func g t2
            let ter := @Term.var (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a1
            let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![ter, const]
            let QF2 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![const, ter]
            exact (disjunctionAtomicblocks.atom QF1).or (disjunctionAtomicblocks.atom QF2)
          case neg =>
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
            apply F_empty.elim'
            apply g

  | Literal.not (Literal.equal (.func f t1) (.var a2)) =>
      by
          rename_i l
          by_cases neq : l = 0
          case pos =>
            rw [neq] at f t1
            let const := Term.func f t1
            let ter := @Term.var (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a2
            let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![ter, const]
            let QF2 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![const, ter]
            exact (disjunctionAtomicblocks.atom QF1).or (disjunctionAtomicblocks.atom QF2)
          case neg =>
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
            apply F_empty.elim'
            apply f

  | Literal.not Literal.truth =>
      disjunctionAtomicblocks.atom Atomicblock.falsum

  | Literal.not (Literal.not f) =>
      f.todisjunctionAtomicblocks

  | Literal.not (Literal.equal (.func h t1) (.func g t2)) =>
        by
          rename_i l t
          by_cases neq : l = 0
          case pos =>
            by_cases neq2 : t = 0
            case pos =>
              rw [neq] at h t1
              let const1 := Term.func h t1
              let const2 := Term.func g t2
              let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![const1, const2]
              let QF2 := Atomicblock.rel (Sum.inl ordsymbol.lt) ![const2, const1]
              exact (disjunctionAtomicblocks.atom QF1).or (disjunctionAtomicblocks.atom QF2)
            case neg =>
              have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
              apply F_empty.elim'
              apply g
          case neg =>
            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l) := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq
            apply F_empty.elim'
            apply h

-----------------------------------------------------------

def Existblock.todisjunctionAtomicblocks {n : ℕ} : Existblock (order_language[[@univ ℝ]]) (Fin 1) n → disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | lit l     => l.todisjunctionAtomicblocks
  | and e₁ e₂ => e₁.todisjunctionAtomicblocks.and e₂.todisjunctionAtomicblocks

-----------------------------------------------------------

def Existblock.todisjunctionRelblocks {n} : Existblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) n :=
    fun eb => eb.todisjunctionAtomicblocks.todisjunctionRelblocks

-----------------------------------------------------------

-- !!! - Docstring missing
@[simp]
def disjunctionExistblocks.elim  {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | existbl eb => eb.todisjunctionRelblocks.todisjunctionExistblocks
  | or f₁ f₂   => f₁.elim.or f₂.elim

-- !!! - Docstring missing
-- !!! - To match?
def notExistblockelim {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n):= by
  intro exbl
  rcases exbl with ⟨ exbl⟩ | ⟨ex1,ex2⟩

  rcases exbl with ⟨lit ⟩

  exact (disjunctionExistblocks.existbl (Existblock.lit lit )).elim
  rename_i ex1 ex2
  exact (notExistblockelim (disjunctionExistblocks.existbl ex1)).or (notExistblockelim (disjunctionExistblocks.existbl ex1))

  exact (notExistblockelim ex1).and (notExistblockelim ex2)

------------------------------------------------------------------

/--
Sends ImpAllFreeFormula `φ` in the language of `(ℝ, <)` to a QFImpAllFreeFormula that is equivalent to it.
-/
def ImpAllFreeFormula.toQFImpAllFreeFormula  {n:ℕ } : ImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) (n) → QFImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) n :=
  let rec helper {n} : ImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) n →
      disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) n
    | .falsum => disjunctionExistblocks.existbl (Existblock.lit (Literal.truth.not))
    | .equal t1 t2 => disjunctionExistblocks.existbl (Existblock.lit (Literal.equal t1 t2))
    | .rel R f => disjunctionExistblocks.existbl (Existblock.lit (Literal.rel R f))
    | .and t1 t2=> (helper t1).and (helper t2)
    | .or t1 t2=> (helper t1).or (helper t2)
    | .not t => (helper t)
    | .exists φ  => match φ with
      | .falsum =>
          disjunctionExistblocks.existbl (Existblock.lit (Literal.truth.not))
      | .equal t1 t2 =>
          (disjunctionExistblocks.existbl (Existblock.lit (Literal.equal t1 t2))).elim
      | .rel R f =>
          (disjunctionExistblocks.existbl (Existblock.lit (Literal.rel R f))).elim
      | .not φ  =>
          notExistblockelim (helper  φ )
      | .or φ₁ φ₂ =>
          (helper φ₁).elim.or (helper φ₂).elim
      | .and φ₁ φ₂ =>
          ((helper φ₁).and (helper φ₂)).elim
      | .exists φ =>
          (helper φ).elim.elim

  fun φ =>
      match φ with
      | .falsum        => QFImpAllFreeFormula.falsum
      | .equal t1 t2   => QFImpAllFreeFormula.equal t1 t2
      | .rel R f       => QFImpAllFreeFormula.rel R f
      | .not φ         => φ.toQFImpAllFreeFormula.not
      | .or φ₁ φ₂      => φ₁.toQFImpAllFreeFormula.or φ₂.toQFImpAllFreeFormula
      | .and φ₁ φ₂     => φ₁.toQFImpAllFreeFormula.and φ₂.toQFImpAllFreeFormula
      | .exists φ      => (helper (.exists φ)).toQFImpAllFreeFormula
