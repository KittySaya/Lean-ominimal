import LeanOminimal.Formula.Simple_Conversions

open FirstOrder
open Language
open Set

namespace FirstOrder
namespace Language

noncomputable section

----------------------------------------------------------

-- Docstring missing
def varelimAtomicblock {n} (i: Fin 1 ⊕ Fin (n+1) ) (ter : order_language[[@univ ℝ]].Term (Fin 1 ⊕ Fin n)) : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → Relblock (order_language[[@univ ℝ]]) (Fin 1) n
  | .truth       => Relblock.truth
  | .falsum      => Relblock.falsum

  | .and f₁ f₂   => (varelimAtomicblock i ter f₁).and (varelimAtomicblock i ter f₁)

  | .equal t₁ t₂ => Relblock.truth --Is this always ∃x[a = x], or can this also be ∃x[a = b]?

  | .rel R ts    => by --!!! - docstring missing
    expose_names
    by_cases l_val : l=2

    case neg =>
      have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= isEmpty_of_relationsOrderLanguageR_of_ne_2 l_val
      apply F_empty.elim'
      exact R

    case pos =>
      subst l
      let t1 := ts ⟨0, by linarith⟩
      let t2 := ts ⟨1, by linarith⟩

      rcases t1 with a1 | ⟨h, t_1⟩
      · rcases t2 with a2 | ⟨g, t_2⟩

        · by_cases neq1 : i=a1

          · by_cases neq2 : i=a2

            · exact Relblock.falsum

            · exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then ter else Term.var ((reindex i a2 neq2)))

          exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex i a1 neq1) else ter)

        · rename_i p
          by_cases p_val : p=0
          · subst p
            by_cases ineqa : i=a1
            · exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2) => if j=0 then ter else Term.func g (fun i: Fin 0 =>  nomatch i))
            · exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2) => if j=0 then Term.var (reindex i a1 ineqa ) else Term.func g (fun i: Fin 0 =>  nomatch i))

          · have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 p_val
            apply F_empty.elim'
            apply g

      · rename_i t
        by_cases t_val : t=0

        case neg =>
          have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 t_val
          apply F_empty.elim'
          apply h

        case pos =>
          subst t
          rcases t2 with a1 | ⟨g, t_2⟩
          · by_cases ineqa :i=a1
            exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else ter)
            exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex i a1 ineqa))

          · rename_i e
            by_cases neq2 : e=0
            rw [neq2] at g t_2
            exact Relblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=>  nomatch i) )

            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := isEmpty_of_functionsOrderLanguageR_of_ne_0 neq2
            apply F_empty.elim'
            apply g


----------------------------------------------------------


-- !!! - docstring missing
def Atomicblock.toRelblock {n} (block : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1)) : Relblock (order_language[[@univ ℝ]]) (Fin 1) n := by
  rcases block with ⟨ _⟩|⟨_ ⟩ | ⟨t1 ,t2⟩ | ⟨R, f⟩| ⟨ f⟩ |⟨ ⟩

  exact Relblock.truth

  exact Relblock.falsum

  exact Relblock.truth

  exact Relblock.truth



  rename_i f
  exact f.toRelblock
  exact Relblock.falsum
  rename_i a t1 t2
  rcases t1 with ⟨i ⟩|  ⟨h,t_1 ⟩
  rcases t2 with ⟨j⟩|  ⟨g,t_2 ⟩
  by_cases neq: i=j
  exact  Relblock.truth
  exact (varelimAtomicblock i (Term.var (reindex i j neq)) (a))
  rename_i l
  by_cases neq2 : l=0
  rw [neq2] at g t_2
  exact (varelimAtomicblock i (Term.func g (fun i: Fin 0=>  nomatch i)) (a))
  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l)  := func0empty neq2
  apply F_empty.elim'
  apply g




  rename_i t
  by_cases neq2 : t=0
  rw [neq2] at h t_1
  rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩

  exact (varelimAtomicblock a1 (Term.func h (fun i: Fin 0=>  nomatch i)) (a))

  rename_i e
  by_cases neq2 : e=0
  rw [neq2] at g t_2
  by_cases h=g
  exact Relblock.truth
  exact Relblock.falsum


  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := func0empty neq2
  apply F_empty.elim'
  apply g
  have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := func0empty neq2
  apply F_empty.elim'
  apply h

  rename_i a l R f
  exact (Atomicblock.rel R f).toRelblock.and a.toRelblock
  rename_i a1 a2 a3
  exact (a1.toRelblock.and a2.toRelblock).and a3.toRelblock


-- !!! - Docstring missing
def disjunctionAtomicblocks.todisjunctionRelblocks {n} : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) (n)
  | atom  a  => disjunctionRelblocks.relb (Atomicblock.toRelblock a)
  | or f₁ f₂ => disjunctionRelblocks.or (f₁.todisjunctionRelblocks) (f₂.todisjunctionRelblocks)

-----------------------------------------------------------

-- !!! - Docstring missing
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

/--
Sends an existblock recursively to a disjunction of atomic blocks
-/
def Existblock.todisjunctionAtomicblocks {n : ℕ} : Existblock (order_language[[@univ ℝ]]) (Fin 1) n → disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | lit l     => l.todisjunctionAtomicblocks
  | and e₁ e₂ => e₁.todisjunctionAtomicblocks.and e₂.todisjunctionAtomicblocks

-----------------------------------------------------------

/--
Sends an existblock to a disjunction of rel blocks through a disjunction of atomic blocks.
-/
def Existblock.todisjunctionRelblocks {n} : Existblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) n :=
    fun eb => eb.todisjunctionAtomicblocks.todisjunctionRelblocks

-----------------------------------------------------------

-- !!! - Docstring missing
@[simp]
def disjunctionExistblocks.elim  {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) n
  | existbl eb => eb.todisjunctionRelblocks.todisjunctionExistblocks
  | or f₁ f₂   => f₁.elim.or f₂.elim

-- !!! - Docstring missing
def notExistblockelim {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n)
  | .existbl eb => match eb with
    | .lit lit => (disjunctionExistblocks.existbl (Existblock.lit lit )).elim
    | .and ex₁ ex₂ => (notExistblockelim (disjunctionExistblocks.existbl ex₁)).or (notExistblockelim (disjunctionExistblocks.existbl ex₂))
  | .or f₁ f₂   => (notExistblockelim f₁).and (notExistblockelim f₂)

-- !!! - To match? - Done so, maybe delete this.
def notExistblockelim.old {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n):= by
  intro exbl
  rcases exbl with ⟨ exbl⟩ | ⟨ex1,ex2⟩

  rcases exbl with ⟨lit ⟩

  exact (disjunctionExistblocks.existbl (Existblock.lit lit )).elim
  rename_i ex1 ex2
  exact (notExistblockelim.old (disjunctionExistblocks.existbl ex1)).or (notExistblockelim.old (disjunctionExistblocks.existbl ex2))

  exact (notExistblockelim.old ex1).and (notExistblockelim.old ex2)

lemma notExistblockelim.equiv {n : ℕ} (deb : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1)) : notExistblockelim.old deb = notExistblockelim deb := by
  induction' deb with r f1 f2 f1ih f2ih
  induction' r with l l1 l2 l1ih l2ih
  unfold notExistblockelim
  unfold notExistblockelim.old
  dsimp
  unfold notExistblockelim
  unfold notExistblockelim.old
  dsimp
  congr
  unfold notExistblockelim
  unfold notExistblockelim.old
  dsimp
  congr

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
