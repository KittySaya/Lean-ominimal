import LeanOminimal.Formula.Simple_Conversions

open FirstOrder
open Language
open Set

namespace FirstOrder
namespace Language

noncomputable section

----------------------------------------------------------

/--
Function that takes in a variable index and a term, and swaps every variable with that particular index for the term with one free variable less.
The resulting function effectively eliminated the variables at the given index. We will only be using this function whenever our atomicblock is preceded by an 
existential quantifier. 
-/

def varelimAtomicblock {n} (i: Fin 1 ⊕ Fin (n+1) ) (ter : order_language[[@univ ℝ]].Term (Fin 1 ⊕ Fin n)) : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → Relblock (order_language[[@univ ℝ]]) (Fin 1) n
  | .truth       => Relblock.truth
  | .falsum      => Relblock.falsum

  | .and f₁ f₂   => (varelimAtomicblock i ter f₁).and (varelimAtomicblock i ter f₁)

  | .equal t₁ t₂ => Relblock.truth -- These should be thought of as \exists (x=a). This statement is always true. The case \exists (a=b), cannot happen since every term contains at least one variable. 

  | .rel R ts    => by  -- We check whether the term of the form 'x<a' contains the variable in question, if so, we replace it by the given term. 
  
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

            · exact Relblock.falsum -- Terms of the form 'x<x' are always false

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



/--
Function that takes an element of the form \exists Atomicblock and sends it to a disjunction of Relblocks, thereby effectively eliminating the 
existential quantifier. This function will only be used on a formula preceded by an existential quantifier. 
-/

def Atomicblock.elim {n}(block : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) ((n+1))) : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) n := by 
rcases block with ⟨ _⟩|⟨_ ⟩ | ⟨t1 ,t2⟩ | ⟨R, f⟩| ⟨ f⟩ |⟨ ⟩

exact Atomicblock.truth

exact Atomicblock.falsum

exact Atomicblock.truth

exact Atomicblock.truth 

rename_i f
exact f.elim
exact Atomicblock.falsum
rename_i a t1 t2
rcases t1 with ⟨i ⟩|  ⟨h,t_1 ⟩
rcases t2 with ⟨j⟩|  ⟨g,t_2 ⟩

by_cases neq1 : i=Sum.inr ⟨n, by simp⟩ 
          
by_cases neq2 : j=Sum.inr ⟨n, by simp⟩ 

exact Atomicblock.truth

exact (varelimAtomicblock (Term.var (reindex j neq2)) (a))

by_cases neq2 : j=Sum.inr ⟨n, by simp⟩ 

exact varelimAtomicblock (Term.var (reindex i neq1)) a 

exact (Atomicblock.equal (Term.var ((reindex i neq1))) (Term.var ((reindex j neq2)))).and a.elim

rename_i l
by_cases neq2 : l=0
rw [neq2] at g t_2
by_cases neq1 : i=Sum.inr ⟨n, by simp⟩ 
exact (varelimAtomicblock (Term.func g (fun i: Fin 0=>  nomatch i)) (a))
exact (Atomicblock.equal (Term.func g (fun i: Fin 0=>  nomatch i)) (Term.var ((reindex i neq1)))).and a.elim
have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l)  := func0empty neq2
apply F_empty.elim'
apply g


rename_i t 
by_cases neq2 : t=0
rw [neq2] at h t_1 
rcases t2 with ⟨a1 ⟩ |  ⟨g, t_2⟩ 
by_cases neq1: a1 = Sum.inr ⟨n, by simp ⟩ 
exact (varelimAtomicblock (Term.func h (fun i: Fin 0=>  nomatch i)) (a))
exact (Atomicblock.equal (Term.func h (fun i: Fin 0=>  nomatch i)) (Term.var ((reindex a1 neq1)))).and a.elim
rename_i l
by_cases neq3 : l=0
rw [neq3] at g t_2
by_cases h=g
exact Atomicblock.truth
exact Atomicblock.falsum


have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l)  := func0empty neq3
apply F_empty.elim'
apply g
have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := func0empty neq2
apply F_empty.elim'
apply h

rename_i a l R f

exact (Atomicblock.rel R f).elim.and a.elim
rename_i a1 a2 a3
exact (a1.elim.and a2.elim).and a3.elim

/--
Since an existential quantifier distributes over a disjunction, we extend the previous function to a function from a disjunction of Atomicblocks 
to a disjunction of Relblocks. 
-/
def disjunctionAtomicblocks.todisjunctionRelblocks {n} : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionRelblocks (order_language[[@univ ℝ]]) (Fin 1) (n)
  | atom  a  => disjunctionRelblocks.relb (Atomicblock.toRelblock a)
  | or f₁ f₂ => disjunctionRelblocks.or (f₁.todisjunctionRelblocks) (f₂.todisjunctionRelblocks)

-----------------------------------------------------------

/--
Function that takes a literal and sends it to a disjunction of atomicblocks. It does this by using the theory of dense linear orders to rewrite every negation. 
-/

def Literal.todisjunctionAtomicblocks {n:ℕ }(l : Literal (order_language[[@univ ℝ]]) (Fin 1) n) : disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) n := by
 rcases l with ⟨ ⟩ | ⟨t1 ,t2⟩ | ⟨R, f⟩ | ⟨ ⟩ | ⟨t1, t2⟩ | ⟨R, f⟩ | f

 exact disjunctionAtomicblocks.atom (Atomicblock.truth)

 rcases t1 with ⟨a1 ⟩ | ⟨f, t1 ⟩
 rcases t2 with ⟨a2 ⟩  | ⟨g, t2⟩

 let QF :=  Atomicblock.equal (@Term.var  (order_language[[@univ ℝ]]) (Fin 1 ⊕ Fin n) a1 ) (@Term.var  (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a2)


 exact QF.todisjunctionAtomicblocks
 let ter := (@Term.var  (order_language[[@univ ℝ]]) ((Fin 1) ⊕ Fin n) a1 )
 rename_i l
 by_cases neq : l=0
 rw [neq] at t2 g
 let const := Term.func g t2
 let QF:= Atomicblock.equal const ter
 exact QF.todisjunctionAtomicblocks 

 have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l)  := func0empty neq
 apply F_empty.elim'
 apply g


 rename_i l


 by_cases neq : l=0
 rw [neq] at f t1
 let const1 := Term.func f t1
 let QF:= Atomicblock.equal const1 t2
 exact QF.todisjunctionAtomicblocks

 have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions l)  := func0empty neq
 apply F_empty.elim'
 apply f

 let QF :=  Atomicblock.rel R f
 exact QF.todisjunctionAtomicblocks
 exact disjunctionAtomicblocks.atom (Atomicblock.falsum)
 let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (i:Fin 2)=>  if i=0 then t1 else t2  )
 let QF2 := Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (i:Fin 2)=> if i=0 then t2 else t1 )
 exact disjunctionAtomicblocks.or QF1.todisjunctionAtomicblocks QF2.todisjunctionAtomicblocks
 rename_i l
 by_cases neq: l=2
 let ter1:= f ⟨0, by linarith⟩
 let ter2 := f ⟨1, by linarith⟩
 let QF1 := Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (i:Fin 2)=>  if i=0 then ter2 else ter1  )
 let QF2 := Atomicblock.equal ter1 ter2
 exact disjunctionAtomicblocks.or QF1.todisjunctionAtomicblocks QF2.todisjunctionAtomicblocks
 exfalso
 have F_empty : IsEmpty (order_language[[ℝ]].Relations l)  := rel2empty neq
 apply F_empty.elim'
 apply R


 exact f.todisjunctionAtomicblocks


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
 
  
 



def varelimAtomicblock {n}  (ter : order_language[[@univ ℝ]].Term (Fin 1 ⊕ Fin n)) : Atomicblock (order_language[[@univ ℝ]]) (Fin 1) (n+1) → Atomicblock (order_language[[@univ ℝ]]) (Fin 1) n
  | .truth       => Atomicblock.truth
  | .falsum      => Atomicblock.falsum

  | .and f₁ f₂   => (varelimAtomicblock  ter f₁).and (varelimAtomicblock  ter f₁)

  | .equal t₁ t₂ => by 
    expose_names
    rcases t₁  with a1 | ⟨h, t_1⟩
    rcases t₂ with a2 | ⟨g, t_2⟩
    by_cases neq1 : a1=Sum.inr ⟨n, by simp⟩ 
          
    by_cases neq2 : a2=Sum.inr ⟨n, by simp⟩ 
          
    exact Atomicblock.falsum
          
    exact Atomicblock.equal ter  (Term.var (reindex a2 neq2))
    by_cases neq2 : a2=Sum.inr ⟨n, by simp⟩ 
    
    exact Atomicblock.equal  (Term.var (reindex a1 neq1)) ter
          
    exact Atomicblock.equal (Term.var ((reindex a1 neq1))) (Term.var ((reindex a2 neq2)))
    rename_i p
    by_cases p_val : p=0
    subst p
    by_cases ineqa : a1=Sum.inr ⟨n, by simp⟩ 
    exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2) => if j=0 then ter else Term.func g (fun i: Fin 0 =>  nomatch i))
    exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2) => if j=0 then Term.var (reindex a1 ineqa ) else Term.func g (fun i: Fin 0 =>  nomatch i))

    have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := func0empty p_val
    apply F_empty.elim'
    apply g
    
    rename_i t
    by_cases t_val : t=0

    case neg =>
          have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := func0empty t_val
          apply F_empty.elim'
          apply h
    
    case pos =>
          subst t
          rcases t₂  with a1 | ⟨g, t_2⟩
          · by_cases ineqa :a1=Sum.inr ⟨n, by simp⟩ 
            exact Atomicblock.equal (Term.func h (fun i: Fin 0=>  nomatch i)) ter
            exact Atomicblock.equal (Term.func h (fun i: Fin 0=>  nomatch i)) ( Term.var (reindex a1 ineqa))

          · rename_i e
            by_cases neq2 : e=0
            rw [neq2] at g t_2
            exact Atomicblock.equal (Term.func h (fun i: Fin 0=>  nomatch i)) (Term.func g (fun i: Fin 0=>  nomatch i) )

            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := func0empty neq2
            apply F_empty.elim'
            apply g



  | .rel R ts    => by 
    expose_names
    by_cases l_val : l=2

    case neg =>
      have F_empty : IsEmpty (order_language[[@univ ℝ]].Relations l):= rel2empty l_val
      apply F_empty.elim'
      exact R

    case pos =>
      subst l
      let t1 := ts ⟨0, by linarith⟩
      let t2 := ts ⟨1, by linarith⟩

      rcases t1 with a1 | ⟨h, t_1⟩
      rcases t2 with a2 | ⟨g, t_2⟩
      
      by_cases neq1 : a1=Sum.inr ⟨n, by simp⟩ 
          
      by_cases neq2 : a2=Sum.inr ⟨n, by simp⟩ 
          
      exact Atomicblock.falsum
          
      exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then ter else Term.var ((reindex a2 neq2)))
      by_cases neq2 : a2=Sum.inr ⟨n, by simp⟩ 
          
      exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.var (reindex a1 neq1) else ter)
          
      exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then Term.var ((reindex a1 neq1)) else Term.var ((reindex a2 neq2)))
      rename_i p
      by_cases p_val : p=0
      subst p
      by_cases ineqa : a1=Sum.inr ⟨n, by simp⟩ 
      exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2) => if j=0 then ter else Term.func g (fun i: Fin 0 =>  nomatch i))
      exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2) => if j=0 then Term.var (reindex a1 ineqa ) else Term.func g (fun i: Fin 0 =>  nomatch i))

      have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions p)  := func0empty p_val
      apply F_empty.elim'
      apply g

      rename_i t
      by_cases t_val : t=0

      case neg =>
          have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions t)  := func0empty t_val
          apply F_empty.elim'
          apply h

      case pos =>
          subst t
          rcases t2 with a1 | ⟨g, t_2⟩
          · by_cases ineqa :a1=Sum.inr ⟨n, by simp⟩ 
            exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else ter)
            exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.var (reindex a1 ineqa))

          · rename_i e
            by_cases neq2 : e=0
            rw [neq2] at g t_2
            exact Atomicblock.rel (Sum.inl ordsymbol.lt) (fun (j:Fin 2)=>  if j=0 then  Term.func h (fun i: Fin 0=>  nomatch i) else Term.func g (fun i: Fin 0=>  nomatch i) )

            have F_empty : IsEmpty (order_language[[@univ ℝ]].Functions e)  := func0empty neq2
            apply F_empty.elim'
            apply g





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
def Existblock.elim {n}:Existblock (order_language[[@univ ℝ]]) (Fin 1) (n+1)→ disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n):= by
intro a 
exact a.todisjunctionAtomicblocks.elim


-----------------------------------------------------------

/--
Function that takes a disjunction of existsblocks preceded by an existential quantifier and sends it to a disjunction of Existblocks without a quantifier. 
It again uses the distributivity of the existential quantifier over the disjunction. The function outputs a disjunction of Relblock, which is a particular case of a disjunction of existblocks.
-/
@[simp]
def disjunctionExistblocks.elim  {n:ℕ } : disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[ℝ]]) (Fin 1) (n):= by 
intro existbl
rcases existbl with ⟨ ex⟩ | ⟨ex1,ex2⟩ 
exact ex.elim.todisjunctionExistblocks
exact ex1.elim.or ex2.elim


def disjunctionAtomicblocks.elim {n}:disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1)→ disjunctionAtomicblocks (order_language[[@univ ℝ]]) (Fin 1) (n):= by
intro disA
rcases disA with ⟨atom ⟩ | ⟨d1, d2 ⟩
exact  disjunctionAtomicblocks.atom atom.elim
exact  (d1.elim).or (d2.elim)


/--
This function shows how to eliminate the quantifier from an expression of the form \exist(\not disjunctionExistblocks). It does this by using
de Morgan's laws. 
-/
def notExistblockelim {n : ℕ} : disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n+1) → disjunctionExistblocks (order_language[[@univ ℝ]]) (Fin 1) (n)
  | .existbl eb => match eb with
    | .lit lit => (disjunctionExistblocks.existbl (Existblock.lit lit.not )).elim
    | .and ex₁ ex₂ => (notExistblockelim (disjunctionExistblocks.existbl ex₁)).or (notExistblockelim (disjunctionExistblocks.existbl ex₂))
  | .or f₁ f₂   => (notExistblockelim f₁).and (notExistblockelim f₂)




------------------------------------------------------------------

/--
Sends ImpAllFreeFormula `φ` in the language of `(ℝ, <)` to a QFImpAllFreeFormula that is equivalent to it.
-/
def ImpAllFreeFormula.toQFImpAllFreeFormula  {n:ℕ } : ImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) (n) → QFImpAllFreeFormula (order_language[[@univ ℝ]]) (Fin 1) n :=
  
-- We first define a helper function that sends an ImpAllFreeFormula formula to a disjunction of existblocks. We only use this helper function
-- whenever we have a formula of the form .exists. Normally, an existblock is thought of as being preceded by an exist, however, in the output of this function. it is eliminated. 
-- We need that the output be an existblock instead of a Relblock, since we are allowing equal and not to be in the formulas. 

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
