import LeanOminimal.ominimality


-- Most important definitions
#check Real_Ominimal

#check DLO
#check Real_DLO

#check DLO.interval.is_finite_union_of_intervalsP
#check DLO.interval.is_finite_union_of_intervalsP.intersection

section Formulas
open FirstOrder.Language

#check ImpAllFreeFormula
#check QFImpAllFreeFormula
#check Existblock
#check Atomicblock
#check Relblock
#check disjunctionExistblocks
#check disjunctionAtomicblocks
#check disjunctionRelblocks
end Formulas

section Definability
open Definability

#check QFImpAllFreeFormula_setOf_is_FiniteUnion
#check definable_sets_are_finite_unions
#check finite_unions_are_definable
end Definability
