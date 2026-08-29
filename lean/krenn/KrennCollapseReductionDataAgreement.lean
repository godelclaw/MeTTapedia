import KrennCollapseReductionReflection
import KrennCollapseComponentContainmentDataDefs

/-!
The top-down determinant reduction and the bottom-up component-containment
certificate corpus use the same fourteen reduced binomial relations.

This file keeps that agreement as a small independent kernel-checked seam.
-/

namespace Krenn.CollapseReductionDataAgreement

open Krenn.LatticeCombinationReflection

macro "closeRelation" : tactic =>
  `(tactic|
    apply congrArg₂ Binomial.mk <;>
      ext coordinate <;>
      fin_cases coordinate <;>
      simp only [CollapseComponentContainmentData.squarefreeExponent_apply,
        Finsupp.single_apply, Finsupp.add_apply] <;>
      decide)

/-- The relation vocabulary derived from the eighteen raw collapse
determinants is exactly the vocabulary consumed by the containment corpus. -/
theorem relation_eq_reducedRelation (index : Fin 14) :
    CollapseComponentContainmentData.relation index =
      CollapseReductionReflection.reducedRelation index := by
  fin_cases index
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 129
         right := CollapseComponentContainmentData.squarefreeExponent 36 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 0 1 + Finsupp.single 7 1
         right := Finsupp.single 2 1 + Finsupp.single 5 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 8193
         right := CollapseComponentContainmentData.squarefreeExponent 8519680 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 0 1 + Finsupp.single 13 1
         right := Finsupp.single 17 1 + Finsupp.single 23 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 258
         right := CollapseComponentContainmentData.squarefreeExponent 72 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 1 1 + Finsupp.single 8 1
         right := Finsupp.single 3 1 + Finsupp.single 6 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 8388610
         right := CollapseComponentContainmentData.squarefreeExponent 4194308 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 1 1 + Finsupp.single 23 1
         right := Finsupp.single 2 1 + Finsupp.single 22 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 33554440
         right := CollapseComponentContainmentData.squarefreeExponent 16777232 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 3 1 + Finsupp.single 25 1
         right := Finsupp.single 4 1 + Finsupp.single 24 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 1048592
         right := CollapseComponentContainmentData.squarefreeExponent 2097408 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 4 1 + Finsupp.single 20 1
         right := Finsupp.single 8 1 + Finsupp.single 21 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 8224
         right := CollapseComponentContainmentData.squarefreeExponent 528384 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 5 1 + Finsupp.single 13 1
         right := Finsupp.single 12 1 + Finsupp.single 19 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 524352
         right := CollapseComponentContainmentData.squarefreeExponent 262272 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 6 1 + Finsupp.single 19 1
         right := Finsupp.single 7 1 + Finsupp.single 18 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 66048
         right := CollapseComponentContainmentData.squarefreeExponent 18432 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 9 1 + Finsupp.single 16 1
         right := Finsupp.single 11 1 + Finsupp.single 14 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 262656
         right := CollapseComponentContainmentData.squarefreeExponent 1048576 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 9 1 + Finsupp.single 18 1
         right := Finsupp.single 20 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 132096
         right := CollapseComponentContainmentData.squarefreeExponent 36864 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 10 1 + Finsupp.single 17 1
         right := Finsupp.single 12 1 + Finsupp.single 15 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 2098176
         right := CollapseComponentContainmentData.squarefreeExponent 2048 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 10 1 + Finsupp.single 21 1
         right := Finsupp.single 11 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 4210688
         right := CollapseComponentContainmentData.squarefreeExponent 16777216 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 14 1 + Finsupp.single 22 1
         right := Finsupp.single 24 1 } : Binomial (Fin 26))
    closeRelation
  · change
      ({ left := CollapseComponentContainmentData.squarefreeExponent 33587200
         right := CollapseComponentContainmentData.squarefreeExponent 65536 } :
        Binomial (Fin 26)) =
      ({ left := Finsupp.single 15 1 + Finsupp.single 25 1
         right := Finsupp.single 16 1 } : Binomial (Fin 26))
    closeRelation

/-- Raw determinant collapse therefore establishes the exact reduced
relations expected by the bottom-up containment certificates. -/
theorem containment_relations_of_raw_collapse
    {R : Type*} [CommRing R]
    (values : Fin 30 → R)
    (collapse : CollapseReductionReflection.SatisfiesRawCollapse values) :
    ∀ index,
      monomial (CollapseReductionReflection.reduceRaw values)
          (CollapseComponentContainmentData.relation index).left =
        monomial (CollapseReductionReflection.reduceRaw values)
          (CollapseComponentContainmentData.relation index).right := by
  intro index
  rw [relation_eq_reducedRelation]
  exact CollapseReductionReflection.reduced_relations_of_raw_collapse
    values collapse index

end Krenn.CollapseReductionDataAgreement

#print axioms Krenn.CollapseReductionDataAgreement.relation_eq_reducedRelation
#print axioms Krenn.CollapseReductionDataAgreement.containment_relations_of_raw_collapse
