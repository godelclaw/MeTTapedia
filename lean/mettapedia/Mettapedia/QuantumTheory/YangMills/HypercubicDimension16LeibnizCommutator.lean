import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CovariantCommutator

/-!
# OUR Leibniz-correct covariant-derivative commutator row

A `CovariantCommutatorSite` selects two adjacent derivatives of one field
letter, `X = D_{w₁} D_a D_b D_{w₂} F`: `w₁` lists the field's derivatives at
smaller (outer) positions and `w₂` those at larger (inner) positions.  With
`Z = D_{w₂} F` the field identity is

`D_{w₁} (D_a D_b Z - D_b D_a Z) = D_{w₁} (F_ab Z - Z F_ab)`,

and the adjoint Leibniz rule distributes `w₁` over each product,

`D_{w₁} (F_ab Z) = ∑_{S ⊆ w₁} (D_S F_ab) (D_{w₁ ∖ S} Z)`,

where each factor keeps the relative order of its derivatives.  The row of
`HypercubicDimension16CovariantCommutator` keeps every outer derivative on
`Z`, which is the `S = ∅` term alone, so it is a field identity exactly when
`w₁` is empty.

This module defines the corrected row

`[X] - [X with a, b exchanged] - ∑_{S ⊆ w₁} ([F_ab before X, carrying S] - [F_ab after X, carrying S])`.

The positions in `S` change owner from the field to the inserted curvature
letter; axes, planes and trace cycle are those of the original insertion.  The
row is equivariant under the signed hypercubic action and equals the earlier
row whenever `w₁` is empty.  The earlier definitions are unchanged.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16LeibnizCommutator

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator

/-! ## The outer derivatives of the commutator's field -/

/-- OUR derivative positions of the site's field outside the commutator pair. -/
def outerSameOwnerPositions {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) :
    Finset (Fin (dimension16DerivativeCount carrier.1)) :=
  Finset.univ.filter fun position =>
    position < site.outer ∧
      carrier.2.derivativeWord.ownerAtPosition position = site.field

@[simp] theorem mem_outerSameOwnerPositions {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    position ∈ outerSameOwnerPositions site ↔
      position < site.outer ∧
        carrier.2.derivativeWord.ownerAtPosition position = site.field := by
  simp [outerSameOwnerPositions]

theorem outerSameOwnerPositions_act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    outerSameOwnerPositions (site.act h) = outerSameOwnerPositions site :=
  rfl

theorem outerSameOwnerPositions_subset_retained {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) :
    outerSameOwnerPositions site ⊆
      retainedDerivativePositions site.outer site.inner := by
  intro position hposition
  rw [mem_outerSameOwnerPositions] at hposition
  have hlt : position < site.inner := lt_trans hposition.1 site.outer_lt_inner
  simp [retainedDerivativePositions, ne_of_lt hposition.1, ne_of_lt hlt]

/-! ## Curvature insertion carrying a set of outer derivatives -/

/-- OUR owner of a retained derivative position once the inserted curvature
letter, the new last field, takes the retained positions in `moved`. -/
def leibnizOwner {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (position : Fin (dimension16DerivativeCount
      (successorFieldCount carrier.1 site.fieldCount_lt_eight))) :
    Fin (carrier.1.1 + 1) :=
  if retainedDerivativeOrderEmbedding site position ∈ moved then
    Fin.last carrier.1.1
  else
    Fin.castSucc (carrier.2.derivativeWord.ownerAtPosition
      (retainedDerivativeOrderEmbedding site position))

/-- OUR curvature insertion in which the inserted letter `F_ab` carries the
derivatives at the positions in `moved`.  For `moved = ∅` it is
`insertCurvatureCarrier`. -/
def insertLeibnizCarrier {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1))) :
    RelationCarrier :=
  let targetFieldCount :=
    successorFieldCount carrier.1 site.fieldCount_lt_eight
  let curvatureFirst :=
    carrier.2.derivativeWord.axisAtPosition site.outer
  let curvatureSecond :=
    carrier.2.derivativeWord.axisAtPosition site.inner
  ⟨targetFieldCount,
    { trace := ⟨insertedTraceOrder site side⟩
      fieldFirst := Fin.lastCases curvatureFirst carrier.2.fieldFirst
      fieldSecond := Fin.lastCases curvatureSecond carrier.2.fieldSecond
      derivativeWord :=
        { ownerAtPosition := leibnizOwner site moved
          axisAtPosition := fun position =>
            carrier.2.derivativeWord.axisAtPosition
              (retainedDerivativeOrderEmbedding site position) } }⟩

theorem leibnizOwner_empty {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) :
    leibnizOwner site ∅ = fun position =>
      Fin.castSucc (carrier.2.derivativeWord.ownerAtPosition
        (retainedDerivativeOrderEmbedding site position)) := by
  funext position
  simp [leibnizOwner]

theorem insertLeibnizCarrier_empty {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide) :
    insertLeibnizCarrier site side ∅ = insertCurvatureCarrier site side := by
  unfold insertLeibnizCarrier insertCurvatureCarrier
  rw [leibnizOwner_empty]

theorem insertLeibnizCarrier_act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1))) :
    exactDimension16DerivativeAlphaReducedAct h
        (insertLeibnizCarrier site side moved) =
      insertLeibnizCarrier (site.act h) side moved := by
  let targetFieldCount :=
    successorFieldCount carrier.1 site.fieldCount_lt_eight
  change (⟨targetFieldCount,
      derivativeAlphaReducedSectorAct h
        (insertLeibnizCarrier site side moved).2⟩ : RelationCarrier) =
    ⟨targetFieldCount, (insertLeibnizCarrier (site.act h) side moved).2⟩
  apply congrArg (fun reduced =>
    (⟨targetFieldCount, reduced⟩ : RelationCarrier))
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · exact comp_lastCases h.perm
      (carrier.2.derivativeWord.axisAtPosition site.outer)
      carrier.2.fieldFirst
  · exact comp_lastCases h.perm
      (carrier.2.derivativeWord.axisAtPosition site.inner)
      carrier.2.fieldSecond
  · apply OrderedDerivativeWord.ext
    · rfl
    · rfl

/-- Moving derivatives between letters changes no axis, so the tensor sign is
that of the source carrier. -/
theorem insertLeibnizCarrier_tensorSign (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1))) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (insertLeibnizCarrier site side moved) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  have hsame :
      exactDimension16DerivativeAlphaReducedTensorSign h
          (insertLeibnizCarrier site side moved) =
        exactDimension16DerivativeAlphaReducedTensorSign h
          (insertCurvatureCarrier site side) := rfl
  rw [hsame, insertCurvatureCarrier_tensorSign]

/-! ## The corrected row -/

/-- OUR Leibniz-correct covariant-derivative commutator row. -/
def leibnizCommutatorRow {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) : RelationSpace :=
  Finsupp.single carrier 1 -
      Finsupp.single
        (swapExactDerivativePositions carrier site.outer site.inner) 1 -
    ∑ moved ∈ (outerSameOwnerPositions site).powerset,
      (Finsupp.single (insertLeibnizCarrier site .before moved) 1 -
        Finsupp.single (insertLeibnizCarrier site .after moved) 1)

/-- The corrected row is stable under the signed hypercubic action. -/
theorem leibnizCommutatorRow_equivariant (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    signedRelationAction h (leibnizCommutatorRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        leibnizCommutatorRow (site.act h) := by
  unfold leibnizCommutatorRow
  rw [outerSameOwnerPositions_act]
  simp only [map_sub, map_sum, signedRelationAction_single, one_mul,
    swapExactDerivativePositions_act,
    swapExactDerivativePositions_tensorSign,
    insertLeibnizCarrier_act, insertLeibnizCarrier_tensorSign,
    smul_sub, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, mul_one]
  simp [CovariantCommutatorSite.act]
  rfl

/-- The corrected row is the earlier row minus the Leibniz terms with at least
one moved derivative. -/
theorem leibnizCommutatorRow_eq_covariantCommutatorRow_sub
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    leibnizCommutatorRow site =
      covariantCommutatorRow site -
        ∑ moved ∈ (outerSameOwnerPositions site).powerset.erase ∅,
          (Finsupp.single (insertLeibnizCarrier site .before moved) 1 -
            Finsupp.single (insertLeibnizCarrier site .after moved) 1) := by
  unfold leibnizCommutatorRow covariantCommutatorRow
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _),
    insertLeibnizCarrier_empty, insertLeibnizCarrier_empty]
  abel

/-- Without outer derivatives on the commutator's field, the corrected row is
the earlier row. -/
theorem leibnizCommutatorRow_eq_covariantCommutatorRow
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)
    (hempty : outerSameOwnerPositions site = ∅) :
    leibnizCommutatorRow site = covariantCommutatorRow site := by
  rw [leibnizCommutatorRow_eq_covariantCommutatorRow_sub, hempty]
  simp

#print axioms insertLeibnizCarrier_empty
#print axioms insertLeibnizCarrier_act
#print axioms insertLeibnizCarrier_tensorSign
#print axioms leibnizCommutatorRow_equivariant
#print axioms leibnizCommutatorRow_eq_covariantCommutatorRow_sub
#print axioms leibnizCommutatorRow_eq_covariantCommutatorRow

end HypercubicDimension16LeibnizCommutator
end YangMills
end QuantumTheory
end Mettapedia
