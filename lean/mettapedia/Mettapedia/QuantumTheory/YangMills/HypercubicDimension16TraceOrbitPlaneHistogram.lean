import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SignedOrbitCoinvariants

/-!
# Plane-multiplicity invariant for the derivative-free eight-field carrier

The six plane multiplicities are defined on the standard labeled carrier,
proved invariant under simultaneous field relabeling, and only then descended
to the genuine orbit carrier.  Equality in the carrier therefore implies
equality of this deliberately coarse invariant.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitPlaneHistogram

open SU2LatticeFDCensusNoGo
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants

abbrev FieldEightLabeledSector := LabeledLocalWordSector 8 0

/-- Multiplicity of one oriented coordinate plane among the eight field
strengths. -/
def labeledPlaneMultiplicity (sector : FieldEightLabeledSector)
    (plane : OrientedPlane) : Nat :=
  ∑ field : Fin 8,
    if (sector.decoration.1 field).plane = plane then 1 else 0

theorem labeledPlaneMultiplicity_relabel
    (rename : Equiv.Perm (Fin 8)) (sector : FieldEightLabeledSector)
    (plane : OrientedPlane) :
    labeledPlaneMultiplicity (sector.relabel rename) plane =
      labeledPlaneMultiplicity sector plane := by
  unfold labeledPlaneMultiplicity
  calc
    (∑ field : Fin 8,
        if ((sector.relabel rename).decoration.1 field).plane = plane
          then 1 else 0) =
        ∑ field : Fin 8,
          if ((sector.relabel rename).decoration.1 (rename field)).plane = plane
            then 1 else 0 :=
      (Equiv.sum_comp rename (fun field : Fin 8 =>
        if ((sector.relabel rename).decoration.1 field).plane = plane
          then 1 else 0)).symm
    _ = ∑ field : Fin 8,
          if (sector.decoration.1 field).plane = plane then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro field _
      change (if (sector.decoration.1
        (rename.symm (rename field))).plane = plane then 1 else 0) = _
      rw [rename.symm_apply_apply]

theorem labeledPlaneMultiplicity_respects_fieldRelabelOrbit
    (left right : FieldEightLabeledSector)
    (hsame : MulAction.orbitRel (Equiv.Perm (Fin 8))
      FieldEightLabeledSector left right) :
    labeledPlaneMultiplicity left = labeledPlaneMultiplicity right := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
  rcases hsame with ⟨rename, hrename⟩
  change right.relabel rename = left at hrename
  funext plane
  rw [← hrename, labeledPlaneMultiplicity_relabel]

/-- The six multiplicities on the genuine field-relabel orbit carrier. -/
def fieldEightOrbitPlaneHistogram :
    FieldEightOrbitCarrier → OrientedPlane → Nat :=
  Quotient.lift labeledPlaneMultiplicity
    labeledPlaneMultiplicity_respects_fieldRelabelOrbit

@[simp] theorem fieldEightOrbitPlaneHistogram_mk
    (sector : FieldEightLabeledSector) :
    fieldEightOrbitPlaneHistogram (Quotient.mk _ sector) =
      labeledPlaneMultiplicity sector :=
  rfl

end HypercubicDimension16TraceOrbitPlaneHistogram
end YangMills
end QuantumTheory
end Mettapedia
