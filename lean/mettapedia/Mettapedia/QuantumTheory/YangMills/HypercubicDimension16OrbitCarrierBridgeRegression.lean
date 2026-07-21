import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16OrbitCarrierBridge

/-!
# Regression checks for the exact quotient-to-orbit carrier bridge
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16OrbitCarrierBridgeRegression

open HypercubicDimension16ContextualQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCarrierBridge
open V14HypercubicFDCensus

def fixed_sector_target_is_the_finite_labeled_carrier
    (fieldCount derivativeCount : ℕ) :
    OrientedLocalSector fieldCount derivativeCount ≃
      LabeledLocalWordSector fieldCount derivativeCount :=
  orientedLocalSectorEquivLabeled fieldCount derivativeCount

theorem fixed_sector_bridge_is_field_relabel_equivariant
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (orientedLocalRelabel rename sector) =
      LabeledLocalWordSector.relabel rename
        (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector) :=
  orientedLocalSectorEquivLabeled_relabel rename sector

theorem fixed_sector_bridge_is_signed_hypercubic_equivariant
    {fieldCount derivativeCount : ℕ}
    (h : Hypercubic4)
    (sector : OrientedLocalSector fieldCount derivativeCount) :
    orientedLocalSectorEquivLabeled fieldCount derivativeCount
        (sector.hypercubicAct h) =
      LabeledLocalWordSector.hypercubicAct h
        (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector) ∧
      LabeledLocalWordSector.tensorSign h
          (orientedLocalSectorEquivLabeled fieldCount derivativeCount sector) =
        sector.tensorSign h :=
  ⟨orientedLocalSectorEquivLabeled_hypercubicAct h sector,
    orientedLocalSectorEquivLabeled_tensorSign h sector⟩

def genuine_field_label_orbits_are_identified
    (fieldCount derivativeCount : ℕ) :
    OrientedLocalRelabelOrbitCarrier fieldCount derivativeCount ≃
      FieldRelabelOrbitCarrier fieldCount derivativeCount :=
  orientedLocalOrbitEquivFieldRelabelOrbit fieldCount derivativeCount

#print axioms planeDerivativeFamilyEquivDecoration
#print axioms orientedLocalSectorEquivLabeled
#print axioms orientedLocalSectorEquivLabeled_relabel
#print axioms orientedLocalSectorEquivLabeled_hypercubicAct
#print axioms orientedLocalSectorEquivLabeled_tensorSign
#print axioms orientedLocalOrbitEquivFieldRelabelOrbit

end HypercubicDimension16OrbitCarrierBridgeRegression
end YangMills
end QuantumTheory
end Mettapedia
