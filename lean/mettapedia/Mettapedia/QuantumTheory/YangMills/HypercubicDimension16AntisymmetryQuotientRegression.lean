import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16AntisymmetryQuotient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Regression checks for the exact field-strength antisymmetry quotient
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16AntisymmetryQuotientRegression

open HypercubicDimension16AntisymmetryQuotient

theorem orderedPair_space_finrank :
    Module.finrank ℚ AxisPairSpace = 16 := by
  rw [Module.finrank_finsupp_self]
  norm_num [Fintype.card_prod]

theorem orientedPlane_space_finrank :
    Module.finrank ℚ OrientedPlaneSpace = 6 := by
  rw [Module.finrank_finsupp_self]
  rfl

theorem relationCoordinate_space_finrank :
    Module.finrank ℚ AntisymmetryRelationCoordinateSpace = 10 := by
  rw [Module.finrank_finsupp_self]
  norm_num [Fintype.card_sum]

def exact_six_plus_ten_decomposition :
    AxisPairSpace ≃ₗ[ℚ]
      OrientedPlaneSpace × AntisymmetryRelationCoordinateSpace :=
  axisPairDecompositionEquiv

theorem literal_rows_are_the_full_kernel :
    LinearMap.ker normalizeAxisPair = axisPairAntisymmetrySubmodule :=
  ker_normalizeAxisPair_eq_antisymmetrySubmodule

def quotient_is_oriented_plane_space :
    (AxisPairSpace ⧸ axisPairAntisymmetrySubmodule) ≃ₗ[ℚ]
      OrientedPlaneSpace :=
  axisPairAntisymmetryQuotientEquiv

theorem simultaneous_literal_rows_are_the_full_kernel (fieldCount : ℕ) :
    LinearMap.ker (normalizeFieldAxes fieldCount) =
      fieldAxisAntisymmetrySubmodule fieldCount :=
  ker_normalizeFieldAxes_eq_fieldAxisAntisymmetrySubmodule fieldCount

def simultaneous_quotient_is_oriented_assignment_space (fieldCount : ℕ) :
    (FieldAxisAssignmentSpace fieldCount ⧸
        fieldAxisAntisymmetrySubmodule fieldCount) ≃ₗ[ℚ]
      OrientedFieldAssignmentSpace fieldCount :=
  fieldAxisAntisymmetryQuotientEquiv fieldCount

theorem normalization_is_signed_hypercubic_equivariant
    (h : V14HypercubicFDCensus.Hypercubic4)
    (value : AxisPairSpace) :
    normalizeAxisPair (signedAxisPairAction h value) =
      signedOrientedPlaneAction h (normalizeAxisPair value) :=
  normalizeAxisPair_equivariant h value

#print axioms axisPairDecompositionEquiv
#print axioms ker_normalizeAxisPair_eq_antisymmetrySubmodule
#print axioms axisPairAntisymmetryQuotientEquiv
#print axioms normalizeAxisPair_equivariant
#print axioms ker_normalizeFieldAxes_eq_fieldAxisAntisymmetrySubmodule
#print axioms fieldAxisAntisymmetryQuotientEquiv

end HypercubicDimension16AntisymmetryQuotientRegression
end YangMills
end QuantumTheory
end Mettapedia
