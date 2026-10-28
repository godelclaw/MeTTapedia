import Mettapedia.Computability.PNP.V13RealRungOneLinear

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check V13RealLinearPublic
#check V13RealLinearWorld
#check v13RealLinearPublicInput
#check v13RealLinearFullDecoder
#check v13RealLinear_fullPublic_decodes_target
#check v13RealLinear_fullPublic_determines_target
#check v13RealLinearEquiv_ext
#check v13RealLinearComp
#check V13RealLinearPublicCoordinate
#check V13RealLinearCoordinateDeterminesTarget
#check V13RealLinearPublicSurfaceCertificate
#check v13RealLinear_no_single_public_coordinate_determines_target_of_spare
#check v13RealLinear_publicSurfaceCertificate

theorem v13RealLinearRegression_full_decoding_small :
    ∀ omega : V13RealLinearWorld 2,
      v13RealLinearFullDecoder 0 (v13RealLinearPublicInput omega) =
        v13RealLinearTarget 0 omega := by
  exact v13RealLinear_fullPublic_decodes_target 0

theorem v13RealLinearRegression_no_single_coordinate_small :
    ∀ coordinate : V13RealLinearPublicCoordinate 2,
      ¬ V13RealLinearCoordinateDeterminesTarget 0 coordinate := by
  exact
    v13RealLinear_no_single_public_coordinate_determines_target_of_spare
      0 1 (by decide)

theorem v13RealLinearRegression_publicSurfaceCertificate_small :
    V13RealLinearPublicSurfaceCertificate 2 := by
  exact v13RealLinear_publicSurfaceCertificate

#print axioms v13RealLinear_fullPublic_decodes_target
#print axioms v13RealLinear_fullPublic_determines_target
#print axioms v13RealLinearEquiv_ext
#print axioms v13RealLinearComp
#print axioms v13RealLinear_no_single_public_coordinate_determines_target_of_spare
#print axioms v13RealLinear_publicSurfaceCertificate
#print axioms v13RealLinearRegression_full_decoding_small
#print axioms v13RealLinearRegression_no_single_coordinate_small
#print axioms v13RealLinearRegression_publicSurfaceCertificate_small

end Mettapedia.Computability.PNP
