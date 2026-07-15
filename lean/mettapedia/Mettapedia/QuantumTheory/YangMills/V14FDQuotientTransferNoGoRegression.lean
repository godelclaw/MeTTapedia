import Mettapedia.QuantumTheory.YangMills.V14FDQuotientTransferNoGo

/-!
# Regressions for the v14 full `F,D` quotient-transfer no-go
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14FDQuotientTransferNoGoRegression

open V14FDQuotientTransferNoGo

example : actionLaplacianCanonicalDimension ≤ 16 :=
  actionLaplacianCanonicalDimension_le_sixteen

example : actionLaplacianDensity ibpWitnessField = 1 :=
  actionLaplacianDensity_witness

example :
    homogeneousActionLaplacian homogeneousActionJetWitness = 1 :=
  homogeneousActionLaplacian_witness

example : ¬ AssociatedRadialImplementsCanonicalCutoff :=
  not_associatedRadialImplementsCanonicalCutoff

example : ¬ IndependentRadialImplementsCanonicalCutoff :=
  not_independentRadialImplementsCanonicalCutoff

example : ¬ Nonempty (V14FaithfulFDTransferSocket .onShell) :=
  no_faithfulFDTransferSocket .onShell

example : ¬ Nonempty (V14FaithfulFDTransferSocket .offShell) :=
  no_faithfulFDTransferSocket .offShell

example :
    ¬ Nonempty (V14FaithfulAssociatedGradedFDTransferSocket .onShell) :=
  no_faithfulAssociatedGradedFDTransferSocket .onShell

example :
    ¬ Nonempty (V14FaithfulAssociatedGradedFDTransferSocket .offShell) :=
  no_faithfulAssociatedGradedFDTransferSocket .offShell

#print axioms actionLaplacianDensity_gaugeInvariant
#print axioms actionLaplacianDensity_witness
#print axioms homogeneousActionLaplacian_smul
#print axioms homogeneousActionLaplacian_witness
#print axioms radialExtraction16_fixes_homogeneousActionLaplacian
#print axioms radialExtraction16_fixes_associatedHighDerivativeJet
#print axioms independentRadialExtraction_fixes_highDerivativeJet
#print axioms not_associatedRadialImplementsCanonicalCutoff
#print axioms not_independentRadialImplementsCanonicalCutoff
#print axioms no_faithfulFDTransferSocket
#print axioms no_faithfulAssociatedGradedFDTransferSocket
#print axioms no_rgCompatibleFDTransferSocket
#print axioms v14FDTransferDecisionMatrix_agrees
#print axioms v14_fullFD_quotientTransfer_noGo

end V14FDQuotientTransferNoGoRegression
end YangMills
end QuantumTheory
end Mettapedia
