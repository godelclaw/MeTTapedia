import Mettapedia.QuantumTheory.YangMills.SU2LatticeFDCensusNoGo

/-!
# Regression checks for the SU(2) Wilson-coordinate census no-go
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2LatticeFDCensusNoGoRegression

open SU2LatticeFDCensusNoGo

example (F : CartanCurvature) :
    iteratedDeriv 4
        (fun t : ℝ =>
          su2HypercubicQuarticWilsonObservable (cartanLinkChart t F)) 0 =
      6 * hypercubicQuarticJet F :=
  su2HypercubicQuarticWilsonObservable_fourthCartanJet F

example (Operator : Type*) [Fintype Operator] :
    ¬ Nonempty (FaithfulDimension16WilsonCoordinateCertificate
      .o9OffShell Operator) :=
  no_faithfulDimension16WilsonCoordinateCertificate_offShell Operator

example (variant : CensusConstructionVariant)
    (Operator : Type*) [Fintype Operator] :
    ¬ Nonempty (variant.SpanningCertificate Operator) :=
  no_censusConstructionVariant_spanningCertificate variant Operator

#print axioms su2CartanMatrix_mem
#print axioms specialUnitaryWilsonPotential_su2CartanElement
#print axioms plaquetteHolonomy_cartanLinkChart
#print axioms plaquettePotential_cartanLinkChart
#print axioms su2HypercubicQuarticWilsonObservable_gaugeInvariant
#print axioms singleCartanWilsonSquare_fourthJet
#print axioms su2HypercubicQuarticWilsonObservable_fourthCartanJet
#print axioms mixingRotation_orthogonal
#print axioms hypercubicQuarticJet_not_lorentzInvariant
#print axioms no_O9WilsonCensusSpanningCore
#print axioms no_faithfulDimension16WilsonCoordinateCertificate_offShell
#print axioms no_faithfulDimension16WilsonCoordinateCertificate_onShell
#print axioms no_censusConstructionVariant_spanningCertificate
#print axioms every_censusConstructionVariant_obstructed
#print axioms ymMove7_dimension16WilsonCoordinate_terminalNoGo

end SU2LatticeFDCensusNoGoRegression
end YangMills
end QuantumTheory
end Mettapedia

