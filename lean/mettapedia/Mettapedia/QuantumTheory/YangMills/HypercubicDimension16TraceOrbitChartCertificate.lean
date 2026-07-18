import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitProductSignatureCertificate

/-!
# Kernel-checked separation certificate for the eight-field orbit chart

The standard product of the eight rooted trace codes is evaluated at
`X = 1` after each of the 24 unsigned coordinate permutations.  Bounded
kernel replays prove that the resulting canonical values are distinct on all
11,654 decoded representatives.  Only the one-way invariant implication is
used: unequal values cannot lie in the same literal hypercubic orbit.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartCertificate

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitSignature
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitProductSignatureCertificate

/-- The standard canonical product signature on a decoded representative. -/
def representativeCanonicalProductSignature
    (index : PositiveRepresentativeIndex) : Nat :=
  canonicalUnsignedProductSignature (positiveRepresentativeTarget index)

/-- The decoded representatives have pairwise distinct standard product
signatures. -/
theorem representativeCanonicalProductSignature_injective :
    Function.Injective representativeCanonicalProductSignature := by
  intro left right hequal
  apply directRepresentativeCanonicalProductSignature_injective
  rw [directRepresentativeCanonicalProductSignature_eq,
    directRepresentativeCanonicalProductSignature_eq]
  exact hequal

/-- Distinct decoded chart entries lie in distinct literal hypercubic
orbits. -/
theorem positiveRepresentativeTargets_hypercubic_separated
    {left right : PositiveRepresentativeIndex} (hdifferent : left ≠ right) :
    ∀ h : Hypercubic4,
      (positiveRepresentativeTarget left).hypercubicAct h ≠
        positiveRepresentativeTarget right := by
  apply not_hypercubic_related_of_canonicalProductSignature_ne
  exact fun hequal => hdifferent
    (representativeCanonicalProductSignature_injective hequal)

end HypercubicDimension16TraceOrbitChartCertificate
end YangMills
end QuantumTheory
end Mettapedia
