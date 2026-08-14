import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-!
# OUR fixed-trace-point topology screen

The fixed-base three-selector refutation leaves open a larger parameter
synthesis and, if necessary, additional trace-topology coordinates.  This
module screens the most direct such coordinate: gate the derivative-axis
character by the condition that the trace permutation has exactly one fixed
field.

The gate detects OUR singleton-trace relation with signed `H(4)` weight `32`.
It is not, however, already a one-coordinate repair: the genuine fundamental
three-cut relation has signed weight `-64` for the same gated character, so
after singleton normalization its value is `-2`.  Thus a nonzero contribution
in this direction would spoil the currently zero fundamental row unless a
further, independently certified cancellation direction accompanies it.

This is an OUR exact finite screen.  It does not yet construct a
field-relabel-descended coordinate, solve the full existing parameter system,
or assert descent through the physical relation submodule.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFixedPointTopologyScreen

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation

/-- OUR number of genuine one-letter traces in a labeled trace layout.  Unlike
`Equiv.Perm.cycleType`, this retains fixed points. -/
def ourFixedTracePointCount
    (sector : LabeledLocalWordSector 7 2) : ℕ :=
  (Finset.univ.filter (fun field => sector.trace field = field)).card

/-- OUR fixed-point-gated derivative-axis character. -/
def ourFixedPointTraceAxisMultiplicity
    (sector : LabeledLocalWordSector 7 2) : ℚ :=
  if ourFixedTracePointCount sector = 1 then
    derivativeAxisWordMultiplicity [0, 2] sector
  else 0

/-- OUR bounded signed `H(4)` numerator for the fixed-point-gated character. -/
def ourFixedPointTraceAxisSignedWeight
    (sector : LabeledLocalWordSector 7 2) : ℚ :=
  ∑ h : Hypercubic4,
    sector.tensorSign h *
      ourFixedPointTraceAxisMultiplicity (sector.hypercubicAct h)

set_option maxRecDepth 100000 in
theorem ourSingletonTrace_fixedTracePointCount :
    ourFixedTracePointCount ourSingletonTraceLabeled = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourSingletonTrace_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight ourSingletonTraceLabeled = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight ourFundamentalThreeCutBaseLabeled = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight
      ourFundamentalThreeCutSwapFirstSecondLabeled = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight
      ourFundamentalThreeCutSwapFirstThirdLabeled = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight
      ourFundamentalThreeCutSwapSecondThirdLabeled = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight ourFundamentalThreeCutForwardLabeled = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight ourFundamentalThreeCutBackwardLabeled = 0 := by
  decide +kernel

/-- The exact fundamental three-cut numerator of OUR naive fixed-point gate.
The signs are the actual six-term fundamental trace relation signs. -/
theorem ourFundamentalThreeCut_fixedPointTraceAxisSignedWeight :
    ourFixedPointTraceAxisSignedWeight ourFundamentalThreeCutBaseLabeled -
        ourFixedPointTraceAxisSignedWeight
          ourFundamentalThreeCutSwapFirstSecondLabeled -
          ourFixedPointTraceAxisSignedWeight
            ourFundamentalThreeCutSwapFirstThirdLabeled -
            ourFixedPointTraceAxisSignedWeight
              ourFundamentalThreeCutSwapSecondThirdLabeled +
              ourFixedPointTraceAxisSignedWeight
                ourFundamentalThreeCutForwardLabeled +
                ourFixedPointTraceAxisSignedWeight
                  ourFundamentalThreeCutBackwardLabeled = -64 := by
  rw [ourFundamentalThreeCutBase_fixedPointTraceAxisSignedWeight,
    ourFundamentalThreeCutSwapFirstSecond_fixedPointTraceAxisSignedWeight,
    ourFundamentalThreeCutSwapFirstThird_fixedPointTraceAxisSignedWeight,
    ourFundamentalThreeCutSwapSecondThird_fixedPointTraceAxisSignedWeight,
    ourFundamentalThreeCutForward_fixedPointTraceAxisSignedWeight,
    ourFundamentalThreeCutBackward_fixedPointTraceAxisSignedWeight]
  norm_num

/-- Singleton normalization makes the same gated character equal to `-2` on
the complete fundamental three-cut relation. -/
theorem ourFundamentalThreeCut_fixedPointTraceAxis_normalizedValue :
    (-64 : ℚ) / 32 = -2 := by
  norm_num

#print axioms ourSingletonTrace_fixedTracePointCount
#print axioms ourSingletonTrace_fixedPointTraceAxisSignedWeight
#print axioms ourFundamentalThreeCut_fixedPointTraceAxisSignedWeight

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFixedPointTopologyScreen
