import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweepCyclicCut
import Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweep

/-!
# Residual-return sweeps restricted to a carrier interval

A long physical return separator can be long along its ambient return or along
the alternating carrier.  The latter case already lies in the linear order on
which the residual-return LIFO sweep is defined.  This file restricts that
sweep to the closed interval between the endpoints of one return chord.

Consequently, a carrier interval larger than the exact number of shallow
phased states contains either a deeper return stack or two materially spaced
equal states, with every selected position still inside that interval.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnSweep
open ResidualReturnSweepCyclicCut
open RestrictedNoncrossingSweep
open ReturnSeparatorLength
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact number of two-shore residual-return states of stack depth at
most `depth` after adjoining a position phase of period `spacing + 1`. -/
def residualReturnShallowStateCount (depth spacing : Nat) : Nat :=
  2 * (spacing + 1) * (depth + 1) ^ 2

/-- The closed cyclic-coordinate interval occupied by one ordered return
chord. -/
def carrierIntervalPositions
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    Finset (CyclePosition sigma site) :=
  Finset.Icc chord.left chord.right

/-- The number of selected carrier positions is exactly the number of
distinct vertices on the corresponding carrier subwalk. -/
theorem carrierIntervalPositions_card
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    (carrierIntervalPositions sigma site chord).card =
      (residualCycleInterval sigma site chord).support.toFinset.card := by
  rw [residualCycleInterval_support_toFinset_card]
  simp only [carrierIntervalPositions, Fin.card_Icc]
  have hleft := chord.left_lt_right
  omega

/-- **Carrier-local residual-return sweep.**  If the carrier interval under
one chord contains more positions than shallow phased two-shore states, then
some selected position has a deeper return stack, or two selected positions
have equal phased states and the requested material separation. -/
theorem exists_deep_return_shore_on_carrierInterval_or_spaced_eq_rawState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (depth spacing : Nat)
    (hmany :
      2 * (spacing + 1) * (depth + 1) ^ 2 <
        (residualCycleInterval sigma bond.site chord).support.toFinset.card) :
    (∃ shore cut,
        cut ∈ carrierIntervalPositions sigma bond.site chord ∧
          depth <
            (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
              shore).stackAt cut).length) ∨
      ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
        firstPosition ∈ carrierIntervalPositions sigma bond.site chord ∧
          secondPosition ∈ carrierIntervalPositions sigma bond.site chord ∧
          firstPosition < secondPosition ∧
          spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
          (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState firstPosition =
            (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState secondPosition := by
  apply RestrictedNoncrossingSweep.SweepData.exists_deep_family_on_or_spaced_eq_rawState
    (data := residualReturnSweepData rotation minimal hG sigma hSigma bond)
    depth spacing (carrierIntervalPositions sigma bond.site chord)
  rw [carrierIntervalPositions_card]
  simpa using hmany

/-- The long-carrier horn of the geometric separator dichotomy is therefore
not terminal: once it exceeds the exact shallow phased-state count, the same
nested physical return witnesses a carrier-local deep stack or repeated
state. -/
theorem exists_nested_carrier_local_sweep_alternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hlong : HasNestedCarrierIntervalSupportLargerThan rotation hG sigma hSigma bond
      (2 * (spacing + 1) * (depth + 1) ^ 2)) :
    ∃ outer inner : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
          orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
        outer.left < inner.left ∧ inner.right < outer.right ∧
        ((∃ shore cut,
            cut ∈ carrierIntervalPositions sigma bond.site inner ∧
              depth <
                (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
                  shore).stackAt cut).length) ∨
          ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
            firstPosition ∈ carrierIntervalPositions sigma bond.site inner ∧
              secondPosition ∈ carrierIntervalPositions sigma bond.site inner ∧
              firstPosition < secondPosition ∧
              spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
              (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
                  spacing).rawState firstPosition =
                (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
                  spacing).rawState secondPosition) := by
  rcases hlong with ⟨outer, inner, hshore, hleft, hright, hcard⟩
  refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
  exact exists_deep_return_shore_on_carrierInterval_or_spaced_eq_rawState
    rotation minimal hG sigma hSigma bond inner depth spacing hcard

/-- A nested physical return pair whose inner carrier interval contains a
residual-return stack deeper than `depth`. -/
def HasNestedCarrierDeepReturnStack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      ∃ shore cut,
        cut ∈ carrierIntervalPositions sigma bond.site inner ∧
          depth <
            (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
              shore).stackAt cut).length

/-- A nested physical return pair whose inner carrier interval contains two
materially spaced equal phased residual-return states. -/
def HasNestedCarrierSpacedSweepRepeat
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
        firstPosition ∈ carrierIntervalPositions sigma bond.site inner ∧
          secondPosition ∈ carrierIntervalPositions sigma bond.site inner ∧
          firstPosition < secondPosition ∧
          spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
          (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState firstPosition =
            (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState secondPosition

/-- A materially spaced equal phased state anywhere on the site's full
carrier sweep. -/
def HasSpacedResidualReturnSweepRepeat
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat) : Prop :=
  ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
    firstPosition < secondPosition ∧
      spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
      (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
          spacing).rawState firstPosition =
        (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
          spacing).rawState secondPosition

/-- The carrier-local alternative packaged into semantic predicates. -/
theorem hasNestedCarrierDeepReturnStack_or_spacedSweepRepeat
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hlong : HasNestedCarrierIntervalSupportLargerThan rotation hG sigma hSigma bond
      (residualReturnShallowStateCount depth spacing)) :
    HasNestedCarrierDeepReturnStack rotation minimal hG sigma hSigma bond depth ∨
      HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond
        spacing := by
  have hlong' : HasNestedCarrierIntervalSupportLargerThan rotation hG sigma hSigma bond
      (2 * (spacing + 1) * (depth + 1) ^ 2) := by
    simpa [residualReturnShallowStateCount] using hlong
  rcases exists_nested_carrier_local_sweep_alternative rotation minimal hG sigma
      hSigma bond depth spacing hlong' with
    ⟨outer, inner, hshore, hleft, hright, hdeep | hrepeated⟩
  · exact Or.inl ⟨outer, inner, hshore, hleft, hright, hdeep⟩
  · exact Or.inr ⟨outer, inner, hshore, hleft, hright, hrepeated⟩

/-- The componentwise geometric sweep alternative after the long-carrier
horn has been discharged by a carrier-local sweep. -/
def CarrierCompressedGeometricAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) : Prop :=
  HasCyclicEdgeCutOfSizeAtMost G
      (6 * residualReturnShallowStateCount depth spacing) ∨
    HasNestedAmbientReturnSupportLargerThan rotation hG sigma hSigma bond
      (residualReturnShallowStateCount depth spacing) ∨
    HasNestedCarrierDeepReturnStack rotation minimal hG sigma hSigma bond depth ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond spacing

/-- The componentwise geometric sweep alternative with the long-carrier
horn discharged by a carrier-local sweep.  The only geometrically long horn
left uncompressed is the ambient return path. -/
theorem hasCarrierCompressedGeometricAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    CarrierCompressedGeometricAlternative rotation minimal hG sigma hSigma bond
      depth spacing := by
  rcases
      hasCyclicEdgeCutOfSizeAtMost_or_longAmbientReturn_or_longCarrierInterval_or_spaced
        rotation minimal hG sigma hSigma bond
          (residualReturnShallowStateCount depth spacing) spacing hmany with
    hcut | hambient | hcarrier | hrepeated
  · exact Or.inl hcut
  · exact Or.inr (Or.inl hambient)
  · rcases hasNestedCarrierDeepReturnStack_or_spacedSweepRepeat
        rotation minimal hG sigma hSigma bond depth spacing hcarrier with
      hdeep | hlocalRepeat
    · exact Or.inr (Or.inr (Or.inl hdeep))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hlocalRepeat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hrepeated)))

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep
