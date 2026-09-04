import Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingSweepInterface
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep

/-!
# Ordered open-wire interfaces at repeated residual-return sweep states

The two repeated-state outcomes of carrier compression are packaged here as
proof-carrying receipts.  Besides their material spacing, each receipt exposes
the canonical family-by-family equivalence between the ordered open-return
slots at its two cuts.

This is the topological interface required before Count or colouring data can
be compared.  It deliberately does not claim equality of those semantic
profiles.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnSweepInterface

open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open NoncrossingSweepInterface
open ResidualReturnCarrierSweep
open ResidualReturnSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A materially spaced repeated residual-return state, retaining the two
positions and their exact phased-state equality. -/
structure SpacedResidualReturnInterfaceReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat) where
  firstPosition : CyclePosition sigma bond.site
  secondPosition : CyclePosition sigma bond.site
  ordered : firstPosition < secondPosition
  separated : spacing + 1 ≤ secondPosition.val - firstPosition.val
  phasedState_eq :
    (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
        spacing).rawState firstPosition =
      (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
        spacing).rawState secondPosition

/-- The canonical equivalence between the two ordered open-return
interfaces carried by a repeated-state receipt. -/
def SpacedResidualReturnInterfaceReceipt.openWireEquiv
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat)
    (receipt : SpacedResidualReturnInterfaceReceipt rotation minimal hG sigma
      hSigma bond spacing) :
    OpenArcInterface
        (residualReturnSweepData rotation minimal hG sigma hSigma bond)
        receipt.firstPosition ≃
      OpenArcInterface
        (residualReturnSweepData rotation minimal hG sigma hSigma bond)
        receipt.secondPosition :=
  openArcInterfaceEquivOfPhasedRawStateEq
    (residualReturnSweepData rotation minimal hG sigma hSigma bond) spacing
    receipt.phasedState_eq

/-- Package the full-carrier repeated-state horn as an interface receipt. -/
theorem nonempty_spacedResidualReturnInterfaceReceipt_of_repeat
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat)
    (hrepeat : HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma
      hSigma bond spacing) :
    Nonempty (SpacedResidualReturnInterfaceReceipt rotation minimal hG sigma
      hSigma bond spacing) := by
  rcases hrepeat with ⟨firstPosition, secondPosition, horder, hspacing, heq⟩
  exact ⟨⟨firstPosition, secondPosition, horder, hspacing, heq⟩⟩

/-- A repeated residual-return state inside one nested carrier interval,
retaining the surrounding return annulus. -/
structure CarrierSpacedResidualReturnInterfaceReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat) where
  outer : OrderedReturnChord
    (orderedSiteReturnPairing hG sigma hSigma bond.site)
  inner : OrderedReturnChord
    (orderedSiteReturnPairing hG sigma hSigma bond.site)
  shore_eq :
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
      orderedReturnShore rotation hG sigma hSigma bond inner.left
  left_nested : outer.left < inner.left
  right_nested : inner.right < outer.right
  repeated : SpacedResidualReturnInterfaceReceipt rotation minimal hG sigma
    hSigma bond spacing
  first_mem : repeated.firstPosition ∈
    carrierIntervalPositions sigma bond.site inner
  second_mem : repeated.secondPosition ∈
    carrierIntervalPositions sigma bond.site inner

/-- Package the carrier-local repeated-state horn as an interface receipt. -/
theorem nonempty_carrierSpacedResidualReturnInterfaceReceipt_of_repeat
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat)
    (hrepeat : HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma
      hSigma bond spacing) :
    Nonempty (CarrierSpacedResidualReturnInterfaceReceipt rotation minimal hG
      sigma hSigma bond spacing) := by
  rcases hrepeat with
    ⟨outer, inner, hshore, hleft, hright, firstPosition, secondPosition,
      hfirstMem, hsecondMem, horder, hspacing, heq⟩
  exact ⟨{
    outer := outer
    inner := inner
    shore_eq := hshore
    left_nested := hleft
    right_nested := hright
    repeated := ⟨firstPosition, secondPosition, horder, hspacing, heq⟩
    first_mem := hfirstMem
    second_mem := hsecondMem }⟩

end

end ResidualReturnSweepInterface

end Mettapedia.GraphTheory.FourColor.Compositional
