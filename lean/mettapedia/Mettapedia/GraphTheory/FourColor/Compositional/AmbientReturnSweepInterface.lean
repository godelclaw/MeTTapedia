import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentSweep
import Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingSweepInterface

/-!
# Ordered open-wire interfaces at repeated ambient-return sweep states

The attachment sweep along one physical residual-return path has the same
representation boundary as the carrier sweep: its finite LIFO state records
only local letters and stacks, whereas a later compositional splice needs a
literal ordered boundary interface.  This file packages a materially spaced
state repeat together with the canonical equivalence of its ordered open
attachment slots.

This remains deliberately topological.  Equality of colouring support and
face-progress data is a separate semantic obligation.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnSweepInterface

open AmbientReturnAttachmentSweep
open CubicPathChordDiagram
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open NoncrossingSweepInterface
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A materially spaced repeated state of the two-turn attachment sweep on
one ambient residual-return path. -/
structure SpacedAmbientReturnInterfaceReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (spacing : Nat) where
  firstCut : Fin
    ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)
  secondCut : Fin
    ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)
  firstEligible : firstCut ∈
    eligibleAmbientReturnSweepPositions hG sigma hSigma site returnChord
  secondEligible : secondCut ∈
    eligibleAmbientReturnSweepPositions hG sigma hSigma site returnChord
  ordered : firstCut < secondCut
  separated : spacing + 1 ≤ secondCut.val - firstCut.val
  firstInternalEndpoint : IsInternalChordEndpoint
    (orderedChordAmbientPath hG sigma hSigma site returnChord) firstCut
  secondInternalEndpoint : IsInternalChordEndpoint
    (orderedChordAmbientPath hG sigma hSigma site returnChord) secondCut
  phasedState_eq :
    ((PhasedNoncrossingSweep.SweepData.withPositionPhase
        (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
          site returnChord closure) spacing).rawState firstCut =
      (PhasedNoncrossingSweep.SweepData.withPositionPhase
        (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
          site returnChord closure) spacing).rawState secondCut)

/-- The repeated state canonically identifies its ordered open attachment
slots, turn by turn. -/
def SpacedAmbientReturnInterfaceReceipt.openWireEquiv
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (spacing : Nat)
    (receipt : SpacedAmbientReturnInterfaceReceipt rotation minimal hG sigma
      hSigma site returnChord closure spacing) :
    OpenArcInterface
        (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
          site returnChord closure) receipt.firstCut ≃
      OpenArcInterface
        (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
          site returnChord closure) receipt.secondCut :=
  openArcInterfaceEquivOfPhasedRawStateEq
    (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma site
      returnChord closure) spacing receipt.phasedState_eq

/-- Package the raw ambient-repeat branch as its proof-carrying ordered
interface receipt. -/
theorem nonempty_spacedAmbientReturnInterfaceReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (spacing : Nat)
    (firstCut secondCut : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hfirstEligible : firstCut ∈
      eligibleAmbientReturnSweepPositions hG sigma hSigma site returnChord)
    (hsecondEligible : secondCut ∈
      eligibleAmbientReturnSweepPositions hG sigma hSigma site returnChord)
    (hordered : firstCut < secondCut)
    (hseparated : spacing + 1 ≤ secondCut.val - firstCut.val)
    (hfirstEndpoint : IsInternalChordEndpoint
      (orderedChordAmbientPath hG sigma hSigma site returnChord) firstCut)
    (hsecondEndpoint : IsInternalChordEndpoint
      (orderedChordAmbientPath hG sigma hSigma site returnChord) secondCut)
    (heq :
      (PhasedNoncrossingSweep.SweepData.withPositionPhase
        (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
          site returnChord closure) spacing).rawState firstCut =
      (PhasedNoncrossingSweep.SweepData.withPositionPhase
        (ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
          site returnChord closure) spacing).rawState secondCut) :
    Nonempty (SpacedAmbientReturnInterfaceReceipt rotation minimal hG sigma
      hSigma site returnChord closure spacing) :=
  ⟨⟨firstCut, secondCut, hfirstEligible, hsecondEligible, hordered,
    hseparated, hfirstEndpoint, hsecondEndpoint, heq⟩⟩

end

end AmbientReturnSweepInterface

end Mettapedia.GraphTheory.FourColor.Compositional
