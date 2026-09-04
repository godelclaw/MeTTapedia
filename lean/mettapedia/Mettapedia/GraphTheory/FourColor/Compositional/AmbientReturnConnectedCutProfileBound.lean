import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnCentralCutFamily
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixConnectedCutProfileBound

/-!
# Full-profile bound for shallow ambient-return cuts

This file is the ambient-return adapter for the path-generic complete-profile
theorem.  The physical sweep supplies a common boundary bound and two path
margins; the generic theorem supplies the coherent rooted cuts and the exact
finite Count-profile bound.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnConnectedCutProfileBound

open AmbientReturnCentralCutFamily
open AmbientReturnSweepBoundedRepeat
open CubicPathChordDiagram
open CyclicEdgeCutRealization
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixConnectedCutProfileBound
open PathPrefixCyclicCut
open PathPrefixRootedNesting
open ResidualReturnPathAttachment
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Compatibility name for the path-generic complete-profile cardinality. -/
def connectedCutProfileStateCount (bound : Nat) : Nat :=
  pathPrefixProfileStateCount bound

/-- Compatibility wrapper for common-root saturation of one path prefix. -/
theorem exists_connectedCut_at_commonRoot
    (hconnected : G.Connected)
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val)
    (bound : Nat)
    (hboundary : (crossingEdgeFinset G (pathPrefixSide path cut)).card ≤ bound)
    (hprefixLarge : bound < cut.val + 2)
    (hsuffixLarge : bound < path.length + 1 - cut.val + 2)
    (anchor : Fin (path.length + 1)) (hcutAnchor : cut ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : prefixExteriorComponent hpath anchor outsideRoot)
    (outsideCycle : G.Walk outsideRoot outsideRoot)
    (hcycle : outsideCycle.IsCycle)
    (hsupportAnchor : ∀ vertex, vertex ∈ outsideCycle.support →
      prefixExteriorComponent hpath anchor vertex) :
    ∃ connected : ConnectedAtWidth G bound,
      ∀ vertex, connected.realization.side vertex ↔
        closureSide (G := G) (pathPrefixSide path cut) outsideRoot
          (prefixExteriorComponent_mono hpath hcutAnchor outsideRoot
            hrootAnchor).choose vertex :=
  PathPrefixConnectedCutProfileBound.exists_connectedCut_at_commonRoot
    hconnected hpath hregular cut hcut bound hboundary hprefixLarge
    hsuffixLarge anchor hcutAnchor outsideRoot hrootAnchor outsideCycle hcycle
    hsupportAnchor

/-- A shallow central family in a least counterexample has at most the exact
number of complete phased connected-shore profiles. -/
theorem ShallowCentralCutFamilyReceipt.card_le_profileStateCount
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
    (depth target : Nat)
    (receipt : ShallowCentralCutFamilyReceipt rotation minimal hG sigma hSigma
      site returnChord closure depth target) :
    (centralSweepPositions hG sigma hSigma site returnChord depth).card ≤
      connectedCutProfileStateCount (physicalSweepBound depth) := by
  have hbound := card_prefixFamily_le_profileStateCount rotation minimal
    (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG)
    (physicalSweepBound depth)
    (centralSweepPositions hG sigma hSigma site returnChord depth)
    (fun cut hcut =>
      positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma hSigma site
        returnChord cut
          (ShallowCentralCutFamilyReceipt.mem_eligible rotation minimal hG sigma
            hSigma site returnChord closure depth target receipt hcut))
    (fun cut hcut =>
      ShallowCentralCutFamilyReceipt.boundaryWidth rotation minimal hG sigma
        hSigma site returnChord closure depth target receipt hcut)
    (fun cut hcut =>
      ShallowCentralCutFamilyReceipt.margins rotation minimal hG sigma hSigma
        site returnChord closure depth target receipt hcut)
  simpa only [connectedCutProfileStateCount] using hbound

end

end AmbientReturnConnectedCutProfileBound

end Mettapedia.GraphTheory.FourColor.Compositional
