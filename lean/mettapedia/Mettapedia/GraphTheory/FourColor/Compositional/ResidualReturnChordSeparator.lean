import Mettapedia.GraphTheory.Embedding.PathChord
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnPathAttachment

/-!
# Exact separators from chords of ambient residual returns

When the canonical third edge at an internal position of an ambient residual
return comes back to the same path, it and the intervening path interval form
a simple cycle.  In the route's connected cellular sphere map, that cycle
carries an exact binary face cut.

This is a pointwise separator.  No pairwise noncrossing or bounded-interface
conclusion is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnChordSeparator

open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.CubicPathAttachment
open Mettapedia.GraphTheory.Embedding
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24WalkCycleParity
open MatchingParity
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A returning third edge on an ambient residual path carries an exact face
cut supported by that chord and the path interval between its endpoints. -/
theorem exists_exactFaceCut_of_ambientReturnChord
    (rotation : Data G)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary rotation.toRotationSystem)
      (Finset.univ : Finset (OrbitFace rotation.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord)
    (attachment : ChordAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position) :
    let boundary := ambientReturnChordBoundary
      hG sigma hSigma site chord position attachment
    ∃ cut : ExactFaceCut rotation.toRotationSystem
        (fun edge : G.edgeSet ↦ edge ∈ boundary.wall) F2,
      orbitFaceBoundaryLinearMap rotation.toRotationSystem cut.label =
        walkEdgeParity boundary.cycleWalk := by
  dsimp only
  exact exists_exactFaceCut_of_samePathChordBoundary rotation htwoSided hdual
    hconnected hsphere
    (ambientReturnChordBoundary hG sigma hSigma site chord position attachment)

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnChordSeparator
