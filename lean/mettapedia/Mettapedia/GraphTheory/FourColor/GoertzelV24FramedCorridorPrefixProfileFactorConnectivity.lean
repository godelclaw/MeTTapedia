import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixTerminalConnectivity

/-!
# Factoring the old-prefix component relation through its finite profile

The finite eight-edge contraction still mentioned reachability through the
entire old cumulative prefix.  Its only selected old-prefix edges are the two
incoming crossings and the shared rung, so the terminal-aware incoming
profile records every nontrivial old-factor component move.

Reflexive equality remains a separate case.  Graph reachability is reflexive
on every edge, whereas the profile matrix deliberately guards its diagonal by
regional membership and tracked color.  Keeping that distinction explicit
gives an exact relational factorization without imposing determinism.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphThreeFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFactorConnectivityEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The old-prefix component relation read only from a bounded incoming
profile.  Equality accounts for the unguarded reflexivity of graph
reachability; every nontrivial move is witnessed by actual port coordinates
and a true `strandConnected` bit. -/
def localLayerOldPrefixProfileComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) : Prop :=
  left = right ∨
    ∃ leftPort rightPort : CorridorPort 2 1,
      aligned.localLayerLeftPrefixSharedRungGraphCutData.portEdge leftPort =
          left.1 ∧
        aligned.localLayerLeftPrefixSharedRungGraphCutData.portEdge rightPort =
          right.1 ∧
        incoming.profile.strandConnected pair leftPort rightPort = true

/-- On the selected finite interface, literal old-prefix reachability is
exactly the relation computed from the terminal-aware incoming profile. -/
theorem localLayerLeftPrefixTrackedGraph_reachable_iff_profileComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerLeftPrefixRegion color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable left right ↔
      aligned.localLayerOldPrefixProfileComponentStep
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor)
        pair left right := by
  let oldGraph := regionalTrackedEdgeGraph
    embedded.cellulation.rotation.toRotationSystem
    aligned.toInterface.localLayerLeftPrefixRegion color
    (trackedColorPairColors pair).1
    (trackedColorPairColors pair).2
  constructor
  · intro hreach
    by_cases heq : left = right
    · exact Or.inl heq
    · have hne : left.1 ≠ right.1 := by
        intro hval
        exact heq (Subtype.ext hval)
      have hleftSupport : left.1 ∈ oldGraph.support :=
        SimpleGraph.mem_support_of_reachable hne hreach
      have hrightSupport : right.1 ∈ oldGraph.support :=
        SimpleGraph.mem_support_of_reachable hne.symm hreach.symm
      rcases (SimpleGraph.mem_support oldGraph).1 hleftSupport with
        ⟨leftNeighbor, hleftAdj⟩
      rcases (SimpleGraph.mem_support oldGraph).1 hrightSupport with
        ⟨rightNeighbor, hrightAdj⟩
      have hleftRegion : left.1 ∈
          aligned.toInterface.localLayerLeftPrefixRegion := hleftAdj.2.1
      have hrightRegion : right.1 ∈
          aligned.toInterface.localLayerLeftPrefixRegion := hrightAdj.2.1
      rcases
          (aligned.mem_finiteConnectivityInterface_inter_leftPrefix_iff_exists_port
            left.1).1 (Finset.mem_inter.2 ⟨left.2, hleftRegion⟩) with
        ⟨leftPort, hleftPort⟩
      rcases
          (aligned.mem_finiteConnectivityInterface_inter_leftPrefix_iff_exists_port
            right.1).1 (Finset.mem_inter.2 ⟨right.2, hrightRegion⟩) with
        ⟨rightPort, hrightPort⟩
      refine Or.inr ⟨leftPort, rightPort, hleftPort, hrightPort, ?_⟩
      apply
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile_strandConnected_eq_true_iff
          color hcolor pair leftPort rightPort).2
      rw [hleftPort, hrightPort]
      exact ⟨hleftAdj.1.2.1, hrightAdj.1.2.1, hreach⟩
  · intro hstep
    rcases hstep with heq | ⟨leftPort, rightPort, hleftPort, hrightPort, hbit⟩
    · rw [heq]
    · have hsemantic :=
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile_strandConnected_eq_true_iff
          color hcolor pair leftPort rightPort).1 hbit
      have hreach := hsemantic.2.2
      rw [hleftPort, hrightPort] at hreach
      exact hreach

/-- One finite-interface move after replacing only the old cumulative factor
by its incoming profile.  The Cell and residual seam remain literal local
relations for the next transport theorem. -/
def localLayerIncomingProfileFactoredComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (incoming : BoundedCorridorCutProfile 2 1 4)
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Subtype fun edge =>
      edge ∈ aligned.localLayerFiniteConnectivityInterface) : Prop :=
  aligned.localLayerOldPrefixProfileComponentStep incoming pair left right ∨
    (regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      aligned.toInterface.localLayerCellBoundaryRegion color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).Reachable left right ∨
    (aligned.toInterface.localLayerTrackedSeamGraph color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).Reachable left right

/-- The actual outgoing connectivity after one source Cell is the finite
closure of a relation whose old-prefix component has been completely
factored through the incoming terminal-aware profile. -/
theorem localLayerRightPrefixTrackedGraph_reachable_iff_incomingProfileFactoredClosure
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color (aligned.toInterface.localLayerPrefixCrossing crossing) ≠ 0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerRightPrefixRegion color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
      (aligned.toInterface.nextLocalLayerPrefixCrossing left)
      (aligned.toInterface.nextLocalLayerPrefixCrossing right) ↔
    Relation.ReflTransGen
      (aligned.localLayerIncomingProfileFactoredComponentStep
        (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor)
        color pair)
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing left,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          left⟩
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing right,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          right⟩ := by
  rw [aligned.localLayerRightPrefixTrackedGraph_reachable_iff_finiteInterfaceClosure
    hcubic hrotation color (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2 left right]
  constructor
  · intro hclosure
    exact hclosure.mono (by
      intro first second hstep
      rcases hstep with hfirst | hcell | hseam
      · exact Or.inl
          ((aligned.localLayerLeftPrefixTrackedGraph_reachable_iff_profileComponentStep
            color hcolor pair first second).1 hfirst)
      · exact Or.inr (Or.inl hcell)
      · exact Or.inr (Or.inr hseam))
  · intro hclosure
    exact hclosure.mono (by
      intro first second hstep
      rcases hstep with hfirst | hcell | hseam
      · exact Or.inl
          ((aligned.localLayerLeftPrefixTrackedGraph_reachable_iff_profileComponentStep
            color hcolor pair first second).2 hfirst)
      · exact Or.inr (Or.inl hcell)
      · exact Or.inr (Or.inr hseam))

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
