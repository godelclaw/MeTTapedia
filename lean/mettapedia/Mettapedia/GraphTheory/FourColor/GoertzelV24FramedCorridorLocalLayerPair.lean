import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLoop
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSlabCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversalAppend
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCycle

/-!
# Local paired layers from a source corridor cell

Two consecutive source slabs give two different simple dual paths with the
same endpoint faces.  This module constructs that pair from the actual
corridor rotations and proves its crossings are disjoint.  It is the local
cell of the open-interface ladder; later formation extends these paths to the
annular boundary faces rather than treating a chord wall as a transversal.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrientedHexSlab
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the edge carrier's equality instance aligned with the source-corridor
   modules, whose finite facial boundaries use the ordinary subtype instance. -/
local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

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

/-- The layer through the next corridor hexagon, with the same two actual
external face endpoints as the first layer. -/
noncomputable def nextLocalLayerWalk
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      interface.firstLayerFace interface.secondLayerFace :=
  SimpleGraph.Walk.cons interface.firstLayerFace_adjacent_nextCenterLayerFace
    (SimpleGraph.Walk.cons interface.nextCenterLayerFace_adjacent_secondLayerFace
      SimpleGraph.Walk.nil)

/-- The next source-slab layer is simple for the same concrete reason as the
first: the two endpoint faces and the central hexagon are all distinct. -/
theorem nextLocalLayerWalk_isPath
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.nextLocalLayerWalk.IsPath := by
  unfold nextLocalLayerWalk
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa using interface.secondLayerFace_ne_nextCenterLayerFace.symm
  · simp [interface.firstLayerFace_ne_nextCenterLayerFace,
      interface.firstLayerFace_ne_secondLayerFace]

/-- The second literal layer in the source corridor cell. -/
noncomputable def nextLocalLayer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    SimpleDualCrosscut
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      interface.firstLayerFace interface.secondLayerFace where
  walk := interface.nextLocalLayerWalk
  isPath := interface.nextLocalLayerWalk_isPath

/-- Both source-derived local layers have the same two crossing positions. -/
theorem nextLocalLayer_walk_length_eq_two
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.nextLocalLayer.walk.length = 2 := by
  simp [nextLocalLayer, nextLocalLayerWalk]

/-- The two source layers meet only at their named endpoints.  After removing
those endpoints from the two path supports, the remaining facial cells are
disjoint by the four distinct faces of the concrete slab cycle. -/
theorem localLayers_tail_disjoint
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayer.walk.support.tail.Disjoint
      interface.nextLocalLayer.walk.reverse.support.tail := by
  simp [localLayer, localLayerWalk, nextLocalLayer, nextLocalLayerWalk,
    interface.firstLayerFace_ne_centerLayerFace,
    interface.firstLayerFace_ne_secondLayerFace,
    interface.centerLayerFace_ne_nextCenterLayerFace.symm,
    interface.secondLayerFace_ne_nextCenterLayerFace.symm]

/-- Following the first local layer and returning on the next local layer is
the explicit four-step facial-dual loop around one real source slab cell. -/
noncomputable def localLayerLoop
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      interface.firstLayerFace interface.firstLayerFace :=
  interface.localLayer.walk.append interface.nextLocalLayer.walk.reverse

/-- The source cell loop is simple.  This is a direct finite check on the
two actual layer paths, not a Jordan-separation assumption. -/
theorem localLayerLoop_isCycle
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerLoop.IsCycle := by
  exact SimpleGraph.Walk.IsPath.isCycle_append interface.localLayer.isPath
    interface.nextLocalLayer.isPath.reverse interface.localLayers_tail_disjoint
      (Or.inl (by simp [interface.localLayer_walk_length_eq_two]))

/-- Every face of a literal source cell loop is either one of its two corridor
centres or a side neighbour of one.  This gives the loop a concrete bounded
neighbourhood in the realized corridor, which later separates distant layer
boundaries without treating an arbitrary chord as a transversal. -/
theorem localLayerLoop_support_near_centers
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (face : AmbientFace (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hface : face ∈ interface.localLayerLoop.support) :
    face = interface.centerLayerFace ∨ face = interface.nextCenterLayerFace ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          interface.centerLayerFace face ∨
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          interface.nextCenterLayerFace face := by
  rw [localLayerLoop, SimpleGraph.Walk.mem_support_append_iff] at hface
  rcases hface with hlocal | hnextLayer
  · change face ∈ interface.localLayerWalk.support at hlocal
    simp only [localLayerWalk, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons] at hlocal
    rcases hlocal with hfirst | hcenter | hsecond
    · subst face
      exact Or.inr (Or.inr (Or.inl
        interface.firstLayerFace_adjacent_centerLayerFace.symm))
    · subst face
      exact Or.inl rfl
    · rcases hsecond with hsecond | hnone
      · subst face
        exact Or.inr (Or.inr (Or.inl
          interface.centerLayerFace_adjacent_secondLayerFace))
      · simp at hnone
  · change face ∈ interface.nextLocalLayerWalk.reverse.support at hnextLayer
    rw [SimpleGraph.Walk.support_reverse] at hnextLayer
    simp only [nextLocalLayerWalk, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_reverse, List.mem_cons] at hnextLayer
    rcases hnextLayer with hfirst | hnextCenter | hsecond
    · subst face
      exact Or.inr (Or.inr (Or.inr
        interface.firstLayerFace_adjacent_nextCenterLayerFace.symm))
    · subst face
      exact Or.inr (Or.inl rfl)
    · rcases hsecond with hsecond | hnone
      · subst face
        exact Or.inr (Or.inr (Or.inr
          interface.nextCenterLayerFace_adjacent_secondLayerFace))
      · simp at hnone

/-- Every primal edge crossing the local cell loop occurs at one unique dual
position.  This is the finite face-incidence fact that prevents the two
layer boundaries from secretly reusing a source edge. -/
theorem localLayerLoop_crossingEdge_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective
      (dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))
        hunique interface.localLayerLoop) := by
  exact dualWalkCrossingEdge_injective_of_isCycle
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))
    (orbitFace_incidence_le_two embedded.cellulation.rotation.toRotationSystem)
    hunique interface.localLayerLoop interface.localLayerLoop_isCycle

/-- The two distinct local source layers cross disjoint primal-edge supports.
The proof reads both crossings into their common simple dual loop and uses
the loop's checked positional injectivity. -/
theorem localLayers_crossing_disjoint
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Disjoint (interface.localLayer.crossingEdges hunique)
      (interface.nextLocalLayer.crossingEdges hunique) := by
  refine Finset.disjoint_left.2 ?_
  intro edge hleft hright
  rcases (interface.localLayer.mem_crossingEdges_iff hunique edge).1 hleft with
    ⟨leftStep, hleftStep⟩
  rcases (interface.nextLocalLayer.mem_crossingEdges_iff hunique edge).1
      hright with ⟨rightStep, hrightStep⟩
  let leftLoopStep : Fin interface.localLayerLoop.length :=
    ⟨leftStep.val, by
      simp [localLayerLoop]
      omega⟩
  let rightReverseStep : Fin interface.nextLocalLayer.walk.reverse.length :=
    ⟨interface.nextLocalLayer.walk.length - (rightStep.val + 1), by
      rw [SimpleGraph.Walk.length_reverse]
      omega⟩
  have hrightReverseLt : rightReverseStep.val <
      interface.nextLocalLayer.walk.reverse.length := rightReverseStep.isLt
  let rightLoopStep : Fin interface.localLayerLoop.length :=
    ⟨interface.localLayer.walk.length + rightReverseStep.val, by
      simpa [localLayerLoop] using
        Nat.add_lt_add_left hrightReverseLt interface.localLayer.walk.length⟩
  have hleftLoop :
      dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.localLayerLoop leftLoopStep = edge := by
    calc
      dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.localLayerLoop leftLoopStep =
        dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.localLayer.walk leftStep := by
            simpa [localLayerLoop, leftLoopStep] using
              (dualWalkCrossingEdge_append_left
                (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
                (Finset.univ : Finset
                  (OrbitFace embedded.cellulation.rotation.toRotationSystem))
                hunique interface.localLayer.walk
                interface.nextLocalLayer.walk.reverse leftStep)
      _ = edge := hleftStep
  have hrightLoop :
      dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.localLayerLoop rightLoopStep = edge := by
    calc
      dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.localLayerLoop rightLoopStep =
        dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.nextLocalLayer.walk.reverse rightReverseStep := by
            simpa [localLayerLoop, rightLoopStep] using
              (dualWalkCrossingEdge_append_right
                (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
                (Finset.univ : Finset
                  (OrbitFace embedded.cellulation.rotation.toRotationSystem))
                hunique interface.localLayer.walk
                interface.nextLocalLayer.walk.reverse rightReverseStep)
      _ = dualWalkCrossingEdge
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.nextLocalLayer.walk rightStep := by
            simpa [rightReverseStep] using
              (dualWalkCrossingEdge_reverse
                (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
                (Finset.univ : Finset
                  (OrbitFace embedded.cellulation.rotation.toRotationSystem))
                hunique interface.nextLocalLayer.walk rightStep)
      _ = edge := hrightStep
  have hpositions := interface.localLayerLoop_crossingEdge_injective
    (hleftLoop.trans hrightLoop.symm)
  have hvalues := congrArg Fin.val hpositions
  have hleftLt : leftLoopStep.val < interface.localLayer.walk.length := by
    exact leftStep.isLt
  have hrightGe : interface.localLayer.walk.length ≤ rightLoopStep.val := by
    simp [rightLoopStep]
  omega

/-- The concrete pair of equal-width, primal-edge-disjoint local layers
generated by one source corridor cell.  This has exactly the same finite
interface shape consumed by the open splice construction. -/
noncomputable def localLayerPair
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    AlignedSimpleDualCrosscuts
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      interface.firstLayerFace interface.secondLayerFace hunique where
  left := interface.localLayer
  right := interface.nextLocalLayer
  length_eq := by
    rw [interface.localLayer_walk_length_eq_two,
      interface.nextLocalLayer_walk_length_eq_two]
  crossing_disjoint := interface.localLayers_crossing_disjoint

/-- The source cell's paired layers are also disjoint as face paths except at
their endpoints, so their closed composite is a genuine local facial-dual
cycle.  This is the reusable local ladder tile for the later annular
formation induction. -/
noncomputable def separatedLocalLayerPair
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      interface.firstLayerFace interface.secondLayerFace hunique where
  left := interface.localLayer
  right := interface.nextLocalLayer
  length_eq := by
    rw [interface.localLayer_walk_length_eq_two,
      interface.nextLocalLayer_walk_length_eq_two]
  crossing_disjoint := interface.localLayers_crossing_disjoint
  transverse_disjoint := interface.localLayers_tail_disjoint
  nondegenerate := Or.inl (by
    rw [interface.localLayer_walk_length_eq_two]
    omega)

/-- The generic loop formed from the concrete local layer pair is the same
cycle already constructed directly from the source slab. -/
theorem separatedLocalLayerPair_dualLoop_isCycle
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.separatedLocalLayerPair.dualLoop.IsCycle := by
  exact interface.separatedLocalLayerPair.dualLoop_isCycle

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
