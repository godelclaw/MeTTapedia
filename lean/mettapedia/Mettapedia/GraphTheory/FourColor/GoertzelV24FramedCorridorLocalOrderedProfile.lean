import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord

/-!
# Ordered finite profiles of source corridor slabs

The compositional splice consumes a boundary order, not merely an arbitrary
enumeration of a finite cut.  A literal source slab already has that order:
walk once around its simple facial-dual layer loop.  This file turns that
ordered walk into the crossing indexing of the graph-derived profile while
retaining every face-fragment datum supplied by the existing profile engine.

Thus a repeated source state will carry a checked correspondence of actual
crossing edges; no later splice may treat `Fintype.equivFin` as geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebProfileSpliceBridge
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance corridorLocalOrderedProfileGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
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

/-- The source-local facial-dual loop has its four literal crossing positions. -/
theorem localLayerLoop_length_eq_four
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerLoop.length = 4 := by
  simp only [localLayerLoop, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse]
  rw [interface.localLayer_walk_length_eq_two,
    interface.nextLocalLayer_walk_length_eq_two]

/-- The four component boundary edges are exactly the four crossings in the
source-local facial-dual order. -/
theorem localLayerProfile_crossingEdges_eq_localLayerLoopCutEdges
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent) =
      interface.localLayerLoopCutEdges := by
  calc
    vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (interface.separatedLocalLayerPair.componentSide
          interface.localLayerProfileComponent) =
        interface.separatedLocalLayerPair.primalCutEdges
          embedded.cellulation.rotation :=
      interface.separatedLocalLayerPair
        |>.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          embedded.cellulation.rotation interface.localLayerProfileComponent
          interface.localLayerProfileComponent_boundary
    _ = interface.localLayerLoopCutEdges :=
      interface.separatedLocalLayerPair_primalCutEdges_eq_localLayerLoopCutEdges

/-- The ordered crossing edge at a source-local layer-loop position. -/
noncomputable def localLayerOrderedCrossing
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 4) : G.edgeSet :=
  dualWalkCrossingEdge
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    interface.localLayerLoop
    (Fin.cast interface.localLayerLoop_length_eq_four.symm step)

/-- Each ordered loop crossing is a real port of the source slab component. -/
theorem localLayerOrderedCrossing_mem
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 4) :
    interface.localLayerOrderedCrossing step ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (interface.separatedLocalLayerPair.componentSide
          interface.localLayerProfileComponent) := by
  rw [interface.localLayerProfile_crossingEdges_eq_localLayerLoopCutEdges,
    localLayerLoopCutEdges]
  exact (mem_dualWalkCrossingEdges_iff
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    interface.localLayerLoop _).2
      ⟨Fin.cast interface.localLayerLoop_length_eq_four.symm step, rfl⟩

/-- Reading the four dual-loop crossings in order is duplicate-free. -/
theorem localLayerOrderedCrossing_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective interface.localLayerOrderedCrossing := by
  intro first second heq
  apply Fin.cast_injective interface.localLayerLoop_length_eq_four.symm
  apply interface.localLayerLoop_crossingEdge_injective
  simpa [localLayerOrderedCrossing] using heq

/-- The source-local loop order covers every actual crossing port of its
deletion component.  This is the non-synthetic port-order theorem needed by
the later splice correspondence. -/
theorem exists_localLayerOrderedCrossing_eq
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (edge : G.edgeSet)
    (hedge : edge ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (interface.separatedLocalLayerPair.componentSide
          interface.localLayerProfileComponent)) :
    ∃ step : Fin 4, interface.localLayerOrderedCrossing step = edge := by
  have hloop : edge ∈ interface.localLayerLoopCutEdges := by
    rw [← interface.localLayerProfile_crossingEdges_eq_localLayerLoopCutEdges]
    exact hedge
  rw [localLayerLoopCutEdges] at hloop
  rcases (mem_dualWalkCrossingEdges_iff
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    interface.localLayerLoop edge).1 hloop with ⟨loopStep, hloopStep⟩
  let step : Fin 4 := Fin.cast interface.localLayerLoop_length_eq_four loopStep
  refine ⟨step, ?_⟩
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      interface.localLayerLoop
      (Fin.cast interface.localLayerLoop_length_eq_four.symm step) = edge
  have hcast : Fin.cast interface.localLayerLoop_length_eq_four.symm step =
      loopStep := by
    apply Fin.ext
    rfl
  rw [hcast]
  exact hloopStep

/-- The literal source loop supplies the exact crossing indexing consumed by
the graph-derived profile constructor. -/
noncomputable def localLayerCrossingIndexing
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    VertexSetCrossingIndexing embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent) := by
  let hcard : Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent)) = 4 :=
    interface.localLayerProfile_crossingCard_eq_four
  apply Equiv.ofBijective
    (fun step =>
      ⟨interface.localLayerOrderedCrossing (Fin.cast hcard step),
        interface.localLayerOrderedCrossing_mem (Fin.cast hcard step)⟩)
  constructor
  · intro first second hports
    apply Fin.cast_injective hcard
    apply interface.localLayerOrderedCrossing_injective
    exact congrArg Subtype.val hports
  · intro port
    rcases interface.exists_localLayerOrderedCrossing_eq port.1 port.2 with
      ⟨step, hstep⟩
    let sourceStep : Fin (Fintype.card (VertexSetCrossingEdge
        embedded.cellulation.rotation.toRotationSystem
        (interface.separatedLocalLayerPair.componentSide
          interface.localLayerProfileComponent))) := Fin.cast hcard.symm step
    refine ⟨sourceStep, ?_⟩
    apply Subtype.ext
    change interface.localLayerOrderedCrossing (Fin.cast hcard sourceStep) =
      port.1
    have hcast : Fin.cast hcard sourceStep = step := by
      apply Fin.ext
      rfl
    rw [hcast]
    exact hstep

/-- The full finite profile of a source slab, now with its crossing ports
ordered by the real facial-dual layer loop.  The existing regional fragment
carrier is retained unchanged. -/
noncomputable def localLayerOrderedProfileData
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  vertexSetBoundaryGraphCutDataWithIndexing
    embedded.cellulation.rotation.toRotationSystem
    (interface.separatedLocalLayerPair.componentSide
      interface.localLayerProfileComponent)
    interface.localLayerCrossingIndexing

/-- The ordered data's crossing coordinates are exactly the literal loop
crossings after the harmless cardinality transport from `Fin 4`. -/
theorem localLayerOrderedProfileData_crossingEdge
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (step : Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent)))) :
    interface.localLayerOrderedProfileData.crossingEdge step =
      interface.localLayerOrderedCrossing
        (Fin.cast interface.localLayerProfile_crossingCard_eq_four step) := by
  rfl

/-- The ordered source profile remains in the common width-four L7 carrier;
only its port coordinates changed, not its region or face fragments. -/
noncomputable def localLayerOrderedDepthProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 4 :=
  graphCutDepthProfile 4 interface.localLayerOrderedProfileData coloring hcoloring
    (by rw [interface.localLayerProfile_crossingCard_eq_four])
    (vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        interface.localLayerProfileComponent))

end SourceConsecutiveSlabInterface

/-- The width-four profile at a literal source corridor position, with port
coordinates supplied by that position's actual facial-dual layer loop. -/
noncomputable def sourceSlabOrderedDepthProfile
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 4 :=
  SourceConsecutiveSlabInterface.localLayerOrderedDepthProfile
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique offset)
    coloring hcoloring

/-- A long source corridor repeats an *ordered, realized* width-four boundary
state.  The equality is therefore suitable for constructing a seam
correspondence; it is not merely equality of arbitrary finite enumerations. -/
theorem exists_equal_sourceSlabOrderedDepthProfiles
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hlarge : closedWebCutProfileCount 4 + 1 ≤ blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (closedWebCutProfileCount 4 + 1), first ≠ second ∧
      sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge first) coloring hcoloring =
      sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (closedWebCutProfileCount 4 + 1) →
      ClosedWebDepthProfile 4 := fun offset =>
    sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset) coloring hcoloring
  rcases exists_depthProfile_repeat 4 profiles with ⟨first, second, hne, heq⟩
  exact ⟨first, second, hne, heq⟩

/-- A longer source corridor has equal realized profile boundaries with three
whole source positions between them.  The extra spacing is finite-state
bookkeeping: without such a repeat, the pair consisting of a profile and a
position modulo four would inject all positions into four copies of the
finite profile carrier. -/
theorem exists_equal_sourceSlabOrderedDepthProfiles_separated
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hlarge : 4 * closedWebCutProfileCount 4 + 1 ≤ blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (4 * closedWebCutProfileCount 4 + 1),
      first.val + 3 < second.val ∧
      sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge first) coloring hcoloring =
      sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (4 * closedWebCutProfileCount 4 + 1) →
      ClosedWebDepthProfile 4 := fun offset =>
    sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset) coloring hcoloring
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin (4 * closedWebCutProfileCount 4 + 1) →
      ClosedWebDepthProfile 4 × Fin 4 := fun offset =>
    (profiles offset, ⟨offset.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hprofile : profiles first = profiles second := by
      exact congrArg Prod.fst heq
    have hmod : first.val % 4 = second.val % 4 := by
      have hresidue := congrArg (fun pair => pair.2.val) heq
      simpa [encode] using hresidue
    apply Fin.ext
    by_cases hval : first.val = second.val
    · exact hval
    · rcases lt_or_gt_of_ne hval with hfirst | hsecond
      · have hfar : first.val + 3 < second.val := by omega
        exact False.elim (hseparated first second hfar hprofile)
      · have hfar : second.val + 3 < first.val := by omega
        exact False.elim (hseparated second first hfar hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  simp [card_closedWebDepthProfile] at hcard
  omega

/-- Two literal source layers whose indexed starts have a three-position gap
are disjoint simple facial-dual loops.  This is the geometric companion to
the separated finite-profile repeat: it retains the actual source loops,
rather than replacing their separation by an abstract profile premise. -/
theorem sourceSlabLocalLayerLoops_support_disjoint_of_add_three_lt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (first second : Fin (blockLength - 3))
    (hseparated : first.val + 3 < second.val) :
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique first).localLayerLoop.support.Disjoint
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique second).localLayerLoop.support := by
  exact (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique first).localLayerLoop_support_disjoint_of_add_three_lt
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique second) (by
        change first.val + 1 + 3 < second.val + 1
        omega)

/-- A long source corridor therefore supplies two equal finite profile states
on literal, disjoint local layer loops.  This packages precisely the
finite-state and geometric input available before the later annular formation
and region-gluing steps. -/
theorem exists_equal_sourceSlabOrderedDepthProfiles_with_disjointLocalLayerLoops
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hlarge : 4 * closedWebCutProfileCount 4 + 1 ≤ blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (4 * closedWebCutProfileCount 4 + 1),
      first.val + 3 < second.val ∧
      sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge first) coloring hcoloring =
      sourceSlabOrderedDepthProfile realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge second) coloring hcoloring ∧
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge first)).localLayerLoop.support.Disjoint
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge second)).localLayerLoop.support := by
  rcases exists_equal_sourceSlabOrderedDepthProfiles_separated realization hcubic
      hrotation htwoSided hunique hlarge coloring hcoloring with
    ⟨first, second, hseparated, hequal⟩
  refine ⟨first, second, hseparated, hequal, ?_⟩
  apply sourceSlabLocalLayerLoops_support_disjoint_of_add_three_lt
  change first.val + 3 < second.val
  exact hseparated

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
