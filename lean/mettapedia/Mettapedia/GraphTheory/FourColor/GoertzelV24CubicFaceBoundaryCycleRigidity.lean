import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24CycleEdgeSupportRigidity
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceWalk
open GoertzelV24PrimalCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cubicFaceBoundaryCycleRigidityGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In a cubic two-sided rotation map, a simple cycle supported by one
facial boundary occupies that entire boundary. -/
theorem isCycle_mem_edges_iff_mem_orbitFaceBoundary_of_subset
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (face : OrbitFace graphData.toRotationSystem)
    {root : V} (cycle : G.Walk root root) (hcycle : cycle.IsCycle)
    (hsubset : ∀ edge : G.edgeSet, edge.1 ∈ cycle.edges →
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (anchor : G.edgeSet) (hanchor : anchor.1 ∈ cycle.edges) :
    ∀ edge : G.edgeSet,
      edge.1 ∈ cycle.edges ↔
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
  have hanchorFace := hsubset anchor hanchor
  rcases (mem_orbitFaceBoundary_iff graphData.toRotationSystem
      face anchor).1 hanchorFace with
    ⟨dart, hdartFace, hdartEdge⟩
  have hdartOrbit :
      dartOrbitFace graphData.toRotationSystem dart = face :=
    (mem_orbitFaceDarts_iff graphData.toRotationSystem face dart).1
      hdartFace
  rcases exists_rootedFaceTrail graphData htwoSided dart with
    ⟨faceTrail, hfaceTrail, _hfaceTrailDarts, hfaceTrailEdgesRaw⟩
  have hfaceTrailEdges : ∀ edge : G.edgeSet,
      edge.1 ∈ faceTrail.edges ↔
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
    intro edge
    simpa only [hdartOrbit] using hfaceTrailEdgesRaw edge
  let indicator := orbitFaceBoundaryIndicator graphData face
  let boundaryGraph : SimpleGraph V := scalarSupportGraph indicator
  letI : boundaryGraph.LocallyFinite := fun _ => Fintype.ofFinite _
  have hindicatorCycle : indicator ∈ f2CycleSpace G := by
    exact orbitFaceBoundaryIndicator_mem_f2CycleSpace graphData
      htwoSided face
  have hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G indicator vertex = 0 := by
    intro vertex
    exact scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
      hindicatorCycle vertex
  have hcubicEdges : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData hcubic
  have hboundaryCycles : boundaryGraph.IsCycles := by
    exact scalarSupportGraph_isCycles indicator hflow hcubicEdges
  have hcycleBoundary : ∀ edge, edge ∈ cycle.edges →
      edge ∈ boundaryGraph.edgeSet := by
    intro edge hedge
    let ambient : G.edgeSet := ⟨edge, cycle.edges_subset_edgeSet hedge⟩
    have hambientFace : ambient ∈
        orbitFaceBoundary graphData.toRotationSystem face :=
      hsubset ambient hedge
    have hindicator : indicator ambient ≠ 0 := by
      simp [indicator, orbitFaceBoundaryIndicator, hambientFace]
    exact (ambientEdge_mem_scalarSupportGraph_edgeSet_iff
      indicator ambient).2 hindicator
  let boundaryCycle := cycle.transfer boundaryGraph hcycleBoundary
  have hboundaryCycleIsCycle : boundaryCycle.IsCycle :=
    hcycle.transfer hcycleBoundary
  have hfaceTrailBoundary : ∀ edge, edge ∈ faceTrail.edges →
      edge ∈ boundaryGraph.edgeSet := by
    intro edge hedge
    let ambient : G.edgeSet :=
      ⟨edge, faceTrail.edges_subset_edgeSet hedge⟩
    have hambientFace : ambient ∈
        orbitFaceBoundary graphData.toRotationSystem face :=
      (hfaceTrailEdges ambient).1 hedge
    have hindicator : indicator ambient ≠ 0 := by
      simp [indicator, orbitFaceBoundaryIndicator, hambientFace]
    exact (ambientEdge_mem_scalarSupportGraph_edgeSet_iff
      indicator ambient).2 hindicator
  let boundaryFaceTrail :=
    faceTrail.transfer boundaryGraph hfaceTrailBoundary
  have hdartEdgeValue : dart.edge = anchor.1 :=
    congrArg Subtype.val hdartEdge
  have hanchorBoundaryCycle : dart.edge ∈ boundaryCycle.edges := by
    rw [SimpleGraph.Walk.edges_transfer]
    rw [hdartEdgeValue]
    exact hanchor
  have hstart : dart.fst ∈ boundaryCycle.toSubgraph.verts :=
    boundaryCycle.mem_verts_toSubgraph.mpr
      (boundaryCycle.fst_mem_support_of_mem_edges hanchorBoundaryCycle)
  have hclosed : ∀ {left right : V},
      left ∈ boundaryCycle.toSubgraph.verts →
        boundaryGraph.Adj left right →
          right ∈ boundaryCycle.toSubgraph.verts := by
    intro left right hleft hadj
    have hcycleAdj : boundaryCycle.toSubgraph.Adj left right :=
      (hboundaryCycleIsCycle.adj_toSubgraph_iff_of_isCycles
        hboundaryCycles hleft right).2 hadj
    exact boundaryCycle.toSubgraph.edge_vert hcycleAdj.symm
  have hfaceSupport : ∀ vertex ∈ boundaryFaceTrail.support,
      vertex ∈ boundaryCycle.toSubgraph.verts :=
    walk_support_subset_of_start_mem_of_adj_closed boundaryFaceTrail
      hstart hclosed
  intro edge
  constructor
  · exact hsubset edge
  · intro hedgeFace
    have hedgeTrail : edge.1 ∈ faceTrail.edges :=
      (hfaceTrailEdges edge).2 hedgeFace
    have hedgeBoundaryTrail : edge.1 ∈ boundaryFaceTrail.edges := by
      simpa [boundaryFaceTrail] using hedgeTrail
    rcases Sym2.mk_surjective edge.1 with
      ⟨⟨left, right⟩, hedgeValue⟩
    have hedgeBoundaryTrailRaw :
        Function.uncurry Sym2.mk (left, right) ∈
          boundaryFaceTrail.edges :=
      hedgeValue.symm ▸ hedgeBoundaryTrail
    have hedgeBoundaryTrail' : s(left, right) ∈
        boundaryFaceTrail.edges := by
      exact hedgeBoundaryTrailRaw
    have hboundaryAdj : boundaryGraph.Adj left right :=
      (boundaryFaceTrail.adj_toSubgraph_iff_mem_edges.2
        hedgeBoundaryTrail').adj_sub
    have hleftSupport : left ∈ boundaryFaceTrail.support :=
      boundaryFaceTrail.fst_mem_support_of_mem_edges
        hedgeBoundaryTrail'
    have hleftCycle : left ∈ boundaryCycle.toSubgraph.verts :=
      hfaceSupport left hleftSupport
    have hcycleAdj : boundaryCycle.toSubgraph.Adj left right :=
      (hboundaryCycleIsCycle.adj_toSubgraph_iff_of_isCycles
        hboundaryCycles hleftCycle right).2 hboundaryAdj
    have hmem :=
      boundaryCycle.adj_toSubgraph_iff_mem_edges.1 hcycleAdj
    have hmemAmbient : s(left, right) ∈ cycle.edges := by
      simpa [boundaryCycle] using hmem
    have hmemAmbientRaw : Function.uncurry Sym2.mk (left, right) ∈
        cycle.edges := hmemAmbient
    exact hedgeValue ▸ hmemAmbientRaw

/-- In a cubic two-sided rotation map, the canonical rooted facial trail is
already a simple cycle: a cycle bypass would have the same exact edge support
and hence could not be shorter. -/
theorem exists_rootedFaceCycle
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) :
    ∃ cycle : G.Walk root.fst root.fst,
      cycle.IsCycle ∧
        cycle.darts = faceOrbitDarts graphData root ∧
        (∀ edge : G.edgeSet,
          edge.1 ∈ cycle.edges ↔
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
              (dartOrbitFace graphData.toRotationSystem root)) := by
  rcases exists_rootedFaceTrail graphData htwoSided root with
    ⟨trail, htrail, hdarts, hedgeExact⟩
  have htrailNotNil : trail ≠ .nil := by
    intro hnil
    subst trail
    exact faceOrbitDarts_ne_nil graphData root hdarts.symm
  have hbypassCycle : trail.cycleBypass.IsCycle :=
    htrail.isCycle_cycleBypass htrailNotNil
  have hbypassNotNil : ¬trail.cycleBypass.Nil :=
    hbypassCycle.not_nil
  have hbypassEdgesNe : trail.cycleBypass.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr hbypassNotNil
  let anchorValue : Sym2 V :=
    trail.cycleBypass.edges.head hbypassEdgesNe
  have hanchorValue : anchorValue ∈ trail.cycleBypass.edges := by
    exact List.head_mem hbypassEdgesNe
  let anchor : G.edgeSet :=
    ⟨anchorValue,
      trail.cycleBypass.edges_subset_edgeSet hanchorValue⟩
  have hbypassFace : ∀ edge : G.edgeSet,
      edge.1 ∈ trail.cycleBypass.edges →
        edge ∈ orbitFaceBoundary graphData.toRotationSystem
          (dartOrbitFace graphData.toRotationSystem root) := by
    intro edge hedge
    apply (hedgeExact edge).1
    exact trail.edges_cycleBypass_subset_edges hedge
  have hanchor : anchor.1 ∈ trail.cycleBypass.edges :=
    hanchorValue
  have hbypassExact :=
    isCycle_mem_edges_iff_mem_orbitFaceBoundary_of_subset graphData
      hcubic htwoSided (dartOrbitFace graphData.toRotationSystem root)
      trail.cycleBypass hbypassCycle hbypassFace anchor hanchor
  have htrailSubsetBypass : trail.edges ⊆ trail.cycleBypass.edges := by
    intro edge hedge
    let ambient : G.edgeSet :=
      ⟨edge, trail.edges_subset_edgeSet hedge⟩
    exact (hbypassExact ambient).2 ((hedgeExact ambient).1 hedge)
  have hedgeFinsets : trail.edges.toFinset =
      trail.cycleBypass.edges.toFinset := by
    ext edge
    simp only [List.mem_toFinset]
    constructor
    · intro hedge
      exact htrailSubsetBypass hedge
    · intro hedge
      exact trail.edges_cycleBypass_subset_edges hedge
  have hedgesLength : trail.edges.length =
      trail.cycleBypass.edges.length := by
    calc
      trail.edges.length = trail.edges.toFinset.card := by
        exact (List.toFinset_card_of_nodup htrail.edges_nodup).symm
      _ = trail.cycleBypass.edges.toFinset.card :=
        congrArg Finset.card hedgeFinsets
      _ = trail.cycleBypass.edges.length :=
        List.toFinset_card_of_nodup hbypassCycle.isTrail.edges_nodup
  have hlength : trail.length ≤ trail.cycleBypass.length := by
    simpa using Nat.le_of_eq hedgesLength
  have hself : trail.cycleBypass = trail :=
    SimpleGraph.Walk.ext_support <|
      trail.support_cycleBypass_sublist_support.eq_of_length_le (by
        simpa using hlength)
  exact ⟨trail, hself ▸ hbypassCycle, hdarts, hedgeExact⟩

/-- In the cubic setting, splitting a rooted facial bypass at a second edge
produces two pieces whose concatenation through that edge is a simple path. -/
theorem exists_rootedFacePath_splitAtEdge
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) (selected : G.edgeSet)
    (hselected : selected ∈
      orbitFaceBoundary graphData.toRotationSystem
        (dartOrbitFace graphData.toRotationSystem root))
    (hselectedRoot : selected.1 ≠ root.edge) :
    ∃ (left right : V) (adj : G.Adj left right)
        (before : G.Walk root.snd left)
        (after : G.Walk right root.fst),
      selected.1 = s(left, right) ∧
        (before.append (SimpleGraph.Walk.cons adj after)).IsPath ∧
        (before.append (SimpleGraph.Walk.cons adj after)).darts =
          (faceOrbitDarts graphData root).tail ∧
        (∀ edge : G.edgeSet,
          edge.1 ∈
              (before.append (SimpleGraph.Walk.cons adj after)).edges ↔
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
                (dartOrbitFace graphData.toRotationSystem root) ∧
              edge.1 ≠ root.edge) := by
  rcases exists_rootedFaceBypass_splitAtEdge graphData htwoSided root
      selected hselected hselectedRoot with
    ⟨left, right, adj, before, after, hedgeValue, _htrail,
      hdarts, hedgeExact⟩
  rcases exists_rootedFaceCycle graphData hcubic htwoSided root with
    ⟨cycle, hcycle, hcycleDarts, _hcycleEdges⟩
  have hcycleDartsNe : cycle.darts ≠ [] := by
    rw [hcycleDarts]
    exact faceOrbitDarts_ne_nil graphData root
  have hcycleNotNil : ¬cycle.Nil :=
    SimpleGraph.Walk.darts_eq_nil.not.mp hcycleDartsNe
  have hcycleHead : cycle.darts.head
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hcycleNotNil) = root := by
    simpa only [hcycleDarts] using faceOrbitDarts_head graphData root
  have hcycleFirstDart : cycle.firstDart hcycleNotNil = root := by
    rw [cycle.firstDart_eq_head_darts hcycleNotNil]
    exact hcycleHead
  have hsnd : cycle.snd = root.snd :=
    congrArg (fun dart : G.Dart => dart.snd) hcycleFirstDart
  let path : G.Walk root.snd root.fst := cycle.tail.copy hsnd rfl
  have hpath : path.IsPath := by
    simpa [path] using hcycle.isPath_tail
  have hpathDarts : path.darts =
      (faceOrbitDarts graphData root).tail := by
    simp [path, SimpleGraph.Walk.tail,
      SimpleGraph.Walk.darts_drop, hcycleDarts]
  have hwalkEq :
      before.append (SimpleGraph.Walk.cons adj after) = path := by
    apply SimpleGraph.Walk.ext_support
    calc
      (before.append (SimpleGraph.Walk.cons adj after)).support =
          (before.append (SimpleGraph.Walk.cons adj after)).darts.map
              (fun dart => dart.fst) ++ [root.fst] :=
        (before.append
          (SimpleGraph.Walk.cons adj after)).map_fst_darts_append.symm
      _ = path.darts.map (fun dart => dart.fst) ++ [root.fst] := by
        rw [hdarts, hpathDarts]
      _ = path.support := path.map_fst_darts_append
  refine ⟨left, right, adj, before, after, hedgeValue, ?_, hdarts,
    hedgeExact⟩
  rw [hwalkEq]
  exact hpath

/-- A nonzero binary cycle-space vector supported on one face has exactly
that facial boundary as its nonzero support. -/
theorem f2CycleSpace_support_eq_orbitFaceBoundary_of_subset
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (face : OrbitFace graphData.toRotationSystem)
    (chain : G.edgeSet → F2) (hchain : chain ∈ f2CycleSpace G)
    (hsupport : ∀ edge : G.edgeSet, chain edge ≠ 0 →
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (anchor : G.edgeSet) (hanchor : chain anchor ≠ 0) :
    ∀ edge : G.edgeSet, chain edge ≠ 0 ↔
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
  have hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G chain vertex = 0 := by
    intro vertex
    exact scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
      hchain vertex
  have hcubicEdges : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData hcubic
  rcases exists_isCycle_through_of_scalar_ne_zero chain hflow hcubicEdges
      anchor hanchor with
    ⟨root, cycle, hcycle, hanchorCycle, hcycleSupport⟩
  have hcycleFace : ∀ edge : G.edgeSet, edge.1 ∈ cycle.edges →
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
    intro edge hedge
    exact hsupport edge (hcycleSupport edge hedge)
  have hcycleExact :=
    isCycle_mem_edges_iff_mem_orbitFaceBoundary_of_subset graphData
      hcubic htwoSided face cycle hcycle hcycleFace anchor hanchorCycle
  intro edge
  constructor
  · exact hsupport edge
  · intro hedgeFace
    exact hcycleSupport edge ((hcycleExact edge).2 hedgeFace)

end

end Mettapedia.GraphTheory.FourColor
