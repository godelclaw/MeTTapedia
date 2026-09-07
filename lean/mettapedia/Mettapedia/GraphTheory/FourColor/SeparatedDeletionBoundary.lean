import Mettapedia.GraphTheory.FourColor.SeparatedOrderedMeshSites

/-!
# The common-core boundary horn already has a local witness

The existing `FirstTaitOrbitReachesSecondPair` does not require a component
to originate near the first deleted pair or to participate in a prescribed
repair of a target colouring.  Any adjacent common/exposed edge pair gives
a witness at the base colouring, with no preceding Kempe moves.

For ambient-separated adjacent-pair deletions in a cubic graph such an
edge pair is supplied locally at a port of the second deletion.  Hence the
boundary horn is automatic there, independently of planarity, minimality,
mesh structure, or a target colouring.  This identifies a precise limit of
using the unrooted horn as a supplier of remote geometry.
-/

namespace Mettapedia.GraphTheory.FourColor.SeparatedDeletionBoundary

open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24LocalSwapKempeGeneration
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue
open GoertzelV24RotationMultigraphAdapter GoertzelV24TwoEdgeCutMinimality
open SeparatedPairDeletion SeparatedOrderedMeshSites
open SimpleGraph SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The boundary observation at the original colouring, before any moves. -/
def AtBase (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color) : Prop :=
  ∃ first second : Color, ValidColorPair first second ∧
    ∃ component : ((firstDeletionCommonCoreColoring
      (third := target.firstVertex) (fourth := target.secondVertex)
      base).bicoloredSubgraph first second).ConnectedComponent,
      FirstComponentReachesSecondPair source target base first second component

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem atBase_of_adjacent_edges (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring _ base)
    (commonEdge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet)
    (exposedEdge : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).edgeSet)
    (hadj : (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex).lineGraph.Adj
      ((deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).mapEdgeSet commonEdge) exposedEdge)
    (hendpoint : ∃ endpoint : retainedVertexSet source.firstVertex source.secondVertex,
      endpoint ∈ (exposedEdge.1 : Sym2 (retainedVertexSet source.firstVertex source.secondVertex)) ∧
        (endpoint.1 = target.firstVertex ∨ endpoint.1 = target.secondVertex)) :
    AtBase source target base := by
  let common := firstDeletionCommonCoreColoring
    (third := target.firstVertex) (fourth := target.secondVertex) base
  let first := common commonEdge
  let second := base exposedEdge
  have hv : ValidColorPair first second :=
    ⟨hbase _, hbase _, base.valid hadj⟩
  let component := (common.bicoloredSubgraph first second).connectedComponentMk
    ⟨commonEdge, Or.inl rfl⟩
  refine ⟨first, second, hv, component, commonEdge, ?_, exposedEdge, Or.inr rfl,
    hadj, hendpoint⟩
  exact common.mem_kempeComponentSet_self (Or.inl rfl)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem atBase_implies_orbit (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color) (h : AtBase source target base) :
    FirstTaitOrbitReachesSecondPair source target base :=
  ⟨base, Relation.ReflTransGen.refl, h⟩

/-- Cubicity at just one target port and ambient separation supply the
two-edge witness.  There is no noncolourability or target-colouring premise. -/
theorem atBase_of_separated (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring _ base) (hsep : Separated source target)
    (hdegree : 3 ≤ G.degree (target.portVertex 0)) : AtBase source target base := by
  let z := target.portVertex 0
  have hz : z ∈ close G (deleted target) :=
    mem_close.mpr ⟨target.firstVertex, by simp [deleted],
      Or.inr target.first_adj_port_zero⟩
  have hznot : z ∉ close G (deleted source) := fun hs =>
    Finset.disjoint_left.mp hsep hs hz
  have hretains (edge : G.edgeSet) (he : z ∈ (edge.1 : Sym2 V)) :
      IsRetainedAmbientEdge source edge := by
    by_contra h
    exact hznot (mem_close_of_not_retained source edge h he)
  have htcard : (deleted target).card ≤ 2 := by
    calc
      (deleted target).card ≤ ({target.secondVertex} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  have hlt : (deleted target).card < (G.neighborFinset z).card := by
    rw [G.card_neighborFinset_eq_degree]
    dsimp [z]
    omega
  obtain ⟨w, hw, hwt⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hzw : G.Adj z w := (G.mem_neighborFinset z w).mp hw
  let edge : G.edgeSet := ⟨s(z, w), hzw⟩
  have hes : IsRetainedAmbientEdge source edge := hretains edge (Sym2.mem_mk_left _ _)
  have het : IsRetainedAmbientEdge target edge := by
    apply isRetainedAmbientEdge_of_deleted_vertices_not_mem
    · simp only [edge, Sym2.mem_toFinset, Sym2.mem_iff, not_or]
      exact ⟨(target.portNeFirst 0).symm, fun he => hwt (by simp [deleted, he])⟩
    · simp only [edge, Sym2.mem_toFinset, Sym2.mem_iff, not_or]
      exact ⟨(target.portNeSecond 0).symm, fun he => hwt (by simp [deleted, he])⟩
  let exposed := boundaryEdge target 0
  have hexposed : z ∈ (exposed.1 : Sym2 V) :=
    portVertex_mem_boundaryEdgeValue target 0
  have hfs : IsRetainedAmbientEdge source exposed := hretains exposed hexposed
  have hadj : G.lineGraph.Adj edge exposed := by
    apply SimpleGraph.lineGraph_adj_iff_exists.mpr
    refine ⟨?_, z, Sym2.mem_mk_left _ _, hexposed⟩
    intro heq
    exact het.2.1 (congrArg Subtype.val heq)
  let commonEdge := ambientEdgeToCommonCoreEdge source target edge hes het
  let exposedEdge := ambientEdgeToRetainedEdge source exposed hfs
  apply atBase_of_adjacent_edges source target base hbase commonEdge exposedEdge
  · rw [firstCommonCoreEdge_eq_retainedEdge]
    exact ambientEdgeToRetainedEdge_adj source edge exposed hes hfs hadj
  · have hmem : target.firstVertex ∈ (exposed.1 : Sym2 V) := Sym2.mem_mk_left _ _
    have hkeep := endpoints_mem_retainedVertexSet source exposed hfs _ hmem
    refine ⟨⟨target.firstVertex, hkeep⟩, ?_, Or.inl rfl⟩
    exact (mem_ambientEdgeToRetainedEdge_iff source exposed hfs _ hkeep).mpr hmem

/-- The old boundary horn is automatic at a separated cubic target port,
already in the supplied base colouring. -/
theorem orbit_of_separated (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring _ base) (hsep : Separated source target)
    (hdegree : 3 ≤ G.degree (target.portVertex 0)) :
    FirstTaitOrbitReachesSecondPair source target base :=
  atBase_implies_orbit source target base
    (atBase_of_separated source target base hbase hsep hdegree)

/-- Every selected source on a long ordered row has a target whose old
boundary horn is witnessed without a Kempe move, for every proper base. -/
theorem exists_rowSite_with_atBase_boundary
    {a n : Nat} (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (source : Fin n) (hlarge : 64 < n) :
    ∃ target : Fin n, source ≠ target ∧
      ∀ base : (DeletedAdjacentPairGraph G
          (siteData rotation minimal ordered row source).firstVertex
          (siteData rotation minimal ordered row source).secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring _ base →
          AtBase (siteData rotation minimal ordered row source)
            (siteData rotation minimal ordered row target) base := by
  obtain ⟨target, hne, hsep⟩ := exists_separated_rowSite rotation minimal ordered row source hlarge
  refine ⟨target, hne, fun base hbase => ?_⟩
  exact atBase_of_separated _ _ base hbase hsep
    (Nat.le_of_eq ((rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic) _).symm)

/-- The old nine-site no-horn premise is false whenever its selected family
contains a separated pair.  This consumes its actual assignment and horn
definitions, rather than introducing a differently scoped substitute. -/
theorem nineSite_horn_of_separated_pair
    {a n : Nat} (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (slot : Fin 9 ↪ Fin n) (first second : Fin 9)
    (hsep : Separated (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second))
    (assignment : NineSiteTaitAssignment rotation minimal ordered row slot) :
    HasNineSiteBranchingOrBoundary rotation minimal ordered row slot assignment := by
  refine ⟨first, second, Or.inr ?_⟩
  exact orbit_of_separated _ _ (assignment first).1 (assignment first).2 hsep
    (Nat.le_of_eq ((rotation.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic) _).symm)

theorem not_nineSite_no_horn_of_separated_pair
    {a n : Nat} (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a (n + 1))
    (row : Fin a) (slot : Fin 9 ↪ Fin n) (first second : Fin 9)
    (hsep : Separated (rowSiteData rotation minimal ordered row slot first)
      (rowSiteData rotation minimal ordered row slot second)) :
    ¬ (∀ assignment : NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot assignment) := by
  intro hno
  let assignment := baseNineSiteTaitAssignment rotation minimal ordered row slot
  exact hno assignment
    (nineSite_horn_of_separated_pair rotation minimal ordered row slot first second hsep assignment)

end
end Mettapedia.GraphTheory.FourColor.SeparatedDeletionBoundary
