import Mettapedia.GraphTheory.FourColor.StructuralCutSnipPatch
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedShoreLiteralNode
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided

/-!
# Snipping any connected planar bond

The contour geometry used to produce a bond is irrelevant once both sides of
the vertex cut are connected. This module derives the full physical snip
patch from that condition. In particular, the result applies to the
connected cuts at internal forks of a branch decomposition; it does not
assume that a general branch cut is a contour of the face dual.
-/

namespace Mettapedia.GraphTheory.FourColor.StructuralCutPlanarBondPatch

open Equiv Equiv.Perm Mettapedia.GraphTheory
open SimpleGraphDartRotation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24CanonicalHubClosure
open GoertzelV24CanonicalHubCyclicity
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24CyclicBondBoundary.CyclicBondBoundaryData
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24VertexSideOpenTangle
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24SimpleGraphTaitBridge
open StructuralCutRLink
open StructuralCutSnipDisk
open StructuralCutSnipPatch

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

noncomputable section

private theorem graph_connected
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem) :
    G.Connected := by
  simpa only [rotationPrimalGraph_toRotationSystem_eq]
    using hclass.primalConnected

/-- Both connected sides and ambient bridge-freedom force one nontrivial
first-return cycle on the boundary of a planar bond. -/
theorem retainedSuccessor_isCycle_of_planarBond
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (deleted : Finset V)
    (hretained :
      (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted :
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected) :
    (retainedRegionBoundarySuccessor rotation.toRotationSystem
      (deletedRegionKeep deleted)).IsCycle := by
  let RS := rotation.toRotationSystem
  let keep := deletedRegionKeep deleted
  obtain ⟨⟨inside, hinside⟩, _⟩ :=
    (SimpleGraph.connected_iff_exists_forall_reachable _).mp hretained
  obtain ⟨⟨outside, houtside⟩, _⟩ :=
    (SimpleGraph.connected_iff_exists_forall_reachable _).mp hdeleted
  have hcard : 2 ≤ Fintype.card (BoundaryDart RS keep) :=
    two_le_card_boundaryDart_of_connected_edgeBridgeFree RS
      hclass.primalConnected hclass.edgeBridgeFree keep
      ⟨inside, hinside⟩ ⟨outside, houtside⟩
  have hpair : ∃ first second : BoundaryDart RS keep, first ≠ second := by
    by_contra hnone
    have hsub : Subsingleton (BoundaryDart RS keep) :=
      ⟨by intro x y; by_contra hxy; exact hnone ⟨x, y, hxy⟩⟩
    have hle : Fintype.card (BoundaryDart RS keep) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨first, second, hne⟩ := hpair
  have hhub : (canonicalHubRotation RS keep).IsCycle :=
    canonicalHubRotation_isCycle_of_planarBond rotation deleted
      first.1 hclass.spherical htwo (graph_connected rotation hclass)
      hclass.vertexRotationCyclic hretained hdeleted first second hne
  simpa only [RS, keep, canonicalHubRotation, inv_inv] using hhub.inv

/-- The two computed cap orders are conjugate through the actual ambient
edge reversal. No border order is selected independently. -/
theorem deletedHub_eq_conjugate_retainedSuccessor_of_planarBond
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (deleted : Finset V)
    (hretained :
      (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted :
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected) :
    canonicalHubRotation rotation.toRotationSystem
        (deletedSideKeep deleted) =
      (complementBoundaryAlphaEquiv rotation.toRotationSystem deleted).permCongr
        (retainedRegionBoundarySuccessor rotation.toRotationSystem
          (deletedRegionKeep deleted)) := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS deleted
  have hrev := orientationReversing_canonicalHubRotation_of_planarBond
    rotation deleted hclass.spherical htwo (graph_connected rotation hclass)
      hclass.vertexRotationCyclic hretained hdeleted
  ext c
  let b := matching.symm c
  have hc : c = matching b := by simp [b]
  rw [hc]
  have h := hrev b
  change (canonicalHubRotation RS (deletedSideKeep deleted)) (matching b) =
      matching ((canonicalHubRotation RS
        (deletedRegionKeep deleted)).symm b) at h
  have hroot : (canonicalHubRotation RS
      (deletedRegionKeep deleted)).symm =
      retainedRegionBoundarySuccessor RS
        (deletedRegionKeep deleted) := by
    simp only [canonicalHubRotation]
    exact inv_inv _
  rw [hroot] at h
  simpa [RS, matching, Equiv.permCongr_apply,
    canonicalHubRotation] using h

private theorem remNodeCycle_of_planarBond
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (deleted : Finset V)
    (hretained :
      (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted :
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedSideKeep deleted)) :
    ∀ x y : RemDarts rotation.toRotationSystem deleted,
      x ∈ remBorder rotation.toRotationSystem deleted →
      (((remMap rotation.toRotationSystem deleted outer).node).SameCycle
        x y ↔ y ∈ remBorder rotation.toRotationSystem deleted) := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS deleted
  let σ := retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted)
  have hσ : σ.IsCycle :=
    retainedSuccessor_isCycle_of_planarBond rotation hclass htwo
      deleted hretained hdeleted
  have heq : canonicalHubRotation RS (deletedSideKeep deleted) =
      matching.permCongr σ :=
    deletedHub_eq_conjugate_retainedSuccessor_of_planarBond
      rotation hclass htwo deleted hretained hdeleted
  have hcycle : (canonicalHubRotation RS
      (deletedSideKeep deleted)).IsCycle := by
    rw [heq]
    exact isCycle_permCongr matching σ hσ
  have hfixfree : ∀ b : BoundaryDart RS (deletedSideKeep deleted),
      canonicalHubRotation RS (deletedSideKeep deleted) b ≠ b := by
    intro b hb
    have hnot := retainedSuccessor_ne_self RS
      (deletedSideKeep deleted) htwo b
    apply hnot
    change (retainedRegionBoundarySuccessor RS
      (deletedSideKeep deleted))⁻¹ b = b at hb
    have h := congrArg (retainedRegionBoundarySuccessor RS
      (deletedSideKeep deleted)) hb
    simpa using h.symm
  exact remNodeCycle RS deleted outer hcycle hfixfree

/-- Any physical connected planar vertex bond is a nonempty-ring snip patch
of the ambient map. This is the geometry needed at a connected branch cut;
the contour-cut theorem is one specialization. -/
theorem planarBond_patch
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (deleted : Finset V)
    (hretained :
      (G.induce {v | deletedRegionKeep deleted v}).Connected)
    (hdeleted :
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected)
    (outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep deleted)) :
    Hypermap.Patch
      (Hypermap.ofRotationSystem rotation.toRotationSystem)
      (diskMap rotation.toRotationSystem deleted outerD)
      (remMap rotation.toRotationSystem deleted outerR)
      (diskEmbed rotation.toRotationSystem deleted)
      (remEmbed rotation.toRotationSystem deleted)
      (diskBorder rotation.toRotationSystem deleted)
      (remBorder rotation.toRotationSystem deleted) := by
  let RS := rotation.toRotationSystem
  have htwo : OrbitFacesTwoSided RS :=
    GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      RS hclass
  refine {
    injd := diskEmbed_injective RS deleted
    injr := remEmbed_injective RS deleted
    edgeCycle_d := ?_
    nodeCycle_r := ?_
    simple_d := ?_
    cover := cover RS deleted
    ring_eq := ring_images_equal RS deleted
    ring_rev := ring_reverse RS deleted outerD outerR
      (deletedHub_eq_conjugate_retainedSuccessor_of_planarBond
        rotation hclass htwo deleted hretained hdeleted)
    edge_d := diskEmbed_edge_off_border RS deleted outerD
    node_d := diskEmbed_node RS deleted outerD
    edge_r := remEmbed_edge RS deleted outerR
    node_r := remEmbed_node_off_border RS deleted outerR
  }
  · exact edgeCycle_border _ _
      (retainedSuccessor_isCycle_of_planarBond rotation hclass htwo
        deleted hretained hdeleted)
      (fun b => retainedSuccessor_ne_self RS
        (deletedRegionKeep deleted) htwo b)
  · exact remNodeCycle_of_planarBond rotation hclass htwo
      deleted hretained hdeleted outerR
  · apply simple_border_of_hubFacesDistinct
    simpa only [diskTangle,
      GoertzelV24VertexSideOpenTangle.canonicalHubRotation] using
      hubFacesDistinct_canonical RS (deletedRegionKeep deleted) outerD

/-- The snip ring is precisely the physical boundary-dart carrier; no
additional hub or interior darts are counted as ports. -/
noncomputable def diskBorderPortEquiv
    (RS : RotationSystem V E) (deleted : Finset V) :
    {d : DiskDarts RS deleted // d ∈ diskBorder RS deleted} ≃
      BoundaryDart RS (deletedRegionKeep deleted) where
  toFun d := Classical.choose d.2
  invFun b := ⟨Sum.inr b, ⟨b, rfl⟩⟩
  left_inv d := by
    apply Subtype.ext
    exact Classical.choose_spec d.2
  right_inv b := by
    apply Sum.inr_injective
    exact Classical.choose_spec (show
      (Sum.inr b : DiskDarts RS deleted) ∈ diskBorder RS deleted from ⟨b, rfl⟩)

theorem card_diskBorder_eq_card_boundaryDart
    (RS : RotationSystem V E) (deleted : Finset V) :
    Fintype.card {d : DiskDarts RS deleted // d ∈ diskBorder RS deleted} =
      Fintype.card (BoundaryDart RS (deletedRegionKeep deleted)) :=
  Fintype.card_congr (diskBorderPortEquiv RS deleted)

/-- In `Patch`'s native `Set.ncard` formulation, the absorbed ring length
is the number of actual crossing darts. -/
theorem ncard_diskBorder_eq_card_boundaryDart
    (RS : RotationSystem V E) (deleted : Finset V) :
    (diskBorder RS deleted).ncard =
      Fintype.card (BoundaryDart RS (deletedRegionKeep deleted)) := by
  change (Set.range (Sum.inr : BoundaryDart RS (deletedRegionKeep deleted) →
    DiskDarts RS deleted)).ncard = _
  rw [Set.ncard_range_of_injective Sum.inr_injective]
  exact Nat.card_eq_fintype_card

section DecompositionCut

variable [G.LocallyFinite]

/-- The literal node constructed at a connected decomposition fork is an
actual planar snip patch, with the node's existing roots and no added border
or orbit-count assumptions. -/
theorem literalShoreNode_patch
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    {k w : Nat} (node : LiteralShoreNode rotation k w) :
    Hypermap.Patch
      (Hypermap.ofRotationSystem rotation.toRotationSystem)
      (diskMap rotation.toRotationSystem
        (majorityDeletedVertices G node.shore) node.innerOuter)
      (remMap rotation.toRotationSystem
        (majorityDeletedVertices G node.shore) node.outsideOuter)
      (diskEmbed rotation.toRotationSystem
        (majorityDeletedVertices G node.shore))
      (remEmbed rotation.toRotationSystem
        (majorityDeletedVertices G node.shore))
      (diskBorder rotation.toRotationSystem
        (majorityDeletedVertices G node.shore))
      (remBorder rotation.toRotationSystem
        (majorityDeletedVertices G node.shore)) := by
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation hclass.spherical.cubic
  have hshores := connected_majority_shores_and_width
    hcubicEdges node.shore node.shoreConnected node.complementConnected
      node.majorityNonempty node.complementNonempty
  have hretained :
      (G.induce {v | deletedRegionKeep
        (majorityDeletedVertices G node.shore) v}).Connected := by
    have hset : {v | deletedRegionKeep
        (majorityDeletedVertices G node.shore) v} =
        {v | majorityVertexSide G node.shore v} := by
      ext v
      exact majorityRetainedKeep_iff node.shore v
    rw [hset]
    exact hshores.1
  have hdeleted :
      (G.induce {v | ¬ deletedRegionKeep
        (majorityDeletedVertices G node.shore) v}).Connected := by
    have hset : {v | ¬ deletedRegionKeep
        (majorityDeletedVertices G node.shore) v} =
        {v | ¬ majorityVertexSide G node.shore v} := by
      ext v
      exact not_congr (majorityRetainedKeep_iff node.shore v)
    rw [hset]
    exact hshores.2.1
  exact planarBond_patch rotation hclass
    (majorityDeletedVertices G node.shore) hretained hdeleted
    node.innerOuter node.outsideOuter

/-- Gonthier's genus-additivity law now holds at every *actual* connected
decomposition node, rather than only at contour cuts. -/
theorem literalShoreNode_genus_add
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    {k w : Nat} (node : LiteralShoreNode rotation k w) :
    Hypermap.genus (Hypermap.ofRotationSystem rotation.toRotationSystem) =
      Hypermap.genus (diskMap rotation.toRotationSystem
        (majorityDeletedVertices G node.shore) node.innerOuter) +
      Hypermap.genus (remMap rotation.toRotationSystem
        (majorityDeletedVertices G node.shore) node.outsideOuter) :=
  (literalShoreNode_patch rotation hclass node).genus_patch

/-- Exact face accounting across a physical branch cut. The correction term
is the *literal* crossing-dart width, not a freely chosen ring length. -/
theorem literalShoreNode_face_count
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    {k w : Nat} (node : LiteralShoreNode rotation k w) :
    GoertzelV24PermutationOrbitSurgery.orbitCount
        (diskMap rotation.toRotationSystem
          (majorityDeletedVertices G node.shore) node.innerOuter).face +
      GoertzelV24PermutationOrbitSurgery.orbitCount
        (remMap rotation.toRotationSystem
          (majorityDeletedVertices G node.shore) node.outsideOuter).face =
      boundaryWidth rotation node.shore +
        GoertzelV24PermutationOrbitSurgery.orbitCount
          rotation.toRotationSystem.phi := by
  have h := (literalShoreNode_patch rotation hclass node).orbitCount_face_add
  rw [ncard_diskBorder_eq_card_boundaryDart] at h
  simpa only [Hypermap.ofRotationSystem_face, boundaryWidth,
    majorityRetainedKeep] using h

/-- Both physical pieces at a connected decomposition node are planar. -/
theorem literalShoreNode_planar_parts
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    {k w : Nat} (node : LiteralShoreNode rotation k w) :
    Hypermap.Planar (diskMap rotation.toRotationSystem
      (majorityDeletedVertices G node.shore) node.innerOuter) ∧
    Hypermap.Planar (remMap rotation.toRotationSystem
      (majorityDeletedVertices G node.shore) node.outsideOuter) := by
  exact ((literalShoreNode_patch rotation hclass node).planar_patch).mp
    (hypermap_planar_of_spherical rotation.toRotationSystem
      hclass.spherical hclass.primalConnected hclass.vertexRotationCyclic)

omit [G.LocallyFinite] in
/-- The snip patch at a decomposition fork inherits the branch-width
interface bound, in the patch's own border carrier rather than a parallel
vertex-middle approximation. -/
theorem literalShoreNode_patch_border_card_le
    (rotation : Data G) {k w : Nat}
    (node : LiteralShoreNode rotation k w) :
    Fintype.card
      {d : DiskDarts rotation.toRotationSystem
            (majorityDeletedVertices G node.shore) //
        d ∈ diskBorder rotation.toRotationSystem
          (majorityDeletedVertices G node.shore)} ≤ k := by
  rw [card_diskBorder_eq_card_boundaryDart]
  exact node.widthBound

end DecompositionCut

end
end Mettapedia.GraphTheory.FourColor.StructuralCutPlanarBondPatch
