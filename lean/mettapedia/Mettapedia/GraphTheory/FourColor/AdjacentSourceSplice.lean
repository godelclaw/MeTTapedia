import Mettapedia.GraphTheory.FourColor.AdjacentSourceBoundaryRepair
import Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry

/-!
# Opposite-pair source splicing with coupled reconstruction

Delete two adjacent cubic source vertices and join the exposed half-darts
in the noncrossing 03|12 pairing. Parallel edges retain their identities.
The smaller source stays spherical and cubic; its dual-and-truncate target
has strictly fewer vertices. A proper three-colour witness on the smaller
source supplies a proper exterior and the two seam inequalities. Those
inequalities leave either a direct joint insertion or precisely the
alternating arrangement repaired by embedded separation.

The witness domain is explicit: a smaller target colouring must come from
the supplied smaller source witness. Arbitrary target colourings, universal
occurrence and a smaller unavoidable catalogue are not asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentSourceSplice

open _root_.SimpleGraph SimpleGraphDartRotation
open GoertzelV24AdjacentPairBoundary
open GoertzelV24DeletedRegionRotationSplice GoertzelV24RotationCutDartDecomposition
open GoertzelV24RetainedVertexRotationSplice GoertzelV24PlanarBondSpliceEuler
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24CyclicBoundaryClosure GoertzelV24RotationEdgeBridge
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24FaceDualConnectedness GoertzelV24TwoEdgeCutMinimality
open TwoCellSourceRepair SourceAlternatingBoundaryRepair

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (graphData : Data G) (data : AdjacentPairData G)
  (hcubic : graphData.toRotationSystem.IsCubic)
  (hrotation : VertexRotationCyclic graphData.toRotationSystem)

abbrev ordered := data.rotationOrderedData graphData hcubic hrotation

/-- The actual half-dart splice; no boundary edge is collapsed into simple
adjacency, and no extra source vertex is introduced. -/
abbrev smaller := (ordered graphData data hcubic hrotation).reductionRotationSystem
  graphData SquareReductionSide.join12_30

/-- Cubic rotations and the planar bond determine the splice geometry. -/
theorem smaller_spherical
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    OrbitSphericalCubicMapData (smaller graphData data hcubic hrotation) := by
  let o := ordered graphData data hcubic hrotation
  apply orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond
    (o.rootedGraphData graphData) o.deletedVertices
    (o.leftCrossing .join12_30) (o.rightCrossing .join12_30)
    (o.pairedCut_boundary (o.rootedGraphData graphData) .join12_30)
    (o.leftCrossing_injective .join12_30) (o.rightCrossing_injective .join12_30)
    (o.pairedCuts_disjoint .join12_30) (by omega)
    (o.cutsFollowOppositeDeletedBoundaryOrder graphData
      (data.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder graphData hcubic hrotation)
      .join12_30)
  · simpa [AdjacentPairData.rootedRotationSystem, AdjacentPairData.rootedGraphData] using hsphere
  · simpa [AdjacentPairData.rootedRotationSystem, AdjacentPairData.rootedGraphData] using htwoSided
  · exact hconnected
  · simpa [AdjacentPairData.rootedRotationSystem, AdjacentPairData.rootedGraphData] using hrotation
  · exact hretained
  · exact o.deletedRegion_connected

theorem smaller_rotation : VertexRotationCyclic (smaller graphData data hcubic hrotation) :=
  (ordered graphData data hcubic hrotation).reduction_vertexRotationCyclic
    graphData .join12_30 hrotation

theorem smaller_connected
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    (rotationPrimalGraph (smaller graphData data hcubic hrotation)).Connected :=
  (ordered graphData data hcubic hrotation).reduction_primalConnected
    graphData .join12_30 hretained

/-- The smaller expanded map has the full bridgeless spherical cubic
geometry required of a target, independently of any colouring. -/
theorem smaller_target_geometry
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    BridgelessSphericalCubicMapData
      (DualTruncateColoring.rotation (smaller graphData data hcubic hrotation)) :=
  DualTruncateMapGeometry.mapClass_of _
    (smaller_spherical graphData data hcubic hrotation hsphere htwoSided hconnected hretained)
    (smaller_connected graphData data hcubic hrotation hretained)
    (smaller_rotation graphData data hcubic hrotation)

/-- Count every vertex of the expanded targets, not just the deleted
source vertices. The target carriers are the actual source dart carriers. -/
theorem target_strict_decrease
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    Fintype.card (smaller graphData data hcubic hrotation).D <
      Fintype.card graphData.toRotationSystem.D := by
  have hsmall := (smaller graphData data hcubic hrotation).card_darts_eq_three_times_card_vertices
    (smaller_spherical graphData data hcubic hrotation hsphere htwoSided hconnected hretained).cubic
  have hlarge := graphData.toRotationSystem.card_darts_eq_three_times_card_vertices hcubic
  have hvertices := (ordered graphData data hcubic hrotation).reductionVertex_card_lt
  rw [hsmall, hlarge]
  exact Nat.mul_lt_mul_of_pos_left hvertices (by omega)

omit [DecidableRel G.Adj] in
/-- The source operation removes exactly its two named adjacent vertices. -/
theorem source_vertices_removed :
    Fintype.card (RetainedVertex (deletedRegionKeep data.deletedVertices)) + 2 =
      Fintype.card V := by
  have hdistinct := G.ne_of_adj data.centralAdjacent
  have hcard : Fintype.card {v // v ∈ data.deletedVertices} = 2 := by
    simpa [AdjacentPairData.deletedVertices, hdistinct] using Fintype.card_coe data.deletedVertices
  have hle := Fintype.card_subtype_le (fun v => v ∈ data.deletedVertices)
  have hcompl := Fintype.card_subtype_compl (fun v => v ∈ data.deletedVertices)
  change Fintype.card (RetainedVertex (deletedRegionKeep data.deletedVertices)) =
    Fintype.card V - Fintype.card {v // v ∈ data.deletedVertices} at hcompl
  omega

/-- All expanded target vertices are counted: exactly six disappear. -/
theorem target_vertices_removed
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected) :
    Fintype.card (smaller graphData data hcubic hrotation).D + 6 =
      Fintype.card graphData.toRotationSystem.D := by
  have hsmall := (smaller graphData data hcubic hrotation).card_darts_eq_three_times_card_vertices
    (smaller_spherical graphData data hcubic hrotation hsphere htwoSided hconnected hretained).cubic
  have hlarge := graphData.toRotationSystem.card_darts_eq_three_times_card_vertices hcubic
  have hvertices := source_vertices_removed (ordered graphData data hcubic hrotation)
  rw [hsmall, hlarge]
  omega

/-- An old intact dart as an actual interior dart of the smaller source. -/
def interior (d : graphData.toRotationSystem.D)
    (hv : deletedRegionKeep data.deletedVertices (graphData.toRotationSystem.vertOf d))
    (hw : deletedRegionKeep data.deletedVertices
      (graphData.toRotationSystem.vertOf (graphData.toRotationSystem.alpha d))) :
    (smaller graphData data hcubic hrotation).D := Sum.inl ⟨⟨d,hv⟩,hw⟩

variable (witness : DualTruncateColoring.ThreeVertexColoring
  (smaller graphData data hcubic hrotation))

/-- The smaller witness supplies the old exterior. Removed vertices have
no assigned nonzero colour until the coupled insertion is performed. -/
def exterior (v : V) : Color :=
  if hv : deletedRegionKeep data.deletedVertices v then witness.colour ⟨v,hv⟩ else 0

theorem exterior_retained (v : RetainedVertex (deletedRegionKeep data.deletedVertices)) :
    exterior graphData data hcubic hrotation witness v.1 = witness.colour v := by
  simp only [exterior, dite_eq_left v.2]
  congr 1

/-- Intact smaller darts discharge all genuine old exterior inequalities. -/
theorem exterior_proper : SourcePatchKempe.ExteriorProper graphData.toRotationSystem
    (AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation).outside
    (exterior graphData data hcubic hrotation witness) := by
  rw [AdjacentSourceBoundaryRepair.frame_outside_eq]
  constructor
  · intro v hv
    simp only [exterior, dite_eq_left hv]
    exact witness.nonzero _
  · intro d hv hw
    simp only [exterior, dite_eq_left hv, dite_eq_left hw]
    exact witness.proper (interior graphData data hcubic hrotation d hv hw)

/-- The two new source edges impose the joint opposite-pin constraints. -/
theorem seam_constraints :
    let f := AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation
    let c := exterior graphData data hcubic hrotation witness
    c (f.pins 0) ≠ c (f.pins 3) ∧ c (f.pins 1) ≠ c (f.pins 2) := by
  let o := ordered graphData data hcubic hrotation
  have h0 := witness.proper (o.reductionLeftSeamDart graphData .join12_30 0)
  have h1 := witness.proper (o.reductionLeftSeamDart graphData .join12_30 1)
  rw [o.reductionRotationSystem_alpha_leftSeamDart,
    o.reductionRotationSystem_vertOf_leftSeamDart,
    o.reductionRotationSystem_vertOf_rightSeamDart] at h0 h1
  have hpartial (i : Fin 4) :
      exterior graphData data hcubic hrotation witness (o.portVertex i) =
        witness.colour (o.reductionVertexOfDeletedVertex (o.retainedPort i)) :=
    exterior_retained graphData data hcubic hrotation witness
      (o.reductionVertexOfDeletedVertex (o.retainedPort i))
  have h0' : exterior graphData data hcubic hrotation witness (o.portVertex 0) ≠
      exterior graphData data hcubic hrotation witness (o.portVertex 3) := by
    simpa [SquareReductionSide.leftPort, SquareReductionSide.rightPort, SquareReductionSide.join12_30, SquareReductionSide.join01_23, hpartial] using h0
  have h1' : exterior graphData data hcubic hrotation witness (o.portVertex 1) ≠
      exterior graphData data hcubic hrotation witness (o.portVertex 2) := by
    simpa [SquareReductionSide.leftPort, SquareReductionSide.rightPort, SquareReductionSide.join12_30, SquareReductionSide.join01_23, hpartial] using h1
  dsimp only
  constructor
  · simpa only [AdjacentSourceBoundaryRepair.frame,
      AdjacentSourceBoundaryRepair.reflection_zero, AdjacentSourceBoundaryRepair.reflection_three,
      o, ordered, AdjacentPairData.rotationOrderedData] using h1'
  · simpa only [AdjacentSourceBoundaryRepair.frame,
      AdjacentSourceBoundaryRepair.reflection_one, AdjacentSourceBoundaryRepair.reflection_two,
      o, ordered, AdjacentPairData.rotationOrderedData] using h0'

/-- The seam contract leaves exactly one obstructed arrangement. This
fixed-alphabet law has no graph-specific colouring table. -/
theorem choices_or_alternating (a b c d : Color)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (had : a ≠ d) (hbc : b ≠ c) :
    (∃ x y, TwoCellBoundaryChoice.Compatible a b c d x y) ∨
      (a = c ∧ b = d ∧ a ≠ b) := by
  rw [TwoCellBoundaryChoice.choices_iff a b c d ha hb hc hd]
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with rfl | rfl | rfl <;>
    first | exact (had (by decide +kernel)).elim | exact (hbc (by decide +kernel)).elim | decide +kernel

/-- The extracted exterior observes precisely the actual smaller target
stars at the retained intact source darts. -/
theorem smaller_observations (d : graphData.toRotationSystem.D)
    (hv : deletedRegionKeep data.deletedVertices (graphData.toRotationSystem.vertOf d))
    (hw : deletedRegionKeep data.deletedVertices
      (graphData.toRotationSystem.vertOf (graphData.toRotationSystem.alpha d))) (i : Fin 3) :
    DualTruncateColoring.edgeColour graphData.toRotationSystem
        (exterior graphData data hcubic hrotation witness)
        ((DualTruncateColoring.rotation graphData.toRotationSystem).edgeOf (d,i)) =
      DualTruncateColoring.colouring (smaller graphData data hcubic hrotation) witness
        ((DualTruncateColoring.rotation (smaller graphData data hcubic hrotation)).edgeOf
          (interior graphData data hcubic hrotation d hv hw,i)) := by
  change _ = DualTruncateColoring.edgeColour _ witness.colour _
  change deletedRegionKeep data.deletedVertices d.fst at hv
  change deletedRegionKeep data.deletedVertices d.snd at hw
  fin_cases i
  · apply (DualTruncateColoring.star_colour_zero graphData.toRotationSystem
      (exterior graphData data hcubic hrotation witness) d).trans
    apply Eq.trans _ (DualTruncateColoring.star_colour_zero
      (smaller graphData data hcubic hrotation) witness.colour
      (interior graphData data hcubic hrotation d hv hw)).symm
    change exterior graphData data hcubic hrotation witness d.fst +
      exterior graphData data hcubic hrotation witness d.snd =
      witness.colour ⟨d.fst,hv⟩ + witness.colour ⟨d.snd,hw⟩
    simp only [exterior, dite_eq_left hv, dite_eq_left hw]
  · apply (DualTruncateColoring.star_colour_one graphData.toRotationSystem
      (exterior graphData data hcubic hrotation witness) d).trans
    apply Eq.trans _ (DualTruncateColoring.star_colour_one
      (smaller graphData data hcubic hrotation) witness.colour
      (interior graphData data hcubic hrotation d hv hw)).symm
    change exterior graphData data hcubic hrotation witness d.snd = witness.colour ⟨d.snd,hw⟩
    simp only [exterior, dite_eq_left hw]
  · apply (DualTruncateColoring.star_colour_two graphData.toRotationSystem
      (exterior graphData data hcubic hrotation witness) d).trans
    apply Eq.trans _ (DualTruncateColoring.star_colour_two
      (smaller graphData data hcubic hrotation) witness.colour
      (interior graphData data hcubic hrotation d hv hw)).symm
    change exterior graphData data hcubic hrotation witness d.fst = witness.colour ⟨d.fst,hv⟩
    simp only [exterior, dite_eq_left hv]

variable (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
  (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
  (hconnected : G.Connected)
  (hretained : (SideGraph G (deletedRegionKeep data.deletedVertices)).Connected)

include hsphere htwoSided hconnected hretained in
/-- Every supplied smaller source witness has an available joint repair:
identity for direct insertion, or an actual embedded separating switch. -/
theorem exists_repair : Nonempty (Repair graphData.toRotationSystem
    (AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation)
    (exterior graphData data hcubic hrotation witness)) := by
  let f := AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation
  let c := exterior graphData data hcubic hrotation witness
  have hc := exterior_proper graphData data hcubic hrotation witness
  have hseams := seam_constraints graphData data hcubic hrotation witness
  have h := choices_or_alternating (c (f.pins 0)) (c (f.pins 1))
    (c (f.pins 2)) (c (f.pins 3))
    (hc.1 _ (f.pins_outside 0)) (hc.1 _ (f.pins_outside 1))
    (hc.1 _ (f.pins_outside 2)) (hc.1 _ (f.pins_outside 3)) hseams.1 hseams.2
  rcases h with ⟨x,y,hxy⟩ | ⟨hac,hbd,hab⟩
  · refine ⟨{ pair := .redBlue
              mask := fun _ => False
              mask_decidable := Classical.decPred _
              region := ⟨?_, ?_⟩
              x := x
              y := y
              compatible := ?_ }⟩
    · intro v _ hm; exact hm.elim
    · intro d _ _ _ _; rfl
    · simpa only [SourcePatchKempe.switched, ite_false] using hxy
  · exact ⟨(AdjacentSourceBoundaryRepair.geometry graphData data hsphere htwoSided
      hconnected hrotation hretained).repair c hc (c (f.pins 0)) (c (f.pins 1)) hab
      ⟨rfl,rfl,hac.symm,hbd.symm⟩⟩

/-- One uniformly available repair of the smaller witness. -/
def repair : Repair graphData.toRotationSystem
    (AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation)
    (exterior graphData data hcubic hrotation witness) :=
  Classical.choice (exists_repair graphData data hcubic hrotation witness
    hsphere htwoSided hconnected hretained)

/-- Reconstruct both removed vertices and their shared edge together. -/
def sourceColouring : DualTruncateColoring.ThreeVertexColoring graphData.toRotationSystem :=
  (repair graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained).complete
    (exterior_proper graphData data hcubic hrotation witness)

theorem target_tait : (DualTruncateColoring.rotation graphData.toRotationSystem).IsTaitEdgeColoring
    (DualTruncateColoring.colouring graphData.toRotationSystem
      (sourceColouring graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained)) :=
  DualTruncateColoring.colouring_nonzero _ _

/-- A complete operation tranche on the stated source-witness domain:
valid smaller target geometry, strict size decrease and actual reconstruction. -/
theorem reduction_reconstruction :
    BridgelessSphericalCubicMapData
        (DualTruncateColoring.rotation (smaller graphData data hcubic hrotation)) ∧
      Fintype.card (smaller graphData data hcubic hrotation).D + 6 =
        Fintype.card graphData.toRotationSystem.D ∧
      (DualTruncateColoring.rotation graphData.toRotationSystem).IsTaitEdgeColoring
        (DualTruncateColoring.colouring graphData.toRotationSystem
          (sourceColouring graphData data hcubic hrotation witness
            hsphere htwoSided hconnected hretained)) :=
  ⟨smaller_target_geometry graphData data hcubic hrotation hsphere htwoSided hconnected hretained,
    target_vertices_removed graphData data hcubic hrotation hsphere htwoSided hconnected hretained,
    target_tait graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained⟩

/-- The repair is realised as a saturated switch on actual exterior target
edges, including the identity branch. -/
theorem physical_region :
    let f := AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation
    let c := exterior graphData data hcubic hrotation witness
    let r := repair graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained
    RotationPatchKempe.Region (DualTruncateColoring.rotation graphData.toRotationSystem)
      (fun d => ¬DualTruncateOpenPatch.vertexRegion graphData.toRotationSystem f.selected d)
      (DualTruncateColoring.edgeColour graphData.toRotationSystem c) r.pair
      (DualTruncateKempeTransport.edgeMask graphData.toRotationSystem f.selected c r.pair r.mask) := by
  dsimp only
  let f := AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation
  let r := repair graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained
  let := r.mask_decidable
  apply DualTruncateKempeTransport.physical_region
  · rw [← f.outside_eq_not_selected]
    exact exterior_proper graphData data hcubic hrotation witness
  · rw [← f.outside_eq_not_selected]
    exact r.region

/-- Reconstruction agrees with the justified physical operation at every
old exterior star; its initial observations come from the smaller target. -/
theorem reconstructs :
    let f := AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation
    let c := exterior graphData data hcubic hrotation witness
    let r := repair graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained
    DualTruncateOpenPatch.Extends graphData.toRotationSystem
      (DualTruncateOpenPatch.vertexRegion graphData.toRotationSystem f.selected)
      (RotationPatchKempe.switched (DualTruncateColoring.edgeColour graphData.toRotationSystem c)
        r.pair (DualTruncateKempeTransport.edgeMask graphData.toRotationSystem f.selected c r.pair r.mask))
      (DualTruncateColoring.colouring graphData.toRotationSystem
        (sourceColouring graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained)) := by
  dsimp only
  let f := AdjacentSourceBoundaryRepair.frame graphData data hcubic hrotation
  let c := exterior graphData data hcubic hrotation witness
  let r := repair graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained
  let := r.mask_decidable
  have hc := exterior_proper graphData data hcubic hrotation witness
  have hs := SourcePatchKempe.switched_exterior graphData.toRotationSystem f.outside c hc
    r.pair r.mask r.region
  have hi := f.reconstructed_extends (SourcePatchKempe.switched c r.pair r.mask) hs
    r.x r.y r.compatible
  have he := DualTruncateKempeTransport.exact_effect graphData.toRotationSystem f.selected c
    r.pair r.mask (by rw [← f.outside_eq_not_selected]; exact hc)
    (by rw [← f.outside_eq_not_selected]; exact r.region)
  intro d hd i
  exact (hi d hd i).trans (he d hd i)

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

include graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained in
/-- The reconstructed colouring supplies compatible witnesses on every
complete faithful GSLT sweep of the original actual target. -/
theorem every_complete_sweep (order : List graphData.toRotationSystem.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic graphData.toRotationSystem)
        (DualTruncateConstructionGSLT.rotationCyclic graphData.toRotationSystem)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateConstructionGSLT.supported_encoded_route graphData.toRotationSystem
    (sourceColouring graphData data hcubic hrotation witness hsphere htwoSided hconnected hretained)
    order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.AdjacentSourceSplice
