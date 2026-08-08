import Mettapedia.GraphTheory.FourColor.GoertzelV24EmbeddedSourceTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24BulkCorridor

/-!
# Weighted curvature inside embedded source trails

The framed Excess Identity is signed: pentagonal and long-face curvature can
cancel.  It therefore does not give a constant bound on the number of
nonhexagonal internal faces.  This module keeps the missing quantity visible
as the total negative-curvature weight `W`.

For an embedded source trail whose internal faces have simple boundaries and
minimum length five, L9 gives the exact weighted balance.  Consequently there
are at most `2W + rho` internal nonhexagons and every internal face has boundary
size at most `W + 6`.  The separate corridor module imports the heavier clean
block extractor only when that geometric conclusion is needed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BulkCorridor
open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SourceTrail

namespace AnnularEmbedding

/-- The geometric hypotheses on the internal cells needed by the clean-block
argument.  These are semantic properties of the annular embedding, not
numerical conclusions smuggled into its statement. -/
structure CorridorGeometry {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Prop where
  internalBoundarySimple :
    ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card = embedded.cellulation.faceLength face
  internalMinimumFive :
    ∀ face ∈ embedded.cellulation.interiorFaces,
      5 ≤ (orbitFaceBoundary
        embedded.cellulation.rotation.toRotationSystem face).card
  internalDualConnected :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Connected

/-- Internal face-boundary lengths, with one entry for each internal facial
orbit. -/
def interiorFaceLengths {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Multiset Nat :=
  embedded.cellulation.interiorFaces.val.map fun face =>
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card

/-- Total long-face negative curvature carried by the internal cells. -/
def interiorNegativeCurvatureWeight {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) : Nat :=
  faceCycleNegativeCurvatureWeight embedded.interiorFaceLengths

/-- Nonhexagonal internal faces, defined locally so the weighted-curvature
layer does not import the heavier path/corridor extraction stack. -/
def interiorFaceDefectSet {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Finset (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
  embedded.cellulation.interiorFaces.filter fun face =>
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card ≠ 6

/-- Abstract face-length family witnessing the arithmetic gap in the
unweighted reading of L9.  It has `k` pentagons and `k + excess`
heptagons. -/
def fixedInteriorExcessFamily (excess k : Nat) : Multiset Nat :=
  Multiset.replicate k 5 + Multiset.replicate (k + excess) 7

theorem fixedInteriorExcessFamily_minimumFive (excess k : Nat) :
    FaceCycleMinimumFive (fixedInteriorExcessFamily excess k) := by
  intro length hlength
  rcases Multiset.mem_add.mp hlength with hfive | hseven
  · have hlengthFive := (Multiset.mem_replicate.mp hfive).2
    omega
  · have hlengthSeven := (Multiset.mem_replicate.mp hseven).2
    omega

/-- The signed excess of the family is fixed while `k` varies. -/
theorem fixedInteriorExcessFamily_signedExcess (excess k : Nat) :
    ((fixedInteriorExcessFamily excess k).map
      (fun length : Nat => (length : Int) - 6)).sum = excess := by
  simp [fixedInteriorExcessFamily]

/-- Its number of nonhexagonal faces nevertheless grows without bound. -/
theorem fixedInteriorExcessFamily_nonHexagonalFaceCount (excess k : Nat) :
    nonHexagonalFaceCount (fixedInteriorExcessFamily excess k) =
      2 * k + excess := by
  have hfive :
      (Multiset.replicate k 5).filter (fun length => length ≠ 6) =
        Multiset.replicate k 5 := by
    apply Multiset.filter_eq_self.mpr
    intro length hlength
    have hlengthFive := (Multiset.mem_replicate.mp hlength).2
    omega
  have hseven :
      (Multiset.replicate (k + excess) 7).filter
          (fun length => length ≠ 6) =
        Multiset.replicate (k + excess) 7 := by
    apply Multiset.filter_eq_self.mpr
    intro length hlength
    have hlengthSeven := (Multiset.mem_replicate.mp hlength).2
    omega
  unfold nonHexagonalFaceCount fixedInteriorExcessFamily
  rw [Multiset.filter_add, hfive, hseven]
  simp
  omega

/-- A fixed signed Excess Identity alone cannot imply any constant defect
budget: pentagon/heptagon cancellation leaves arbitrarily many nonhexagons.
This theorem isolates the precise source-level obstruction repaired below by
retaining negative-curvature weight. -/
theorem exists_fixedSignedExcess_with_arbitrarily_many_nonHexagons
    (excess bound : Nat) :
    ∃ lengths : Multiset Nat,
      FaceCycleMinimumFive lengths ∧
      (lengths.map (fun length : Nat => (length : Int) - 6)).sum = excess ∧
      bound ≤ nonHexagonalFaceCount lengths := by
  refine ⟨fixedInteriorExcessFamily excess bound,
    fixedInteriorExcessFamily_minimumFive excess bound,
    fixedInteriorExcessFamily_signedExcess excess bound, ?_⟩
  rw [fixedInteriorExcessFamily_nonHexagonalFaceCount]
  omega

theorem interiorFaceLengths_minimumFive
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    FaceCycleMinimumFive embedded.interiorFaceLengths := by
  intro length hlength
  unfold interiorFaceLengths at hlength
  rw [Multiset.mem_map] at hlength
  obtain ⟨face, hface, rfl⟩ := hlength
  exact geometry.internalMinimumFive face hface

/-- On simple internal face boundaries, the curvature sum of the boundary
length multiset is the negative of the signed annular excess. -/
theorem sum_interiorFaceLengthCurvature_eq_neg_interiorExcess
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    (embedded.interiorFaceLengths.map faceLengthCurvature).sum =
      -embedded.cellulation.interiorExcess := by
  unfold interiorFaceLengths
  rw [Multiset.map_map]
  unfold FramedAnnularCellulation.interiorExcess
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro face hface
  simp only [Function.comp_apply, faceLengthCurvature, neg_sub]
  rw [geometry.internalBoundarySimple face hface]

/-- Exact weighted L9 balance.  The long-face weight and boundary surplus pay
for every pentagon plus the two missing-edge feet and frozen stub feet. -/
theorem interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorFaceLengths.count 5 + 4 +
        2 * source.frozenInterfaceStubVertices.card =
      embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  have hcurvature :=
    embedded.sum_interiorFaceLengthCurvature_eq_neg_interiorExcess geometry
  have hweighted :=
    sum_faceLengthCurvature_eq_pentagonCount_sub_negativeWeight
      embedded.interiorFaceLengths
      (embedded.interiorFaceLengths_minimumFive geometry)
  have hexcess := embedded.interiorExcess_eq_source_framed_constant hsource
  unfold interiorNegativeCurvatureWeight
  rw [hweighted, hexcess] at hcurvature
  exact_mod_cast (show
    (embedded.interiorFaceLengths.count 5 : Int) + 4 +
          2 * source.frozenInterfaceStubVertices.card =
        faceCycleNegativeCurvatureWeight embedded.interiorFaceLengths +
          embedded.cellulation.boundarySurplus source.toFramedTrailData by
    omega)

theorem interiorPentagonCount_le_weight_add_boundarySurplus
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorFaceLengths.count 5 ≤
      embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  have hbalance :=
    embedded.interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
      hsource geometry
  omega

/-- Every unit of internal negative curvature is paid for by a pentagon or
one of the fixed framed source feet.  This is the useful reverse reading of
the exact weighted L9 balance: bounding pentagons bounds the long-face
weight, without treating signed excess as an unsigned defect budget. -/
theorem interiorNegativeCurvatureWeight_le_pentagonCount_add_sourceFeet
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorNegativeCurvatureWeight ≤
      embedded.interiorFaceLengths.count 5 + 4 +
        2 * source.frozenInterfaceStubVertices.card := by
  have hbalance :=
    embedded.interiorPentagonCount_add_sourceFeet_eq_weight_add_boundarySurplus
      hsource geometry
  omega

/-- Counting defects through the internal face set agrees with counting
nonhexagonal entries in the internal length multiset. -/
theorem card_interiorFaceDefectSet_eq_nonHexagonalFaceCount
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    embedded.interiorFaceDefectSet.card =
        nonHexagonalFaceCount embedded.interiorFaceLengths := by
  unfold interiorFaceDefectSet
  rw [Finset.card_def, Finset.filter_val]
  unfold nonHexagonalFaceCount interiorFaceLengths
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- Faithful annular defect budget: it depends on the actual negative
curvature weight and cannot in general be replaced by a constant. -/
theorem card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry) :
    embedded.interiorFaceDefectSet.card ≤
      2 * embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  rw [embedded.card_interiorFaceDefectSet_eq_nonHexagonalFaceCount]
  calc
    nonHexagonalFaceCount embedded.interiorFaceLengths ≤
        embedded.interiorFaceLengths.count 5 +
          embedded.interiorNegativeCurvatureWeight :=
      nonHexagonalFaceCount_le_pentagonCount_add_negativeWeight
        embedded.interiorFaceLengths
        (embedded.interiorFaceLengths_minimumFive geometry)
    _ ≤ 2 * embedded.interiorNegativeCurvatureWeight +
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
      have hpentagons :=
        embedded.interiorPentagonCount_le_weight_add_boundarySurplus
          hsource geometry
      omega

theorem internalFaceBoundary_card_sub_six_le_weight
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    {face : OrbitFace embedded.cellulation.rotation.toRotationSystem}
    (hface : face ∈ embedded.cellulation.interiorFaces) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card - 6 ≤ embedded.interiorNegativeCurvatureWeight := by
  unfold interiorNegativeCurvatureWeight faceCycleNegativeCurvatureWeight
  apply Multiset.le_sum_of_mem
  rw [Multiset.mem_map]
  refine ⟨
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card, ?_, rfl⟩
  unfold interiorFaceLengths
  rw [Multiset.mem_map]
  exact ⟨face, hface, rfl⟩

/-- Every internal face has boundary size at most `W + 6`. -/
theorem internalFaceBoundary_card_le_weight_add_six
    {source : SourceTrail G} (embedded : source.AnnularEmbedding)
    {face : OrbitFace embedded.cellulation.rotation.toRotationSystem}
    (hface : face ∈ embedded.cellulation.interiorFaces) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card ≤ embedded.interiorNegativeCurvatureWeight + 6 := by
  by_cases hshort :
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ 6
  · omega
  · have hexcess := embedded.internalFaceBoundary_card_sub_six_le_weight hface
    omega

/-- Restricting the full orbit-face incidence model to the internal faces
preserves the at-most-two-faces-per-edge bound. -/
theorem internalFace_incidence_le_two
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    ∀ edge,
      totalIncidenceCount
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces edge ≤ 2 := by
  intro edge
  calc
    totalIncidenceCount
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces edge ≤
      totalIncidenceCount
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) edge := by
        exact Finset.card_le_card
          (Finset.filter_subset_filter _ (by simp))
    _ ≤ 2 := orbitFace_incidence_le_two
      embedded.cellulation.rotation.toRotationSystem edge

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
