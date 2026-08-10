import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierExcess
import Mettapedia.GraphTheory.FourColor.GoertzelV24BulkCorridor

/-!
# Weighted curvature for annular frontier tangles

Addendum XXV Step 2 gives a signed excess identity.  A signed identity alone
does not bound the number of nonhexagonal faces: pentagons and long faces can
cancel.  This module keeps the source's actual negative-curvature weight
visible and derives the annular weighted balance needed by the L1 corridor
argument.  No configuration catalogue or covering-style reduction is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierWeightedCurvature

open GoertzelV24AnnularFrontierExcess
open GoertzelV24AnnularFrontierExcess.AnnularFrontierEmbeddingExcess
open GoertzelV24BulkCorridor
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

namespace AnnularFrontier

variable {data : AnnularBoundaryData G outerCount}

/-- The fixed positive term in Addendum XXV's annular curvature balance. -/
def annularInterfaceCurvatureConstant (outerCount : Nat) : Nat :=
  10 + 2 * outerCount

/-- The geometric hypotheses on the internal annular cells used by the
clean-corridor extraction.  They are stated as genuine embedding properties,
not as a numerical defect bound. -/
structure AnnularFrontierGeometry (embedded : ClosedWebAnnularEmbedding data) : Prop where
  internalBoundarySimple :
    ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card = embedded.cellulation.faceLength face
  internalMinimumFive :
    ∀ face ∈ embedded.cellulation.interiorFaces,
      5 ≤ (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card
  internalDualConnected :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Connected

/-- One boundary-size entry for each internal facial orbit. -/
def interiorFaceLengths (embedded : ClosedWebAnnularEmbedding data) : Multiset Nat :=
  embedded.cellulation.interiorFaces.val.map fun face =>
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card

/-- Total negative curvature from internal faces longer than hexagons. -/
def interiorNegativeCurvatureWeight
    (embedded : ClosedWebAnnularEmbedding data) : Nat :=
  faceCycleNegativeCurvatureWeight (interiorFaceLengths embedded)

/-- The actual internal nonhexagonal faces. -/
def interiorFaceDefectSet (embedded : ClosedWebAnnularEmbedding data) :
    Finset (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
  embedded.cellulation.interiorFaces.filter fun face =>
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card ≠ 6

/-- The internal boundary-size multiset inherits the source frontier's
girth-five lower bound. -/
theorem interiorFaceLengths_minimumFive
    (embedded : ClosedWebAnnularEmbedding data)
    (geometry : AnnularFrontierGeometry embedded) :
    FaceCycleMinimumFive (interiorFaceLengths embedded) := by
  intro length hlength
  unfold interiorFaceLengths at hlength
  rw [Multiset.mem_map] at hlength
  obtain ⟨face, hface, rfl⟩ := hlength
  exact geometry.internalMinimumFive face hface

/-- On simple internal boundary walks, the boundary curvature sum is the
negative of the literal annular excess. -/
theorem sum_interiorFaceLengthCurvature_eq_neg_interiorExcess
    (embedded : ClosedWebAnnularEmbedding data)
    (geometry : AnnularFrontierGeometry embedded) :
    ((interiorFaceLengths embedded).map faceLengthCurvature).sum =
      -embedded.cellulation.interiorExcess := by
  unfold interiorFaceLengths
  rw [Multiset.map_map]
  unfold FramedAnnularCellulation.interiorExcess
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro face hface
  simp only [Function.comp_apply, faceLengthCurvature, neg_sub]
  rw [geometry.internalBoundarySimple face hface]

/-- Exact weighted version of Addendum XXV Step 2.  It is the honest form of
the source's ``defect budget'': long-face weight and hole surplus together pay
for every internal pentagon plus the fixed annular-interface constant. -/
theorem interiorPentagonCount_add_annularInterfaceConstant_eq_weight_add_boundarySurplus
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    (interiorFaceLengths embedded).count 5 +
        annularInterfaceCurvatureConstant outerCount =
      interiorNegativeCurvatureWeight embedded +
        boundarySurplus embedded := by
  have hcurvature :=
    sum_interiorFaceLengthCurvature_eq_neg_interiorExcess embedded geometry
  have hweighted :=
    sum_faceLengthCurvature_eq_pentagonCount_sub_negativeWeight
      (interiorFaceLengths embedded)
      (interiorFaceLengths_minimumFive embedded geometry)
  have hexcess :=
    interiorExcess_eq_ten_add_twice_outerCount_sub_boundarySurplus
      embedded hdata
  unfold interiorNegativeCurvatureWeight annularInterfaceCurvatureConstant
  rw [hweighted, hexcess] at hcurvature
  have hnatural :
      (interiorFaceLengths embedded).count 5 + 10 + 2 * outerCount =
        faceCycleNegativeCurvatureWeight (interiorFaceLengths embedded) +
          boundarySurplus embedded := by
    exact_mod_cast (show
      ((interiorFaceLengths embedded).count 5 : Int) + 10 + 2 * outerCount =
        faceCycleNegativeCurvatureWeight (interiorFaceLengths embedded) +
          boundarySurplus embedded by
        omega)
  simpa [Nat.add_assoc] using hnatural

/-- A bound on pentagons controls the otherwise unbounded long-face weight.
This is the usable one-way reading of the weighted excess balance. -/
theorem interiorNegativeCurvatureWeight_le_pentagonCount_add_annularInterfaceConstant
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    interiorNegativeCurvatureWeight embedded ≤
      (interiorFaceLengths embedded).count 5 +
        annularInterfaceCurvatureConstant outerCount := by
  have hbalance :=
    interiorPentagonCount_add_annularInterfaceConstant_eq_weight_add_boundarySurplus
      embedded hdata geometry
  unfold annularInterfaceCurvatureConstant at hbalance ⊢
  omega

/-- Counting the literal internal defect faces agrees with counting
nonhexagonal entries of the source's internal face-length multiset. -/
theorem card_interiorFaceDefectSet_eq_nonHexagonalFaceCount
    (embedded : ClosedWebAnnularEmbedding data) :
    (interiorFaceDefectSet embedded).card =
      nonHexagonalFaceCount (interiorFaceLengths embedded) := by
  unfold interiorFaceDefectSet
  rw [Finset.card_def, Finset.filter_val]
  unfold nonHexagonalFaceCount interiorFaceLengths
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- The annular defect count is bounded by the retained negative-curvature
weight and the actual boundary surplus, not by signed excess alone. -/
theorem card_interiorFaceDefectSet_le_twiceWeight_add_boundarySurplus
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (geometry : AnnularFrontierGeometry embedded) :
    (interiorFaceDefectSet embedded).card ≤
      2 * interiorNegativeCurvatureWeight embedded + boundarySurplus embedded := by
  rw [card_interiorFaceDefectSet_eq_nonHexagonalFaceCount embedded]
  calc
    nonHexagonalFaceCount (interiorFaceLengths embedded) ≤
        (interiorFaceLengths embedded).count 5 +
          interiorNegativeCurvatureWeight embedded :=
      nonHexagonalFaceCount_le_pentagonCount_add_negativeWeight
        (interiorFaceLengths embedded)
        (interiorFaceLengths_minimumFive embedded geometry)
    _ ≤ 2 * interiorNegativeCurvatureWeight embedded + boundarySurplus embedded := by
      have hpentagons :=
        interiorPentagonCount_add_annularInterfaceConstant_eq_weight_add_boundarySurplus
          embedded hdata geometry
      unfold annularInterfaceCurvatureConstant at hpentagons
      omega

/-- One internal face cannot contribute more than the total long-face
negative-curvature weight. -/
theorem internalFaceBoundary_card_sub_six_le_weight
    (embedded : ClosedWebAnnularEmbedding data)
    {face : OrbitFace embedded.cellulation.rotation.toRotationSystem}
    (hface : face ∈ embedded.cellulation.interiorFaces) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card - 6 ≤ interiorNegativeCurvatureWeight embedded := by
  unfold interiorNegativeCurvatureWeight faceCycleNegativeCurvatureWeight
  apply Multiset.le_sum_of_mem
  rw [Multiset.mem_map]
  refine ⟨
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card, ?_, rfl⟩
  unfold interiorFaceLengths
  rw [Multiset.mem_map]
  exact ⟨face, hface, rfl⟩

/-- Every internal face boundary has size at most the explicit long-face
weight plus six. -/
theorem internalFaceBoundary_card_le_weight_add_six
    (embedded : ClosedWebAnnularEmbedding data)
    {face : OrbitFace embedded.cellulation.rotation.toRotationSystem}
    (hface : face ∈ embedded.cellulation.interiorFaces) :
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
      face).card ≤ interiorNegativeCurvatureWeight embedded + 6 := by
  by_cases hshort :
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
        face).card ≤ 6
  · omega
  · have hweight :=
      internalFaceBoundary_card_sub_six_le_weight embedded hface
    omega

/-- Restricting facial incidence to internal faces preserves the standard
at-most-two occurrence bound needed by the finite clean-block extractor. -/
theorem internalFace_incidence_le_two
    (embedded : ClosedWebAnnularEmbedding data) :
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

end AnnularFrontier

end

end GoertzelV24AnnularFrontierWeightedCurvature

end Mettapedia.GraphTheory.FourColor
