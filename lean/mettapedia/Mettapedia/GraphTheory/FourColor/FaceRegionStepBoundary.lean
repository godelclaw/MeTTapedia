import Mettapedia.GraphTheory.FourColor.FaceRegionShelling
import Mathlib.Data.Finset.SymmDiff

/-!
# Exact boundary change when a face is added

A face-addition event toggles precisely the edges of that original face
in the complete contour. The number of boundary edges changes by the face
length minus twice the number of attachment edges. We identify this contour
with the actual outer darts of the retained-edge patch, so the length formula
concerns its literal boundary.

The boundary degree imbalance changes by the face length minus six. In
particular a hexagonal step can change width while preserving imbalance.
These laws do not assume that the contour alternates in degree.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionStepBoundary

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24KauffmanFacePotential GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality GoertzelV24BridgelessFaceTwoSided
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation PlanePatchCurvature
open FaceRegionShelling SphericalDistanceContours FaceRegionPatch
open scoped symmDiff

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

/-- A structural face event is literal union on original edge identifiers. -/
theorem event_retained_edges {S R : Region data} (e : Event S R) :
    edges data.toRotationSystem R.faces =
      edges data.toRotationSystem S.faces ∪ orbitFaceBoundary data.toRotationSystem e.face := by
  rw [e.target]
  simp only [edges, Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-- All original edges separating the two facial sides. -/
def contourEdges (S : Finset (OrbitFace data.toRotationSystem)) : Finset G.edgeSet :=
  Finset.univ.filter fun e =>
    orbitFaceBoundaryLinearMap data.toRotationSystem (faceSetIndicator data S) e ≠ 0

theorem mem_contourEdges (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S : Finset (OrbitFace data.toRotationSystem)) (d : data.toRotationSystem.D) :
    data.toRotationSystem.edgeOf d ∈ contourEdges data S ↔
      ((dartOrbitFace data.toRotationSystem d ∈ S ∧
          dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉ S) ∨
        (dartOrbitFace data.toRotationSystem d ∉ S ∧
          dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ S)) := by
  simpa only [contourEdges, Finset.mem_filter, Finset.mem_univ, true_and] using
    boundary_ne_zero_iff_separates data htwo S d

theorem contourEdges_insert (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (S : Finset (OrbitFace data.toRotationSystem)) (f : OrbitFace data.toRotationSystem)
    (hf : f ∉ S) :
    contourEdges data (insert f S) =
      contourEdges data S ∆ orbitFaceBoundary data.toRotationSystem f := by
  ext e
  obtain ⟨d, hd⟩ := data.toRotationSystem.dartsOn_nonempty e
  have he := (data.toRotationSystem.mem_dartsOn).mp hd
  rw [← he, Finset.mem_symmDiff, mem_contourEdges data htwo,
    mem_contourEdges data htwo]
  have hb := edge_mem_iff data.toRotationSystem {f} d
  simp only [edges, Finset.singleton_biUnion, Finset.mem_singleton] at hb
  rw [hb]
  have hn := htwo d
  by_cases hl : dartOrbitFace data.toRotationSystem d = f <;>
    by_cases hr : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) = f <;>
    by_cases hls : dartOrbitFace data.toRotationSystem d ∈ S <;>
    by_cases hrs : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ S <;>
    simp_all

variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (S : Region data)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ S.faces)

include ambient ho

/-- The outer orbit lists precisely the original contour edges. -/
theorem outer_edges_eq_contourEdges :
    (outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer)).image
      (fun d => data.toRotationSystem.edgeOf d.val) = contourEdges data S.faces := by
  have htwo := BridgelessSphericalCubicMapData.orbitFacesTwoSided data.toRotationSystem ambient
  ext e
  constructor
  · rintro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have hout := (mem_outerDarts_iff data S.faces ambient outer ho S.inside S.outside d).mp hd
    have hin := ((edge_mem_iff _ _ d.val).mp d.property).resolve_left hout
    exact (mem_contourEdges data htwo S.faces d.val).mpr (Or.inr ⟨hout, hin⟩)
  · intro he
    obtain ⟨d, hd⟩ := data.toRotationSystem.dartsOn_nonempty e
    have heq := (data.toRotationSystem.mem_dartsOn).mp hd
    have hc := (mem_contourEdges data htwo S.faces d).mp (heq ▸ he)
    have exterior (a : data.toRotationSystem.D)
        (hout : dartOrbitFace data.toRotationSystem a ∉ S.faces)
        (hin : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha a) ∈ S.faces)
        (ha : data.toRotationSystem.edgeOf a = e) :
        e ∈ (outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer)).image
          (fun d => data.toRotationSystem.edgeOf d.val) := by
      let a' : Dart data.toRotationSystem (edges data.toRotationSystem S.faces) :=
        ⟨a, (edge_mem_iff _ _ a).mpr (Or.inr hin)⟩
      exact Finset.mem_image.mpr ⟨a',
        (mem_outerDarts_iff data S.faces ambient outer ho S.inside S.outside a').mpr hout, ha⟩
    rcases hc with hc | hc
    · exact exterior (data.toRotationSystem.alpha d) hc.2
        (by simpa only [data.toRotationSystem.alpha_involutive] using hc.1)
        ((data.toRotationSystem.edge_alpha d).trans heq)
    · exact exterior d hc.1 hc.2 heq

/-- No original edge occurs twice on the actual outer orbit. -/
theorem outer_edges_injective :
    Set.InjOn (fun d : Dart data.toRotationSystem (edges data.toRotationSystem S.faces) =>
      data.toRotationSystem.edgeOf d.val)
      (outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer)) := by
  intro d hd e he heq
  have hdout := (mem_outerDarts_iff data S.faces ambient outer ho S.inside S.outside d).mp hd
  have heout := (mem_outerDarts_iff data S.faces ambient outer ho S.inside S.outside e).mp he
  have hdin := ((edge_mem_iff _ _ d.val).mp d.property).resolve_left hdout
  rcases data.toRotationSystem.edge_fiber_two_cases rfl heq.symm with h | h
  · exact Subtype.ext h.symm
  · exact (heout (h ▸ hdin)).elim

/-- Contour size is the length of the literal outer facial orbit. -/
theorem outer_length_eq_contour_card :
    (outerDarts (toMap data.toRotationSystem (edges data.toRotationSystem S.faces) outer)).card =
      (contourEdges data S.faces).card := by
  rw [← outer_edges_eq_contourEdges data ambient S outer ho]
  exact (Finset.card_image_iff.mpr (outer_edges_injective data ambient S outer ho)).symm

omit ho
variable {data S}

/-- A face step changes only the edges of its own facial cycle. -/
theorem event_contour_update {R : Region data} (e : Event S R) :
    contourEdges data R.faces =
      contourEdges data S.faces ∆ orbitFaceBoundary data.toRotationSystem e.face := by
  rw [e.target]
  exact contourEdges_insert data
    (BridgelessSphericalCubicMapData.orbitFacesTwoSided data.toRotationSystem ambient)
    S.faces e.face e.fresh

omit ambient in
private theorem card_symmDiff_balance {X : Type*} [DecidableEq X] (A B : Finset X) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hb
  omega

/-- Exact length change: remove each attachment edge and insert the other
edges of the new face. Boundary width need not be preserved. -/
theorem event_contour_length {R : Region data} (e : Event S R) :
    (contourEdges data R.faces).card +
        2 * (contourEdges data S.faces ∩ orbitFaceBoundary data.toRotationSystem e.face).card =
      (contourEdges data S.faces).card + (orbitFaceDarts data.toRotationSystem e.face).card := by
  rw [event_contour_update ambient e]
  have htwo := BridgelessSphericalCubicMapData.orbitFacesTwoSided data.toRotationSystem ambient
  rw [← orbitFaceBoundarySimple_of_twoSided data.toRotationSystem htwo e.face]
  exact card_symmDiff_balance _ _

variable (inner : Dart data.toRotationSystem (edges data.toRotationSystem S.faces))
variable (hi : dartOrbitFace data.toRotationSystem inner.val ∉ S.faces)

include hi in
/-- The exact degree imbalance law on the old and new literal boundaries. -/
theorem event_degree_imbalance {R : Region data} (e : Event S R)
    (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
    (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces) :
    let T := toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer
    let U := toMap data.toRotationSystem (edges data.toRotationSystem S.faces) inner
    ((degreeTwo T).card : ℤ) - (boundaryThree T).card =
      (degreeTwo U).card - (boundaryThree U).card +
        (orbitFaceDarts data.toRotationSystem e.face).card - 6 := by
  have hbig := FaceRegionCurvature.boundary_balance data R.faces ambient outer ho R.inside R.outside
  have hsmall := FaceRegionCurvature.boundary_balance data S.faces ambient inner hi S.inside S.outside
  have hsum : (∑ f ∈ R.faces, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ))) =
      (6 - ((orbitFaceDarts data.toRotationSystem e.face).card : ℤ)) +
        ∑ f ∈ S.faces, (6 - ((orbitFaceDarts data.toRotationSystem f).card : ℤ)) := by
    rw [e.target, Finset.sum_insert e.fresh]
  rw [hsum] at hbig
  dsimp
  linarith

end
end Mettapedia.GraphTheory.FourColor.FaceRegionStepBoundary
