import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpaceEquality
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WalkFaceCut

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- On a connected cellular sphere graph, the parity vector of every closed
walk is the boundary of an `F2`-labeling of the quotient faces. -/
theorem exists_orbitFaceLabeling_eq_walkEdgeParity
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex) :
    ∃ labels : OrbitFace data.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap data.toRotationSystem labels =
        walkEdgeParity walk := by
  have hspan : walkEdgeParity walk ∈ LinearMap.range
      (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hsphere]
    exact walkEdgeParity_mem_f2CycleSpace_of_closed walk
  exact hspan

/-- For a trail represented by a face labeling, crossing a dart's primal edge
changes the binary face label exactly when that edge occurs in the trail. -/
theorem orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {vertex : V} {walk : G.Walk vertex vertex}
    (htrail : walk.IsTrail)
    {labels : OrbitFace data.toRotationSystem → F2}
    (hlabels : orbitFaceBoundaryLinearMap data.toRotationSystem labels =
      walkEdgeParity walk)
    (dart : data.toRotationSystem.D) :
    labels (dartOrbitFace data.toRotationSystem dart) ≠
        labels (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart)) ↔
      (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges := by
  rw [← f2_add_eq_one_iff_ne,
    ← orbitFaceBoundaryLinearMap_apply_edgeOf
      data.toRotationSystem htwoSided labels dart,
    hlabels,
    walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail htrail]

/-- A closed trail on a connected cellular sphere graph therefore has an
exact face cut: its edges, and only its edges, separate differently labeled
quotient faces. -/
theorem exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex)
    (htrail : walk.IsTrail) :
    ∃ labels : OrbitFace data.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap data.toRotationSystem labels =
          walkEdgeParity walk ∧
        ∀ dart : data.toRotationSystem.D,
          labels (dartOrbitFace data.toRotationSystem dart) ≠
              labels (dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart)) ↔
            (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges := by
  rcases exists_orbitFaceLabeling_eq_walkEdgeParity
      data htwoSided hdual hconnected hsphere walk with ⟨labels, hlabels⟩
  refine ⟨labels, hlabels, ?_⟩
  exact fun dart => orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    data htwoSided htrail hlabels dart

end

end GoertzelV24WalkFaceCut

end Mettapedia.GraphTheory.FourColor
