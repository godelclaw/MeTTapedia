import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceParityBoundary
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity

/-!
# Exact face cuts with bridge-safe parity

The support-based closed-walk face cut assumes that every edge has two
distinct incident quotient faces.  Framed annular tangles contain boundary
stub bridges, so this module obtains the same exact cut from dart-multiplicity
boundaries.  The hypotheses are the actual cellular-sphere ingredients:
connected primal and facial-dual graphs plus Euler's equation.  Cubicity and
global face two-sidedness are not required.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WalkFaceParityCut

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24PrimalCycleSpace
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- On a connected cellular sphere graph, the parity vector of every closed
walk is the dart-multiplicity boundary of an `F2`-labeling of the quotient
faces. -/
theorem exists_orbitFaceLabeling_eq_walkEdgeParity
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {vertex : V} (walk : G.Walk vertex vertex) :
    ∃ labels : OrbitFace data.toRotationSystem → F2,
      orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
        walkEdgeParity walk := by
  have hspan : walkEdgeParity walk ∈ LinearMap.range
      (orbitFaceParityBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceParityBoundaryLinearMap_eq_f2CycleSpace
      data hdual hconnected heuler]
    exact walkEdgeParity_mem_f2CycleSpace_of_closed walk
  exact hspan

/-- For a trail represented by a dart-multiplicity face labeling, crossing a
dart's primal edge changes the binary face label exactly when that edge occurs
in the trail.  A bridge can never occur in a closed trail, and its two equal
dart-side face labels correctly do not change. -/
theorem orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    (data : Data G)
    {vertex : V} {walk : G.Walk vertex vertex}
    (htrail : walk.IsTrail)
    {labels : OrbitFace data.toRotationSystem → F2}
    (hlabels : orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
      walkEdgeParity walk)
    (dart : data.toRotationSystem.D) :
    labels (dartOrbitFace data.toRotationSystem dart) ≠
        labels (dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha dart)) ↔
      (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges := by
  rw [← f2_add_eq_one_iff_ne,
    ← orbitFaceParityBoundaryLinearMap_apply_edgeOf,
    hlabels,
    walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail htrail]

/-- A closed trail on a connected cellular sphere graph has an exact binary
face cut without cubicity or global face two-sidedness. -/
theorem exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    (data : Data G)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {vertex : V} (walk : G.Walk vertex vertex)
    (htrail : walk.IsTrail) :
    ∃ labels : OrbitFace data.toRotationSystem → F2,
      orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
          walkEdgeParity walk ∧
        ∀ dart : data.toRotationSystem.D,
          labels (dartOrbitFace data.toRotationSystem dart) ≠
              labels (dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart)) ↔
            (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges := by
  rcases exists_orbitFaceLabeling_eq_walkEdgeParity
      data hdual hconnected heuler walk with ⟨labels, hlabels⟩
  refine ⟨labels, hlabels, ?_⟩
  exact fun dart => orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
    data htrail hlabels dart

end

end GoertzelV24WalkFaceParityCut

end Mettapedia.GraphTheory.FourColor
