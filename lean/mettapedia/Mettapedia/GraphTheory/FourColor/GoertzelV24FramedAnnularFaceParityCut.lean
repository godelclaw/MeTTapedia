import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess
import Mettapedia.GraphTheory.FourColor.GoertzelV24NonisolatedFaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceParityCut

/-!
# Exact face cuts for framed annular cellulations

This module discharges the abstract dual-connectedness and Euler hypotheses of
the bridge-safe face-cut theorem from `FramedAnnularCellulation` itself.  Thus
every closed trail in the graph underlying a framed annulus has an exact
binary labeling of its actual quotient faces, despite the one-sided boundary
stub edges.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24NonisolatedFaceDualConnectedness
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24WalkCycleParity
open GoertzelV24WalkFaceParityCut
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24FramedAnnularExcess.FramedAnnularCellulation

/-- The full quotient facial dual of a framed annular cellulation is
connected.  Mixed boundary/interior degrees are allowed; connectedness and the
stored cyclic rotations are the only graph hypotheses used. -/
theorem fullOrbitFaceInteriorDual_connected
    (cell : FramedAnnularCellulation G) :
    (interiorDualGraph
      (orbitFaceBoundary cell.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace cell.rotation.toRotationSystem))).Connected := by
  apply orbitFaceInteriorDual_connected_of_simpleGraph
    cell.rotation cell.connected
  exact cell.vertexRotation_cyclic

/-- Every closed walk in a framed annular cellulation is represented by a
dart-multiplicity face boundary. -/
theorem exists_orbitFaceLabeling_eq_walkEdgeParity
    (cell : FramedAnnularCellulation G)
    {vertex : V} (walk : G.Walk vertex vertex) :
    ∃ labels : OrbitFace cell.rotation.toRotationSystem → F2,
      orbitFaceParityBoundaryLinearMap
          cell.rotation.toRotationSystem labels =
        walkEdgeParity walk := by
  exact GoertzelV24WalkFaceParityCut.exists_orbitFaceLabeling_eq_walkEdgeParity
    cell.rotation (fullOrbitFaceInteriorDual_connected cell)
      cell.connected cell.euler walk

/-- Every closed trail in a framed annular cellulation cuts its quotient faces
exactly along its edge set. -/
theorem exists_exact_orbitFaceCut_of_isTrail
    (cell : FramedAnnularCellulation G)
    {vertex : V} (walk : G.Walk vertex vertex)
    (htrail : walk.IsTrail) :
    ∃ labels : OrbitFace cell.rotation.toRotationSystem → F2,
      orbitFaceParityBoundaryLinearMap
          cell.rotation.toRotationSystem labels = walkEdgeParity walk ∧
        ∀ dart : cell.rotation.toRotationSystem.D,
          labels (dartOrbitFace cell.rotation.toRotationSystem dart) ≠
              labels (dartOrbitFace cell.rotation.toRotationSystem
                (cell.rotation.toRotationSystem.alpha dart)) ↔
            (cell.rotation.toRotationSystem.edgeOf dart).1 ∈ walk.edges := by
  exact
    GoertzelV24WalkFaceParityCut.exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
      cell.rotation (fullOrbitFaceInteriorDual_connected cell)
        cell.connected cell.euler walk htrail

/-- The exact cut always puts the two named holes either on the same binary
side or on opposite binary sides.  Later chord geometry must prove which
alternative holds for a given candidate wall; it may not assume one. -/
theorem exists_exact_orbitFaceCut_with_hole_dichotomy
    (cell : FramedAnnularCellulation G)
    {vertex : V} (walk : G.Walk vertex vertex)
    (htrail : walk.IsTrail) :
    ∃ labels : OrbitFace cell.rotation.toRotationSystem → F2,
      orbitFaceParityBoundaryLinearMap
          cell.rotation.toRotationSystem labels = walkEdgeParity walk ∧
        (∀ dart : cell.rotation.toRotationSystem.D,
          labels (dartOrbitFace cell.rotation.toRotationSystem dart) ≠
              labels (dartOrbitFace cell.rotation.toRotationSystem
                (cell.rotation.toRotationSystem.alpha dart)) ↔
            (cell.rotation.toRotationSystem.edgeOf dart).1 ∈ walk.edges) ∧
        (labels cell.innerHole = labels cell.outerHole ∨
          labels cell.innerHole ≠ labels cell.outerHole) := by
  rcases exists_exact_orbitFaceCut_of_isTrail cell walk htrail with
    ⟨labels, hlabels, hexact⟩
  exact ⟨labels, hlabels, hexact,
    eq_or_ne (labels cell.innerHole) (labels cell.outerHole)⟩

end GoertzelV24FramedAnnularExcess.FramedAnnularCellulation

end

end Mettapedia.GraphTheory.FourColor
