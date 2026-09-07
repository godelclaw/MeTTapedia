import Mettapedia.GraphTheory.FourColor.SphericalContourNodeChain
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-!
# Bounded face size converts dual distance to actual vertex count

The full quotient-face dual has degree at most its face-boundary size.
The existing closed-neighborhood counting theorem supplies the distance
estimate. Cubicity and quotient-face Euler give |V|+4=2|F|. Together these
convert large vertex count into large actual face-dual distance, without
any corridor, contour, or path supplied as a hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24BoundedDegreePath GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24CurvatureScope GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Forgetting the vacuous ambient-face subtype preserves the degree bound. -/
theorem orbitFaceDualGraph_degree_le_boundary (data : Data G)
    (f : OrbitFace data.toRotationSystem) :
    (orbitFaceDualGraph data).degree f ≤ (orbitFaceBoundary data.toRotationSystem f).card := by
  classical
  let D := interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))
  let F : AmbientFace (Finset.univ : Finset (OrbitFace data.toRotationSystem)) :=
    ⟨f, Finset.mem_univ _⟩
  let lift : (orbitFaceDualGraph data).neighborSet f → D.neighborSet F :=
    fun g => ⟨⟨g.val, Finset.mem_univ _⟩, g.property⟩
  have hinj : Function.Injective lift := by
    intro g h heq
    apply Subtype.ext
    exact congrArg (fun x : D.neighborSet F => x.val.val) heq
  calc
    _ = Fintype.card ((orbitFaceDualGraph data).neighborSet f) :=
      (SimpleGraph.card_neighborSet_eq_degree ..).symm
    _ ≤ Fintype.card (D.neighborSet F) := Fintype.card_le_of_injective lift hinj
    _ = D.degree F := SimpleGraph.card_neighborSet_eq_degree ..
    _ ≤ _ := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
        interiorDualGraph_degree_le_faceBoundary_card
          (orbitFaceBoundary data.toRotationSystem) Finset.univ
          (orbitFace_incidence_le_two data.toRotationSystem) F

/-- Actual quotient faces, not deduplicated face-edge sets, enter Euler counting. -/
theorem card_vertices_add_four_eq_two_mul_faces
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS) :
    Fintype.card V + 4 = 2 * Fintype.card (OrbitFace RS) := by
  have heuler := hsphere.euler
  have hVE : (3 : ℤ) * Fintype.card V = 2 * Fintype.card E := by
    exact_mod_cast (RS.card_darts_eq_three_times_card_vertices hsphere.cubic).symm.trans
      RS.card_darts_eq_twice_card_edges
  have hcount : (Fintype.card V : ℤ) + 4 = 2 * Fintype.card (OrbitFace RS) := by
    linarith
  exact_mod_cast hcount

/-- The explicit size threshold for forcing a dual distance of at least r. -/
def boundedFaceSizeBound (B r : ℕ) : ℕ := 2 * (B + 1) ^ r - 4

/-- Generic bounded-face spherical geometry supplies the long dual axis. -/
theorem exists_dual_distance_ge_of_large_vertex_card (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (B r : ℕ)
    (hfaces : ∀ f, (orbitFaceBoundary data.toRotationSystem f).card ≤ B)
    (hlarge : boundedFaceSizeBound B r < Fintype.card V) :
    ∃ root far : OrbitFace data.toRotationSystem, r ≤ (orbitFaceDualGraph data).dist root far := by
  classical
  have heuler := card_vertices_add_four_eq_two_mul_faces data.toRotationSystem hclass.spherical
  have hcard : (B + 1) ^ r < Fintype.card (OrbitFace data.toRotationSystem) := by
    unfold boundedFaceSizeBound at hlarge
    omega
  obtain ⟨root, far, p, _, heq, hlen⟩ := exists_geodesicPath_length_ge_of_pow_lt_card
    (orbitFaceDualGraph data) (orbitFaceDualGraph_connected data hclass) B r
    (fun f => by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
        (orbitFaceDualGraph_degree_le_boundary data f).trans (hfaces f)) hcard
  exact ⟨root, far, heq ▸ hlen⟩

/-- The contrapositive size bound uses the actual graph and all quotient faces. -/
theorem vertex_card_le_of_dual_distances_lt (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (B r : ℕ)
    (hfaces : ∀ f, (orbitFaceBoundary data.toRotationSystem f).card ≤ B)
    (hd : ∀ root far, (orbitFaceDualGraph data).dist root far < r) :
    Fintype.card V ≤ boundedFaceSizeBound B r := by
  by_contra hn
  obtain ⟨root, far, hge⟩ := exists_dual_distance_ge_of_large_vertex_card
    data hclass B r hfaces (Nat.lt_of_not_le hn)
  exact (Nat.not_le_of_gt (hd root far)) hge

end
end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
