import Mettapedia.GraphTheory.FourColor.ContourFirstHit
import Mettapedia.GraphTheory.FourColor.OrderedContourExtraction
import Mettapedia.GraphTheory.FourColor.SphericalContourBondChain

/-!
# Actual spherical contours supply the wall-facing ordered mesh

Simple contour cycles are opened into simple paths with the same vertex
sets. First-hit positions on full-ambient linkage paths are increasing in
depth. Thinning and independently orienting the rows supplies rectangular
branch order. Consequently excluding an ordered mesh forces a complete
bounded bond, without assuming absence of the more permissive mesh.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RotationMultigraphAdapter GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open SphericalDistanceContours VertexSplitCut RotationWalkMeshPath OrderedContourExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The contour and all branch-order data are constructed, not supplied. -/
theorem exists_orderedMesh_of_contour_linkage (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo a b N : ℕ)
    (hd : lo + a ≤ (orbitFaceDualGraph data).dist root far)
    (L : Linkage G (frontier data root far lo) (frontier data root far (lo + a - 1)) N)
    (hN : b ^ (2 ^ a) < N) :
    Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b) := by
  classical
  have hcycles (t : Fin a) : ∃ s : V, ∃ c : G.Walk s s, c.IsCycle ∧
      ∀ v, v ∈ c.support ↔ v ∈ frontier data root far (lo + t.val) := by
    obtain ⟨s, c, hc, _, hv⟩ :=
      exists_distance_contour data hclass htwo root far (lo + t.val) (by omega)
    exact ⟨s, c, hc, hv⟩
  choose start cycles hsimple hcycles using hcycles
  let rows := fun t => ofWalk data (cycles t).tail
  let cols := fun t => ofWalk data (L.walk t)
  have hrows (i s) : (rows i).vert s ∈ frontier data root far (lo + i.val) :=
    (hcycles i _).mp ((cycle_tail_support (cycles i) (hsimple i)).mp
      (vert_mem_support data (cycles i).tail s))
  have hhits (j : Fin N) := exists_strictMono_frontier_hits data hclass htwo root far lo a
    (L.walk j) (L.start_mem j) (L.finish_mem j)
  choose cp hcp hcp_mem using hhits
  have hrp (i : Fin a) (j : Fin N) : ∃ s, (rows i).vert s = (cols j).vert (cp j i) := by
    apply (exists_vert_iff data (cycles i).tail).mpr
    exact (cycle_tail_support (cycles i) (hsimple i)).mpr ((hcycles i _).mpr (hcp_mem j i))
  choose rp hrp using hrp
  apply exists_orderedMesh_of_paths rows cols ?_ ?_
    (fun i => vert_injective_of_isPath data (cycles i).tail (hsimple i).isPath_tail)
    (fun j => vert_injective_of_isPath data (L.walk j) (L.simple j)) rp
    (fun i j => cp j i) hrp hcp hN
  · intro i j hij s t heq
    have hd := distance_frontiers_disjoint data hclass htwo root far
      (i := lo + i.val) (j := lo + j.val) (fun h => hij (Fin.ext (by omega)))
    exact Set.disjoint_left.mp hd (hrows i s) (heq ▸ hrows j t)
  · intro i j hij s t heq
    exact L.disjoint i j hij ((cols i).vert s)
      (vert_mem_support data (L.walk i) s)
      (heq ▸ vert_mem_support data (L.walk j) t)

/-- Enough linkage columns for a by b ordered extraction. -/
def orderedLinkageSize (a b : ℕ) : ℕ := b ^ (2 ^ a) + 1

/-- The alternative includes the entire ambient cut, both connected shores,
the exposed-port bound, and the inverse boundary first-return orders. -/
theorem exists_orderedMesh_or_contour_bond (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo a b : ℕ)
    (ha : 2 ≤ a) (hd : lo + a ≤ (orbitFaceDualGraph data).dist root far) :
    Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b) ∨
      Nonempty (OrderedContourBond data root far lo (lo + a - 1)
        (3 * (orderedLinkageSize a b - 1))) := by
  rcases exists_linkage_or_ordered_bond data hclass htwo root far
    (i := lo) (j := lo + a - 1) (by omega) (by omega) (by omega)
    (orderedLinkageSize a b) with hL | hcut
  · obtain ⟨L⟩ := hL
    exact Or.inl (exists_orderedMesh_of_contour_linkage data hclass htwo root far
      lo a b _ hd L (Nat.lt_succ_self _))
  · obtain ⟨deleted, hfirst, hlast, hconn, hcomp, hedge, hport, hface, horder⟩ := hcut
    exact Or.inr ⟨⟨deleted, hfirst, hlast, hconn, hcomp, hedge, hport, hface, horder⟩⟩

end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
