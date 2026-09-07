import Mettapedia.GraphTheory.FourColor.ContourPathCrossing
import Mettapedia.GraphTheory.FourColor.RotationWalkMeshPath

/-!
# First encounters with nested distance contours are strictly ordered

Apply the full-ambient crossing theorem to the prefix ending at the first
encounter with a later contour. It already meets every earlier contour.
Disjointness of the complete distance frontiers makes the resulting order
strict. No prohibition on excursions or repeated row encounters is needed.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open SphericalDistanceContours FaceDistanceFrontiers

namespace RotationWalkMeshPath

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem vert_injective_of_isPath (data : Data G) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) : Function.Injective (ofWalk data p).vert := by
  intro i j hij
  exact Fin.ext (hp.getVert_injOn (by
    have h : i.val < p.length + 1 := i.isLt
    exact Nat.le_of_lt_succ h) (by
    have h : j.val < p.length + 1 := j.isLt
    exact Nat.le_of_lt_succ h) hij)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Removing the first edge of a simple closed contour gives a simple path
with the same vertex set, since the initial vertex remains at the end. -/
theorem cycle_tail_support {u v : V} (p : G.Walk u u) (hp : p.IsCycle) :
    v ∈ p.tail.support ↔ v ∈ p.support := by
  rw [← p.cons_support_tail hp.not_nil, List.mem_cons]
  constructor
  · exact Or.inr
  · rintro (rfl | h)
    · exact p.tail.end_mem_support
    · exact h

end RotationWalkMeshPath

namespace SphericalContourSeparators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The crossing positions are constructed from the ambient walk itself. -/
theorem exists_strictMono_frontier_hits (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (lo a : ℕ)
    {u v : V} (p : G.Walk u v)
    (hu : u ∈ frontier data root far lo)
    (hv : v ∈ frontier data root far (lo + a - 1)) :
    ∃ hit : Fin a → Fin (p.length + 1), StrictMono hit ∧
      ∀ i, p.getVert (hit i).val ∈ frontier data root far (lo + i.val) := by
  classical
  have exists_hit (i : Fin a) : ∃ n, n ≤ p.length ∧
      p.getVert n ∈ frontier data root far (lo + i.val) := by
    obtain ⟨w, hw, hf⟩ := walk_meets_intermediate data hclass htwo root far
      (d := lo + i.val) (by omega) (by omega) hu hv p
    obtain ⟨n, hn, hl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    exact ⟨n, hl, hn ▸ hf⟩
  let hit (i : Fin a) : Fin (p.length + 1) :=
    ⟨Nat.find (exists_hit i), by have := (Nat.find_spec (exists_hit i)).1; omega⟩
  have hhit (i) : p.getVert (hit i).val ∈ frontier data root far (lo + i.val) :=
    (Nat.find_spec (exists_hit i)).2
  refine ⟨hit, ?_, hhit⟩
  intro i j hij
  obtain ⟨w, hw, hf⟩ := walk_meets_intermediate data hclass htwo root far
    (d := lo + i.val) (j := lo + j.val) (by omega) (by exact Nat.add_le_add_left hij.le lo)
    hu (hhit j) (p.take (hit j).val)
  obtain ⟨n, hn, hl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  have hnle : n ≤ (hit j).val := by
    have := p.take_length (hit j).val
    omega
  rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hnle] at hn
  have hi_le : (hit i).val ≤ n := Nat.find_min' (exists_hit i)
    ⟨by have := (hit j).isLt; omega, hn ▸ hf⟩
  have hne : hit i ≠ hit j := by
    intro heq
    have hd := distance_frontiers_disjoint data hclass htwo root far
      (i := lo + i.val) (j := lo + j.val) (by have := hij; simp only [Fin.lt_def] at this; omega)
    exact Set.disjoint_left.mp hd (hhit i) (heq ▸ hhit j)
  exact lt_of_le_of_ne (by exact hi_le.trans hnle) hne

end SphericalContourSeparators
end Mettapedia.GraphTheory.FourColor
