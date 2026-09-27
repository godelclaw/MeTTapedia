import Mettapedia.GraphTheory.FourColor.FaceColourTransfer

/-!
# An order-independent edge budget for facial sweeps

Assign a facial addition the signed deficit three minus the number of
new edges. Along a complete source sweep, the sum of these deficits is
exactly the length of the initial face. Consequently every sweep contains
short additions: at least half the initial face length, rounded up.

Exchanging the order can move the short additions, but cannot eliminate
them. This is an obstruction to completing a construction solely with the
unconditional extension law for paths of at least three edges. It is not
an obstruction to choosing compatible colourings for short additions.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceSweepEdgeBudget

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree FaceRegionShelling
open FaceRegionSweep FaceRegionComplement
open Mettapedia.GSLT.Ultrainfinite

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

/-- The signed shortfall from three newly introduced edges per event. -/
def deficit : {S T : Region data} → Route Event S T → ℤ
  | _, _, .refl _ => 0
  | _, _, .cons e p => 3 - ((exposedEdges data e).card : ℤ) + deficit p

/-- Count actual additions introducing only one or two edges. -/
def shortCount : {S T : Region data} → Route Event S T → ℕ
  | _, _, .refl _ => 0
  | _, _, .cons e p => (if (exposedEdges data e).card < 3 then 1 else 0) + shortCount p

/-- Disjoint introduction of original edges makes the budget telescope. -/
theorem deficit_eq {S T : Region data} (p : Route Event S T) :
    deficit data p = 3 * (p.length : ℤ) +
      (edges data.toRotationSystem S.faces).card - (edges data.toRotationSystem T.faces).card := by
  induction p with
  | refl S => simp [deficit, Route.length]
  | @cons S R T e p ih =>
    have hcard : (edges data.toRotationSystem R.faces).card =
        (edges data.toRotationSystem S.faces).card + (exposedEdges data e).card := by
      rw [FaceColourTransfer.shores_union data e]
      exact Finset.card_union_of_disjoint (FaceColourTransfer.shores_disjoint data e)
    simp only [deficit, Route.length, Nat.cast_add, Nat.cast_one]
    rw [ih]
    have hc : ((edges data.toRotationSystem R.faces).card : ℤ) =
        (edges data.toRotationSystem S.faces).card + (exposedEdges data e).card := by
      exact_mod_cast hcard
    omega

/-- Changing any part of the face ordering preserves the signed deficit
between the same two actual regions. -/
theorem deficit_eq_of_same_endpoints {S T : Region data} (p q : Route Event S T) :
    deficit data p = deficit data q := by
  have hp := route_length p
  have hq := route_length q
  have hlen : p.length = q.length := by omega
  rw [deficit_eq data p, deficit_eq data q, hlen]

/-- Cubic incidence and the sphere Euler equation fix the total edge count. -/
theorem edges_eq_three_faces_sub_six
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem) :
    (Fintype.card G.edgeSet : ℤ) =
      3 * Fintype.card (OrbitFace data.toRotationSystem) - 6 := by
  have hv := data.toRotationSystem.card_darts_eq_three_times_card_vertices ambient.spherical.cubic
  have he := data.toRotationSystem.card_darts_eq_twice_card_edges
  have hvi : (Fintype.card data.toRotationSystem.D : ℤ) = 3 * Fintype.card V := by
    exact_mod_cast hv
  have hei : (Fintype.card data.toRotationSystem.D : ℤ) = 2 * Fintype.card G.edgeSet := by
    exact_mod_cast he
  linarith [ambient.spherical.euler]

/-- Every complete facial sweep has the same positive signed deficit,
regardless of its ordering and intermediate boundary widths. -/
theorem sweep_deficit
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (first outer : OrbitFace data.toRotationSystem)
    (p : Route Event (single data ambient first) (coSingle data ambient outer)) :
    deficit data p = (orbitFaceBoundary data.toRotationSystem first).card := by
  have hlen := sweep_length data ambient first outer p
  have hleni : (p.length : ℤ) + 2 = Fintype.card (OrbitFace data.toRotationSystem) := by
    exact_mod_cast hlen
  have hstart : edges data.toRotationSystem (single data ambient first).faces =
      orbitFaceBoundary data.toRotationSystem first := by
    simp only [single, edges, Finset.singleton_biUnion]
  rw [deficit_eq data p, hstart, coSingle_retains_all_edges data ambient outer,
    Finset.card_univ, edges_eq_three_faces_sub_six data ambient, ← hleni]
  ring

/-- Every short event contributes at most two to the deficit. Longer
events contribute zero or a negative amount. -/
theorem deficit_le_twice_shortCount
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {S T : Region data} (p : Route Event S T) :
    deficit data p ≤ 2 * (shortCount data p : ℤ) := by
  induction p with
  | refl S => simp [deficit, shortCount]
  | @cons S R T e p ih =>
    have hpos : 0 < (exposedEdges data e).card :=
      Finset.card_pos.mpr (exposed_nonempty data ambient e)
    simp only [deficit, shortCount]
    split_ifs with h
    · push_cast
      omega
    · push_cast
      omega

/-- The unavoidable short steps are quantified by the initial face
length. In particular a pentagonal start requires at least three. -/
theorem sweep_shortCount_bound
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (first outer : OrbitFace data.toRotationSystem)
    (p : Route Event (single data ambient first) (coSingle data ambient outer)) :
    (orbitFaceBoundary data.toRotationSystem first).card ≤ 2 * shortCount data p := by
  have h := deficit_le_twice_shortCount data ambient p
  rw [sweep_deficit data ambient first outer p] at h
  exact_mod_cast h

/-- No complete facial sweep can use only the unconditional
three-or-more-edge extension rule. -/
theorem sweep_has_short_step
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (first outer : OrbitFace data.toRotationSystem)
    (p : Route Event (single data ambient first) (coSingle data ambient outer)) :
    0 < shortCount data p := by
  obtain ⟨d, hd⟩ := exists_dartOrbitFace_eq data.toRotationSystem first
  have hpos : 0 < (orbitFaceBoundary data.toRotationSystem first).card := by
    apply Finset.card_pos.mpr
    exact ⟨data.toRotationSystem.edgeOf d,
      hd ▸ GoertzelV24FaceDualConnectedness.edgeOf_mem_orbitFaceBoundary_dartOrbitFace
        data.toRotationSystem d⟩
  have h := sweep_shortCount_bound data ambient first outer p
  omega

/-- Three short additions cannot be removed from a complete sweep
starting at a pentagon, even by changing its entire face order. -/
theorem pentagonal_sweep_has_three_short_steps
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (first outer : OrbitFace data.toRotationSystem)
    (hfirst : (orbitFaceBoundary data.toRotationSystem first).card = 5)
    (p : Route Event (single data ambient first) (coSingle data ambient outer)) :
    3 ≤ shortCount data p := by
  have h := sweep_shortCount_bound data ambient first outer p
  omega

end
end Mettapedia.GraphTheory.FourColor.FaceSweepEdgeBudget
