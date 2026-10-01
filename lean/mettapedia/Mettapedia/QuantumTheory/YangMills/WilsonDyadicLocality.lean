import Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
import Mettapedia.QuantumTheory.YangMills.WilsonPatchGeometry

/-!
# Geometric dependency sets for exact Wilson elimination

The interior components touched by a mark are entire mesh cells. Their
incident plaquettes can depend on retained links only in a collar of radius
`mesh + 1` around the original mark. These geometric statements supply the
support conditions for conditional factorization; they do not by themselves
assert locality of a statistical projection.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical
open Mettapedia.Combinatorics.PolymerGas
namespace Mettapedia.QuantumTheory.YangMills.WilsonDyadicLocality
open StrongCouplingCrossing WilsonDyadicGeometry WilsonPatchGeometry
variable {d n : ℕ}

/-- Circle projection can only shorten the distance of the chosen representatives. -/
theorem coordinate_dist_le (x y : ZMod (n + 3)) :
    dist (coordinateCircle n x) (coordinateCircle n y) ≤ |(x.val : ℝ) - y.val| := by
  rw [coordinateCircle_apply, coordinateCircle_apply, dist_eq_norm, ← AddCircle.coe_sub]
  exact (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (n + 3 : ℝ))
    (m := (x.val : ℝ) - y.val)).trans_eq (Real.norm_eq_abs _)

theorem abs_sub_le_of_div_eq {s a b : ℕ} (hs : 0 < s) (h : a / s = b / s) :
    |(a : ℝ) - b| ≤ s := by
  have ha := Nat.mod_add_div a s
  have hb := Nat.mod_add_div b s
  have hra := Nat.mod_lt a hs
  have hrb := Nat.mod_lt b hs
  rw [h] at ha
  have hab : a ≤ b + s := by omega
  have hba : b ≤ a + s := by omega
  have hab' : (a : ℝ) ≤ b + s := by exact_mod_cast hab
  have hba' : (b : ℝ) ≤ a + s := by exact_mod_cast hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A cell has bounded diameter in the actual periodic sup metric. -/
theorem same_cell_dist_le {s : ℕ} (hs : 0 < s) (l k : Link d n)
    (h : cell s l.1 = cell s k.1) : dist l k ≤ s := by
  rw [dist_link_eq]
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ s)).mpr
  intro i
  exact (coordinate_dist_le _ _).trans (abs_sub_le_of_div_eq hs (congrFun h i))

/-- All interior cells touched by an observable support. -/
def affectedInterior (s : ℕ) (S : Finset (Link d n)) : Finset (Link d n) :=
  univ.filter (fun l => ¬Retained s l ∧
    ∃ a ∈ S, ¬Retained s a ∧ cell s l.1 = cell s a.1)

/-- The retained source variables plus the retained variables in plaquettes
incident to the affected interior cells. -/
def dependencyBoundary (s : ℕ) (S : Finset (Link d n)) : Finset (Link d n) :=
  S.filter (Retained s) ∪ (collar (affectedInterior s S)).filter (Retained s)

theorem affectedInterior_closed (s : ℕ) (S : Finset (Link d n))
    (p : Plaquette d n) {l k : Link d n} (hl : l ∈ affectedInterior s S)
    (hlp : l ∈ support p) (hkp : k ∈ support p) (hk : ¬Retained s k) :
    k ∈ affectedInterior s S := by
  obtain ⟨_, hil, a, ha, hia, hcell⟩ := mem_filter.mp hl
  apply mem_filter.mpr
  refine ⟨mem_univ _, hk, a, ha, hia, ?_⟩
  exact (internal_support_same_cell s p hkp hlp hk hil).trans hcell

theorem source_covered (s : ℕ) (S : Finset (Link d n)) :
    S ⊆ dependencyBoundary s S ∪ affectedInterior s S := by
  intro l hl
  by_cases hr : Retained s l
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hl, hr⟩))
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hr, l, hl, hr, rfl⟩)

/-- All interaction variables adjoining an affected cell belong either to its
retained dependency boundary or to an affected interior cell. -/
theorem incident_support_covered (s : ℕ) (S : Finset (Link d n))
    (p : Plaquette d n) (hp : p ∈ incident (affectedInterior s S)) :
    support p ⊆ dependencyBoundary s S ∪ affectedInterior s S := by
  obtain ⟨l, hl, hlp⟩ := mem_incident.mp hp
  intro k hkp
  by_cases hr : Retained s k
  · exact mem_union_left _ (mem_union_right _
      (mem_filter.mpr ⟨mem_biUnion.mpr ⟨p, hp, hkp⟩, hr⟩))
  · exact mem_union_right _ (affectedInterior_closed s S p hl hlp hkp hr)

/-- The candidate dependency boundary lies within an explicit radius of the
original source, uniformly in the surrounding torus. -/
theorem dependencyBoundary_radius {s : ℕ} (hs : 0 < s) (S : Finset (Link d n))
    {l : Link d n} (hl : l ∈ dependencyBoundary s S) :
    ∃ a ∈ S, dist l a ≤ (s : ℝ) + 1 := by
  rcases mem_union.mp hl with hl | hl
  · exact ⟨l, (mem_filter.mp hl).1, by simp; positivity⟩
  · obtain ⟨j, hj, hdist⟩ := collar_radius (mem_filter.mp hl).1
    obtain ⟨_, _, a, ha, _, hcell⟩ := mem_filter.mp hj
    refine ⟨a, ha, (dist_triangle l j a).trans ?_⟩
    have hc := same_cell_dist_le hs j a hcell
    linarith

/-- A plaquette collar enlarged by one cell elimination fits into a ball
whose radius depends on the cell size, not on the surrounding volume. -/
theorem dependencyBoundary_collar_subset_ball {s : ℕ} (hs : 0 < s) (l : Link d n) :
    dependencyBoundary s (collar {l}) ⊆ linkBall ((s : ℝ) + 2) l := by
  intro k hk
  obtain ⟨a, ha, hka⟩ := dependencyBoundary_radius hs (collar {l}) hk
  obtain ⟨b, hb, hab⟩ := collar_radius ha
  have hbl : b = l := mem_singleton.mp hb
  subst b
  apply mem_linkBall.mpr
  rw [dist_comm]
  linarith [dist_triangle k a l]

theorem dependencyBoundary_collars_subset_balls {s : ℕ} (hs : 0 < s)
    (l m : Link d n) :
    dependencyBoundary s (collar {l} ∪ collar {m}) ⊆
      linkBall ((s : ℝ) + 2) l ∪ linkBall ((s : ℝ) + 2) m := by
  intro k hk
  obtain ⟨a, ha, hka⟩ := dependencyBoundary_radius hs (collar {l} ∪ collar {m}) hk
  have hnear (x : Link d n) (hx : a ∈ collar {x}) : k ∈ linkBall ((s : ℝ) + 2) x := by
    obtain ⟨b, hb, hab⟩ := collar_radius hx
    have hbx : b = x := mem_singleton.mp hb
    subst b
    apply mem_linkBall.mpr
    rw [dist_comm]
    linarith [dist_triangle k a x]
  exact (mem_union.mp ha).elim (fun h ↦ mem_union_left _ (hnear l h))
    (fun h ↦ mem_union_right _ (hnear m h))

#print axioms same_cell_dist_le
#print axioms affectedInterior_closed
#print axioms incident_support_covered
#print axioms dependencyBoundary_radius
end Mettapedia.QuantumTheory.YangMills.WilsonDyadicLocality
