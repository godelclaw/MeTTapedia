import Mettapedia.QuantumTheory.YangMills.CalibrationSeparation

/-!
# The geometric collar of a Wilson boundary change

Changing link variables in a patch affects only its incident plaquettes.
The union of their four-link supports is a radius-one collar, with cardinality
at most `16 d²` times the patch size. Two such collars lose at most two units
of separation. All constants are independent of the torus volume.
-/
set_option autoImplicit false
noncomputable section
open Finset
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.WilsonPatchGeometry
open StrongCouplingCrossing
variable {d n : ℕ}

/-- Exactly the plaquettes that touch the changed links. -/
def incident (S : Finset (Link d n)) : Finset (Plaquette d n) :=
  univ.filter (fun p => ¬ Disjoint (support p) S)

/-- All variables that can occur in the change of the Wilson action. -/
def collar (S : Finset (Link d n)) : Finset (Link d n) :=
  (incident S).biUnion support

theorem mem_incident {S : Finset (Link d n)} {p : Plaquette d n} :
    p ∈ incident S ↔ ∃ l ∈ S, l ∈ support p := by
  simp only [incident, mem_filter, mem_univ, true_and, not_disjoint_iff]
  constructor <;> rintro ⟨l, ha, hb⟩ <;> exact ⟨l, hb, ha⟩

theorem card_incident_le (S : Finset (Link d n)) :
    (incident S).card ≤ S.card * (4 * (d * d)) := by
  have hsub : incident S ⊆ S.biUnion
      (fun l => univ.filter (fun p : Plaquette d n => l ∈ support p)) := by
    intro p hp
    obtain ⟨l, hl, hlp⟩ := mem_incident.mp hp
    exact mem_biUnion.mpr ⟨l, hl, mem_filter.mpr ⟨mem_univ _, hlp⟩⟩
  exact (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _
    (fun l _ => StrongCouplingCrossing.card_incident_le d n l))

theorem card_collar_le (S : Finset (Link d n)) :
    (collar S).card ≤ S.card * (16 * (d * d)) := by
  calc
    _ ≤ (incident S).card * 4 := card_biUnion_le_card_mul _ _ _ (fun p _ => card_support_le p)
    _ ≤ (S.card * (4 * (d * d))) * 4 := Nat.mul_le_mul_right 4 (card_incident_le S)
    _ = _ := by ring

/-- Each variable in the response has a witness in the original patch within
one unit of the same circle sup metric used in the crossing theorem. -/
theorem collar_radius {S : Finset (Link d n)} {x : Link d n} (hx : x ∈ collar S) :
    ∃ a ∈ S, dist x a ≤ 1 := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
  obtain ⟨a, ha, hap⟩ := mem_incident.mp hp
  exact ⟨a, ha, (dist_le_polymerDiam hxp hap).trans (diam_support_le p)⟩

theorem polymerDist_le_dist {S T : Finset (Link d n)} {a b : Link d n}
    (ha : a ∈ S) (hb : b ∈ T) : polymerDist S T ≤ dist b a :=
  (polymerDist_le_infDist hb).trans (Metric.infDist_le_dist_of_mem ha)

/-- Separation survives the actual plaquette collar, at a cost of two lattice
units. The nonempty collar hypotheses avoid the empty-set distance convention. -/
theorem separation_collar {S T : Finset (Link d n)}
    (hS : (collar S).Nonempty) (hT : (collar T).Nonempty) :
    polymerDist S T - 2 ≤ polymerDist (collar S) (collar T) := by
  simp only [polymerDist, hT, ↓reduceDIte]
  apply le_inf'
  intro y hy
  apply (Metric.le_infDist hS.to_set).mpr
  intro x hx
  change polymerDist S T - 2 ≤ dist y x
  obtain ⟨a, ha, hxa⟩ := collar_radius hx
  obtain ⟨b, hb, hyb⟩ := collar_radius hy
  have hdist := polymerDist_le_dist ha hb
  have htriangle := dist_triangle b y a
  have htriangle' := dist_triangle y x a
  rw [dist_comm b y] at htriangle
  linarith

/-- Sufficient geometric separation prevents a plaquette from meeting both
changed patches; hence there is no elementary mixed boundary factor. -/
theorem disjoint_incident_of_separation {S T : Finset (Link d n)}
    (hsep : 1 < polymerDist S T) : Disjoint (incident S) (incident T) := by
  apply disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, ha, hap⟩ := mem_incident.mp hp
  obtain ⟨b, hb, hbp⟩ := mem_incident.mp hq
  have := (polymerDist_le_dist ha hb).trans
    ((dist_le_polymerDiam hbp hap).trans (diam_support_le p))
  linarith

/-- In four dimensions each direction-zero link belongs to its `(0,1)`
plaquette, so its collar is nonempty at every volume. -/
theorem singleton_zero_collar_nonempty (x : Site 4 n) :
    (collar ({(x, (0 : Fin 4))} : Finset (Link 4 n))).Nonempty := by
  let p : Plaquette 4 n := (x, ⟨(0, 1), by decide⟩)
  have hp : (x, (0 : Fin 4)) ∈ support p :=
    mem_image.mpr ⟨0, mem_univ _, by simp [p, linkAt]⟩
  refine ⟨(x, 0), mem_biUnion.mpr ⟨p, ?_, hp⟩⟩
  exact mem_incident.mpr ⟨(x, 0), mem_singleton_self _, hp⟩

#print axioms card_collar_le
#print axioms collar_radius
#print axioms separation_collar
#print axioms disjoint_incident_of_separation

end Mettapedia.QuantumTheory.YangMills.WilsonPatchGeometry
