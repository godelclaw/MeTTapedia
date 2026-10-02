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

/-- A finite metric ball in the original link geometry. Direction labels at
the same site are all included, as required by the link pseudometric. -/
def linkBall (r : ℝ) (l : Link d n) : Finset (Link d n) :=
  univ.filter (fun k ↦ dist l k ≤ r)

@[simp] theorem mem_linkBall {r : ℝ} {l k : Link d n} :
    k ∈ linkBall r l ↔ dist l k ≤ r := by simp [linkBall]

theorem linkBall_nonempty {r : ℝ} (hr : 0 ≤ r) (l : Link d n) :
    (linkBall r l).Nonempty := ⟨l, by simpa using hr⟩

/-- The exponential volume estimate gives an explicit finite ball bound,
with no dependence on the torus side length. -/
theorem card_linkBall_le (hd : 0 < d) (r : ℝ) (l : Link d n) :
    ((linkBall r l).card : ℝ) ≤ Real.exp r * exponentialVolumeBound d 1 := by
  calc
    _ = ∑ k ∈ linkBall r l, (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ linkBall r l, Real.exp r * Real.exp (-dist l k) := by
      apply sum_le_sum
      intro k hk
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith [mem_linkBall.mp hk])
    _ ≤ ∑ k : Link d n, Real.exp r * Real.exp (-dist l k) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ by positivity)
    _ = Real.exp r * ∑ k : Link d n, Real.exp (-dist l k) := (mul_sum _ _ _).symm
    _ ≤ Real.exp r * exponentialVolumeBound d 1 :=
      mul_le_mul_of_nonneg_left (by simpa using sum_exp_dist_le hd (by norm_num : (0 : ℝ) < 1) l)
        (Real.exp_pos _).le

theorem separation_linkBall {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (l m : Link d n) :
    dist l m - (r + s) ≤ polymerDist (linkBall r l) (linkBall s m) := by
  have hn := linkBall_nonempty hs m
  simp only [polymerDist, hn, ↓reduceDIte]
  apply le_inf'
  intro y hy
  apply (Metric.le_infDist (linkBall_nonempty hr l).to_set).mpr
  intro x hx
  have hx' := mem_linkBall.mp hx
  have hy' := mem_linkBall.mp hy
  have h₁ := dist_triangle l x m
  have h₂ := dist_triangle x y m
  rw [dist_comm y m] at h₂
  rw [dist_comm y x]
  linarith

theorem separation_linkBall_union {r : ℝ} (hr : 0 ≤ r) (l m k : Link d n) :
    min (dist l m) (dist l k) - 2 * r ≤
      polymerDist (linkBall r l) (linkBall r m ∪ linkBall r k) := by
  have hn : (linkBall r m ∪ linkBall r k).Nonempty :=
    (linkBall_nonempty hr m).mono subset_union_left
  simp only [polymerDist, hn, ↓reduceDIte]
  apply le_inf'
  intro y hy
  apply (Metric.le_infDist (linkBall_nonempty hr l).to_set).mpr
  intro x hx
  change min (dist l m) (dist l k) - 2 * r ≤ dist y x
  rcases mem_union.mp hy with hy | hy
  · have h := (separation_linkBall hr hr l m).trans
      ((polymerDist_le_infDist hy).trans (Metric.infDist_le_dist_of_mem hx))
    linarith [min_le_left (dist l m) (dist l k)]
  · have h := (separation_linkBall hr hr l k).trans
      ((polymerDist_le_infDist hy).trans (Metric.infDist_le_dist_of_mem hx))
    linarith [min_le_right (dist l m) (dist l k)]

def ballFamily (r : ℝ) (A : Finset (Link d n)) : Finset (Link d n) := A.biUnion (linkBall r)

theorem linkBall_subset_ballFamily (r : ℝ) {A : Finset (Link d n)} {l : Link d n} (hl : l ∈ A) :
    linkBall r l ⊆ ballFamily r A := by
  intro x hx
  exact mem_biUnion.mpr ⟨l, hl, hx⟩

theorem ballFamily_nonempty {r : ℝ} (hr : 0 ≤ r) {A : Finset (Link d n)} (hA : A.Nonempty) :
    (ballFamily r A).Nonempty := by
  obtain ⟨l, hl⟩ := hA
  exact (linkBall_nonempty hr l).mono (linkBall_subset_ballFamily r hl)

theorem card_ballFamily_le (hd : 0 < d) (r : ℝ) (A : Finset (Link d n)) :
    ((ballFamily r A).card : ℝ) ≤ A.card * (Real.exp r * exponentialVolumeBound d 1) := by
  have hc : ((ballFamily r A).card : ℝ) ≤ ∑ l ∈ A, ((linkBall r l).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  calc
    _ ≤ ∑ l ∈ A, ((linkBall r l).card : ℝ) := hc
    _ ≤ ∑ _l ∈ A, Real.exp r * exponentialVolumeBound d 1 :=
      sum_le_sum (fun l _ ↦ card_linkBall_le hd r l)
    _ = _ := by simp

theorem separation_ballFamily {r δ : ℝ} (hr : 0 ≤ r)
    {A B : Finset (Link d n)} (hA : A.Nonempty) (hB : B.Nonempty)
    (hδ : ∀ l ∈ A, ∀ m ∈ B, δ ≤ dist l m) :
    δ - 2*r ≤ polymerDist (ballFamily r A) (ballFamily r B) := by
  have hn := ballFamily_nonempty hr hB
  simp only [polymerDist, hn, ↓reduceDIte]
  apply le_inf'
  intro y hy
  apply (Metric.le_infDist (ballFamily_nonempty hr hA).to_set).mpr
  intro x hx
  obtain ⟨l, hl, hxl⟩ := mem_biUnion.mp hx
  obtain ⟨m, hm, hym⟩ := mem_biUnion.mp hy
  have h := (separation_linkBall hr hr l m).trans
    ((polymerDist_le_infDist hym).trans (Metric.infDist_le_dist_of_mem hxl))
  linarith [hδ l hl m hm]

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

/-- Singleton plaquette collars lie in the unit ball of the link metric. -/
theorem collar_singleton_subset_linkBall (l : Link d n) :
    collar {l} ⊆ linkBall 1 l := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := collar_radius hx
  simp only [mem_singleton] at ha
  subst a
  exact mem_linkBall.mpr (by simpa only [dist_comm] using hxa)

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

/-- A single collar remains separated from the union of two collars, with
the same two-unit loss as for two patches. -/
theorem separation_collar_union {S T U : Finset (Link d n)}
    (hS : (collar S).Nonempty) (hT : (collar T).Nonempty)
    (hU : (collar U).Nonempty) :
    min (polymerDist S T) (polymerDist S U) - 2 ≤
      polymerDist (collar S) (collar T ∪ collar U) := by
  have hTU : (collar T ∪ collar U).Nonempty := hT.mono subset_union_left
  simp only [polymerDist, hTU, ↓reduceDIte]
  apply le_inf'
  intro y hy
  apply (Metric.le_infDist hS.to_set).mpr
  intro x hx
  change min (polymerDist S T) (polymerDist S U) - 2 ≤ dist y x
  rcases mem_union.mp hy with hy | hy
  · have h := (separation_collar hS hT).trans (polymerDist_le_dist hx hy)
    linarith [min_le_left (polymerDist S T) (polymerDist S U)]
  · have h := (separation_collar hS hU).trans (polymerDist_le_dist hx hy)
    linarith [min_le_right (polymerDist S T) (polymerDist S U)]

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

/-- Every link direction in four dimensions has an incident plaquette. -/
theorem singleton_collar_nonempty (l : Link 4 n) :
    (collar ({l} : Finset (Link 4 n))).Nonempty := by
  rcases l with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst μ
    exact singleton_zero_collar_nonempty x
  · have hpos : (0 : Fin 4) < μ := Fin.pos_iff_ne_zero.mpr hμ
    let p : Plaquette 4 n := (x, ⟨(0, μ), hpos⟩)
    have hp : (x, μ) ∈ support p :=
      mem_image.mpr ⟨3, mem_univ _, by simp [p, linkAt]⟩
    refine ⟨(x, μ), mem_biUnion.mpr ⟨p, ?_, hp⟩⟩
    exact mem_incident.mpr ⟨(x, μ), mem_singleton_self _, hp⟩

@[simp] theorem polymerDist_singletons (l m : Link d n) :
    polymerDist ({l} : Finset (Link d n)) {m} = dist l m := by
  simp [polymerDist, Metric.infDist_singleton, dist_comm]

#print axioms card_collar_le
#print axioms collar_radius
#print axioms separation_collar
#print axioms disjoint_incident_of_separation

end Mettapedia.QuantumTheory.YangMills.WilsonPatchGeometry
