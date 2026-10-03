import Mettapedia.Combinatorics.PolymerGas.PlaquetteSmallness
import Mettapedia.QuantumTheory.YangMills.CrossingInput
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Strong-coupling crossing for finite torus plaquette measures

Links of the torus of side `n + 3` carry independent reference variables. A
measurable four-link potential between zero and two defines the Wilson-type
plaquette density. Its connected expansion satisfies the crossing input below
an explicit positive coupling threshold depending only on the dimension.
The resulting exponential clustering estimate is uniform in the torus volume.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

/-- Torus vertices, with side length at least three. -/
abbrev Site (d n : ℕ) := Fin d → ZMod (n + 3)

/-- Positively oriented links, indexed by their base point and direction. -/
abbrev Link (d n : ℕ) := Site d n × Fin d

/-- The two distinct, increasingly ordered directions of a plaquette. -/
abbrev Plane (d : ℕ) := {a : Fin d × Fin d // a.1 < a.2}

/-- A plaquette is its base point together with its ordered pair of directions. -/
abbrev Plaquette (d n : ℕ) := Site d n × Plane d

/-- The displacement by one unit in a coordinate direction. -/
def step {d n : ℕ} (μ : Fin d) : Site d n := fun i => if i = μ then 1 else 0

/-- The four positive links in boundary order. A gauge-theory potential applies
inverses to the third and fourth link variables. -/
def linkAt {d n : ℕ} (p : Plaquette d n) : Fin 4 → Link d n :=
  ![(p.1, p.2.1.1), (p.1 + step p.2.1.1, p.2.1.2),
    (p.1 + step p.2.1.2, p.2.1.1), (p.1, p.2.1.2)]

/-- The positively oriented group plaquette product in the same four-link
order as `linkAt`. -/
def holonomy {E : Type*} [Group E] (v : Fin 4 → E) : E :=
  v 0 * v 1 * (v 2)⁻¹ * (v 3)⁻¹

/-- The support of one plaquette. -/
def support {d n : ℕ} (p : Plaquette d n) : Finset (Link d n) := univ.image (linkAt p)

theorem support_nonempty {d n : ℕ} (p : Plaquette d n) : (support p).Nonempty :=
  ⟨linkAt p 0, mem_image.mpr ⟨0, mem_univ _, rfl⟩⟩

theorem card_support_le {d n : ℕ} (p : Plaquette d n) : (support p).card ≤ 4 := by
  simpa [support] using (card_image_le (s := (univ : Finset (Fin 4))) (f := linkAt p))

/-- A positive plaquette edge has no displacement in its own direction. -/
theorem linkAt_parallel_coordinate {d n : ℕ} (p : Plaquette d n) (i : Fin 4) :
    (linkAt p i).1 (linkAt p i).2 = p.1 (linkAt p i).2 := by
  have hμν : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have hνμ := hμν.symm
  fin_cases i <;> simp [linkAt, step, hμν, hνμ]

theorem support_parallel_coordinate {d n : ℕ} (p : Plaquette d n) (l : Link d n) (hl : l ∈ support p) :
    l.1 l.2 = p.1 l.2 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hl
  exact linkAt_parallel_coordinate p i

theorem linkAt_eq_first_iff {d n : ℕ} (p : Plaquette d n) (i : Fin 4) :
    linkAt p i = linkAt p 0 ↔ i = 0 := by
  have hμν : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have hνμ := hμν.symm
  haveI : Fact (1 < n + 3) := ⟨by omega⟩
  fin_cases i
  · simp
  · simp [linkAt, hνμ]
  · constructor
    · intro h
      have hh := congrArg (fun l : Link d n ↦ l.1 p.2.1.2) h
      have : (1 : ZMod (n + 3)) = 0 := by simpa [linkAt, step] using hh
      exact one_ne_zero this |>.elim
    · simp
  · simp [linkAt, hνμ]

/-- All four links of an elementary plaquette are distinct on these tori. -/
theorem linkAt_injective {d n : ℕ} (p : Plaquette d n) : Function.Injective (linkAt p) := by
  have hμν : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have hνμ := hμν.symm
  haveI : Fact (1 < n+3) := ⟨by omega⟩
  have hstep (μ : Fin d) : (step μ : Site d n) ≠ 0 := by
    intro h
    have hh := congrFun h μ
    simpa [step] using hh
  intro i j hij
  have hμ := congrArg (fun l : Link d n => l.1 p.2.1.1) hij
  have hν := congrArg (fun l : Link d n => l.1 p.2.1.2) hij
  have hdir := congrArg Prod.snd hij
  fin_cases i <;> fin_cases j <;> simp_all [linkAt, step]


/-- Embed a cyclic coordinate into the additive circle with the same period. -/
def coordinateCircle (n : ℕ) : ZMod (n + 3) →+ AddCircle (n + 3 : ℝ) :=
  ZMod.lift (n + 3)
    ⟨AddMonoidHom.mk' (fun j : ℤ => ((j : ℝ) : AddCircle (n + 3 : ℝ)))
      (by intro a b; simp), by
        simp only [AddMonoidHom.mk'_apply, Nat.cast_add, Int.cast_add, Int.cast_natCast,
          Int.cast_ofNat, Nat.cast_ofNat]
        exact AddCircle.coe_period _⟩

@[simp] theorem coordinateCircle_intCast (n : ℕ) (j : ℤ) :
    coordinateCircle n (j : ZMod (n + 3)) = ((j : ℝ) : AddCircle (n + 3 : ℝ)) := by
  simp [coordinateCircle]

@[simp] theorem coordinateCircle_one (n : ℕ) :
    coordinateCircle n 1 = ((1 : ℝ) : AddCircle (n + 3 : ℝ)) := by
  simpa using coordinateCircle_intCast n 1

theorem coordinateCircle_apply (n : ℕ) (z : ZMod (n + 3)) :
    coordinateCircle n z = ((z.val : ℝ) : AddCircle (n + 3 : ℝ)) := by
  have h := coordinateCircle_intCast n (z.val : ℤ)
  simpa using h

/-- The circle distance is the absolute value of the centered integer
representative, including the half-period endpoint on even tori. -/
theorem norm_coordinateCircle_eq (n : ℕ) (z : ZMod (n + 3)) :
    ‖coordinateCircle n z‖ = (z.valMinAbs.natAbs : ℝ) := by
  conv_lhs => rw [← ZMod.coe_valMinAbs z, coordinateCircle_intCast]
  have h := z.valMinAbs_mem_Ioc
  have hlo : -(n + 3 : ℝ) < (z.valMinAbs : ℝ) * 2 := by exact_mod_cast h.1
  have hhi : (z.valMinAbs : ℝ) * 2 ≤ n + 3 := by exact_mod_cast h.2
  have hn : ‖((z.valMinAbs : ℝ) : AddCircle (n + 3 : ℝ))‖ = |(z.valMinAbs : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (n + 3 : ℝ) (by positivity)).mpr
    rw [abs_of_pos (by positivity : (0 : ℝ) < n + 3)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hn

/-- A cyclic coordinate contributes no more than the full integer geometric
series. The constant is independent of the period and of the base point. -/
theorem sum_exp_coordinate_le (n : ℕ) {a : ℝ} (ha : 0 < a)
    (x : ZMod (n + 3)) :
    ∑ z : ZMod (n + 3), Real.exp (-a * ‖coordinateCircle n (z - x)‖) ≤
      2 * (1 - Real.exp (-a))⁻¹ := by
  let f : ℤ → ℝ := fun j ↦ Real.exp (-a * (j.natAbs : ℝ))
  have hN : Summable (fun k : ℕ ↦ Real.exp (-a * (k : ℝ))) := by
    simpa only [mul_comm] using
      (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ha))
  have hp : Summable (fun k : ℕ ↦ f (k : ℤ)) := by simpa [f] using hN
  have hm : Summable (fun k : ℕ ↦ f (-(k : ℤ))) := by simpa [f] using hN
  have hf : Summable f := hp.of_nat_of_neg hm
  have hg : ∑' k : ℕ, Real.exp (-a * (k : ℝ)) = (1 - Real.exp (-a))⁻¹ := by
    simp_rw [mul_comm (-a), Real.exp_nat_mul]
    apply tsum_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have ht : ∑' j : ℤ, f j ≤ 2 * (1 - Real.exp (-a))⁻¹ := by
    rw [hp.tsum_of_nat_of_neg hm]
    simp only [f, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_zero, Nat.cast_zero,
      mul_zero, Real.exp_zero, hg]
    linarith
  have hs : ∑ z : ZMod (n + 3), f z.valMinAbs ≤ ∑' j : ℤ, f j := by
    rw [← Finset.sum_image (fun _ _ _ _ h ↦ ZMod.injective_valMinAbs h)]
    exact hf.sum_le_tsum _ (fun _ _ ↦ (Real.exp_pos _).le)
  have he := (Equiv.subRight x).sum_comp
    (fun z : ZMod (n + 3) ↦ Real.exp (-a * ‖coordinateCircle n z‖))
  change (∑ z : ZMod (n + 3), Real.exp (-a * ‖coordinateCircle n (z - x)‖)) = _ at he
  rw [he]
  simpa only [f, norm_coordinateCircle_eq] using hs.trans ht

/-- The circle embedding retains all cyclic coordinates. -/
theorem coordinateCircle_injective (n : ℕ) : Function.Injective (coordinateCircle n) := by
  have : Fact (0 < (n + 3 : ℝ)) := ⟨by positivity⟩
  intro a b h
  rw [coordinateCircle_apply, coordinateCircle_apply] at h
  have ha : (a.val : ℝ) ∈ Set.Ico 0 (0 + (n + 3 : ℝ)) := by
    constructor
    · positivity
    · simp only [zero_add]
      exact_mod_cast a.val_lt
  have hb : (b.val : ℝ) ∈ Set.Ico 0 (0 + (n + 3 : ℝ)) := by
    constructor
    · positivity
    · simp only [zero_add]
      exact_mod_cast b.val_lt
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico ha hb).mp h
  apply ZMod.val_injective
  exact_mod_cast heq

/-- Place a link at its base point in the product of circles. -/
def position {d n : ℕ} (l : Link d n) : Fin d → AddCircle (n + 3 : ℝ) :=
  fun i => coordinateCircle n (l.1 i)

/-- Links at the same base point have distance zero; positions use the sup metric. -/
instance linkPseudoMetricSpace (d n : ℕ) : PseudoMetricSpace (Link d n) :=
  PseudoMetricSpace.induced position inferInstance

@[simp] theorem dist_link_eq {d n : ℕ} (l m : Link d n) :
    dist l m = dist (position l) (position m) := rfl

/-- The sum of the coordinate distances is at most dimension times the sup
distance used by the crossing input. -/
theorem sum_coordinate_norm_le {d n : ℕ} (l m : Link d n) :
    ∑ i, ‖coordinateCircle n (m.1 i - l.1 i)‖ ≤ (d : ℝ) * dist l m := by
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin d)))
    (fun i _ ↦ dist_le_pi_dist (position m) (position l) i)
  rw [dist_link_eq, dist_comm (position l) (position m)]
  conv_lhs at h => simp only [position, dist_eq_norm, ← map_sub]
  simpa only [position, ← map_sub, dist_eq_norm, Finset.sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

/-- An explicit exponential-volume constant for the circle sup metric. -/
def exponentialVolumeBound (d : ℕ) (a : ℝ) : ℝ :=
  (d : ℝ) * (2 * (1 - Real.exp (-(a / d)))⁻¹) ^ d

/-- Exponentially weighted link counts are uniformly bounded over all torus
side lengths. Directions at the same base point retain their multiplicity. -/
theorem sum_exp_dist_le {d n : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a)
    (l : Link d n) :
    ∑ m : Link d n, Real.exp (-a * dist l m) ≤ exponentialVolumeBound d a := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have had : 0 < a / (d : ℝ) := div_pos ha hd'
  have hpoint (m : Link d n) : Real.exp (-a * dist l m) ≤
      ∏ i, Real.exp (-(a / d) * ‖coordinateCircle n (m.1 i - l.1 i)‖) := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hmean : (∑ i, ‖coordinateCircle n (m.1 i - l.1 i)‖) / d ≤ dist l m :=
      (div_le_iff₀ hd').mpr (by simpa only [mul_comm] using sum_coordinate_norm_le l m)
    have h := mul_le_mul_of_nonpos_left hmean (neg_nonpos.mpr ha.le)
    refine h.trans_eq ?_
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply (Finset.sum_le_sum (fun m _ ↦ hpoint m)).trans
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun i z ↦
    Real.exp (-(a / d) * ‖coordinateCircle n (z - l.1 i)‖))]
  apply mul_le_mul_of_nonneg_left _ hd'.le
  change (∏ i : Fin d, ∑ z : ZMod (n + 3),
    Real.exp (-(a / d) * ‖coordinateCircle n (z - l.1 i)‖)) ≤
      (2 * (1 - Real.exp (-(a / d)))⁻¹) ^ d
  have hc : (2 * (1 - Real.exp (-(a / d)))⁻¹) ^ d =
      ∏ _i : Fin d, (2 * (1 - Real.exp (-(a / d)))⁻¹) := by simp
  rw [hc]
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)
  · intro i _
    exact sum_exp_coordinate_le n had (l.1 i)

/-- The only zero-distance links are those sharing their base point. -/
theorem dist_link_eq_zero_iff {d n : ℕ} (l m : Link d n) :
    dist l m = 0 ↔ l.1 = m.1 := by
  rw [dist_link_eq, dist_eq_zero]
  constructor
  · intro h
    funext i
    exact coordinateCircle_injective n (congrFun h i)
  · intro h
    exact congrArg (fun x : Site d n => fun i => coordinateCircle n (x i)) h

theorem norm_coordinateCircle_one_le (n : ℕ) : ‖coordinateCircle n 1‖ ≤ 1 := by
  rw [coordinateCircle_one]
  simpa using (QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (n + 3 : ℝ)) (m := (1 : ℝ)))

theorem linkAt_coordinate {d n : ℕ} (p : Plaquette d n) (i : Fin 4) (j : Fin d) :
    (linkAt p i).1 j = p.1 j ∨ (linkAt p i).1 j = p.1 j + 1 := by
  fin_cases i
  · simp [linkAt]
  · by_cases hj : j = p.2.1.1 <;> simp [linkAt, step, hj]
  · by_cases hj : j = p.2.1.2 <;> simp [linkAt, step, hj]
  · simp [linkAt]

theorem dist_coordinateCircle_le_one {n : ℕ} {x a b : ZMod (n + 3)}
    (ha : a = x ∨ a = x + 1) (hb : b = x ∨ b = x + 1) :
    dist (coordinateCircle n a) (coordinateCircle n b) ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp
  · simpa [map_add, dist_eq_norm, sub_add_eq_sub_sub] using norm_coordinateCircle_one_le n
  · simpa [map_add, dist_eq_norm] using norm_coordinateCircle_one_le n
  · simp

/-- Every plaquette support has diameter at most one, independently of volume. -/
theorem diam_support_le {d n : ℕ} (p : Plaquette d n) : polymerDiam (support p) ≤ 1 := by
  apply Metric.diam_le_of_forall_dist_le (by norm_num)
  intro l hl m hm
  obtain ⟨i, _, rfl⟩ := mem_image.mp hl
  obtain ⟨j, _, rfl⟩ := mem_image.mp hm
  rw [dist_link_eq]
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro k
  exact dist_coordinateCircle_le_one (linkAt_coordinate p i k) (linkAt_coordinate p j k)

/-- For fixed directions and a fixed boundary position, the link determines
the base point of a plaquette. -/
theorem linkAt_base_injective {d n : ℕ} (a : Plane d) (i : Fin 4) :
    Function.Injective (fun x : Site d n => linkAt (x, a) i) := by
  fin_cases i <;> intro x y h <;>
    simpa [linkAt] using congrArg Prod.fst h

theorem plaquette_eq_of_plane_linkAt_eq {d n : ℕ} {p q : Plaquette d n} {i : Fin 4}
    (ha : p.2 = q.2) (hl : linkAt p i = linkAt q i) : p = q := by
  rcases p with ⟨x, a⟩
  rcases q with ⟨y, b⟩
  change a = b at ha
  subst b
  exact Prod.ext (linkAt_base_injective a i hl) rfl

/-- A fixed boundary position contributes at most `d²` plaquettes through a link. -/
theorem card_linkAt_fiber_le {d n : ℕ} (l : Link d n) (i : Fin 4) :
    ((univ : Finset (Plaquette d n)).filter (fun p => linkAt p i = l)).card ≤ d * d := by
  have h := card_le_card_of_injOn (s := univ.filter (fun p : Plaquette d n => linkAt p i = l))
    (t := (univ : Finset (Fin d × Fin d))) (fun p => p.2.1)
    (fun _ _ => mem_univ _) (fun p hp q hq heq =>
      plaquette_eq_of_plane_linkAt_eq (Subtype.ext heq)
        ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm))
  simpa using h

/-- A volume-independent incidence bound. -/
theorem card_incident_le (d n : ℕ) (l : Link d n) :
    ((univ : Finset (Plaquette d n)).filter (fun p => l ∈ support p)).card ≤ 4 * (d * d) := by
  have hsub : (univ.filter (fun p : Plaquette d n => l ∈ support p)) ⊆
      (univ : Finset (Fin 4)).biUnion
        (fun i => univ.filter (fun p : Plaquette d n => linkAt p i = l)) := by
    intro p hp
    obtain ⟨i, _, hi⟩ := mem_image.mp (mem_filter.mp hp).2
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  refine (card_le_card hsub).trans ?_
  simpa using card_biUnion_le_card_mul (univ : Finset (Fin 4))
    (fun i => univ.filter (fun p : Plaquette d n => linkAt p i = l)) (d * d)
    (fun i _ => card_linkAt_fiber_le l i)

open scoped Classical in
/-- The plaquette overlap graph has degree at most `16 d²`, uniformly in volume. -/
theorem degree_plaquetteGraph_le (d n : ℕ) (p : Plaquette d n) :
    (plaquetteGraph (support (d := d) (n := n))).degree p ≤ 16 * (d * d) := by
  have hsub : (plaquetteGraph (support (d := d) (n := n))).neighborFinset p ⊆
      (support p).biUnion (fun l => univ.filter (fun q : Plaquette d n => l ∈ support q)) := by
    intro q hq
    have hq' := ((plaquetteGraph (support (d := d) (n := n))).mem_neighborFinset p q).mp hq
    obtain ⟨l, hlp, hlq⟩ := not_disjoint_iff.mp hq'.2
    exact mem_biUnion.mpr ⟨l, hlp, mem_filter.mpr ⟨mem_univ _, hlq⟩⟩
  calc
    _ ≤ ((support p).biUnion
        (fun l => univ.filter (fun q : Plaquette d n => l ∈ support q))).card := card_le_card hsub
    _ ≤ (support p).card * (4 * (d * d)) :=
      card_biUnion_le_card_mul _ _ _ (fun l _ => card_incident_le d n l)
    _ ≤ 4 * (4 * (d * d)) := Nat.mul_le_mul_right _ (card_support_le p)
    _ = _ := by omega

section Potential

variable {E : Type*} [MeasurableSpace E]

/-- Evaluate the four-link potential in boundary order. -/
def potential {d n : ℕ} (φ : (Fin 4 → E) → ℝ) (p : Plaquette d n)
    (ω : Link d n → E) : ℝ := φ (fun i => ω (linkAt p i))

/-- The local perturbation relative to the product reference measure. -/
def perturbation {d n : ℕ} (φ : (Fin 4 → E) → ℝ) (β : ℝ) (p : Plaquette d n)
    (ω : Link d n → E) : ℂ := (Real.exp (-β * potential φ p ω) : ℂ) - 1

/-- The finite Wilson-type Boltzmann density. -/
def wilsonDensity {d n : ℕ} (φ : (Fin 4 → E) → ℝ) (β : ℝ) (ω : Link d n → E) : ℂ :=
  ∏ p : Plaquette d n, (Real.exp (-β * potential φ p ω) : ℂ)

/-- Connected plaquette activities as functions of their link variables. -/
def activity (d : ℕ) (base : E) (φ : (Fin 4 → E) → ℝ) (β : ℝ)
    (n : ℕ) (S : Finset (Link d n)) : (S → E) → ℂ :=
  plaquetteActivity support base (perturbation φ β) S

omit [MeasurableSpace E] in
theorem perturbation_local {d n : ℕ} (φ : (Fin 4 → E) → ℝ) (β : ℝ) :
    PlaquetteLocal (support (d := d) (n := n)) (perturbation φ β) := by
  intro p ω ω' h
  have hp : potential φ p ω = potential φ p ω' := by
    apply congrArg φ
    funext i
    exact h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  simp only [perturbation, hp]

theorem measurable_potential {d n : ℕ} {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (p : Plaquette d n) : Measurable (potential φ p) :=
  hφ.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)

theorem measurable_perturbation {d n : ℕ} {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (β : ℝ) (p : Plaquette d n) : Measurable (perturbation φ β p) := by
  exact (Complex.measurable_ofReal.comp
    ((measurable_const.mul (measurable_potential hφ p)).exp)).sub measurable_const

omit [MeasurableSpace E] in
/-- The perturbation is bounded by twice the coupling for a potential in `[0,2]`. -/
theorem norm_perturbation_le {d n : ℕ} {φ : (Fin 4 → E) → ℝ}
    (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2) {β : ℝ} (hβ : 0 ≤ β)
    (p : Plaquette d n) (ω : Link d n → E) : ‖perturbation φ β p ω‖ ≤ 2 * β := by
  have hp0 : 0 ≤ potential φ p ω := hφ0 _
  have hp2 : potential φ p ω ≤ 2 := hφ2 _
  have he : Real.exp (-β * potential φ p ω) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  unfold perturbation
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  have := Real.add_one_le_exp (-β * potential φ p ω)
  nlinarith

omit [MeasurableSpace E] in
/-- The exact Wilson density is the density of the connected polymer gas. -/
theorem wilsonDensity_eq_polymerDensity (d n : ℕ) (base : E)
    (φ : (Fin 4 → E) → ℝ) (β : ℝ) (ω : Link d n → E) :
    wilsonDensity φ β ω = polymerDensity (activity d base φ β n) univ ω := by
  unfold activity
  convert prod_one_add_eq_polymerDensity support support_nonempty base
    (perturbation φ β) (perturbation_local φ β) ω using 1
  simp [wilsonDensity, perturbation]

/-- A positive coupling threshold depending only on the dimension. -/
def beta0 (d : ℕ) : ℝ :=
  strongCouplingThreshold (4 * (d * d)) (16 * (d * d)) 4 1 1 (Real.exp (-1)) / 2

theorem beta0_pos (d : ℕ) : 0 < beta0 d :=
  div_pos (strongCouplingThreshold_pos _ _ _ _ _ (Real.exp_pos _)) (by norm_num)

/-- Closed form of the dimension-dependent coupling threshold. -/
theorem beta0_eq (d : ℕ) :
    beta0 d = Real.exp (-18) /
      (4 * (4 * (d : ℝ) ^ 2 + 1) * (16 * (d : ℝ) ^ 2 + 1) ^ 2) := by
  simp only [beta0, strongCouplingThreshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  rw [show (-18 : ℝ) = -1 - 17 by norm_num, Real.exp_sub]
  field_simp
  ring

/-- The connected plaquette activities satisfy the crossing input at strong
coupling, with decay rate one and smallness `exp (-1)` at every volume. -/
theorem crossingInput (d : ℕ) (base : E) {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    CrossingInput.CrossingInput (Link d) E (activity d base φ β) := by
  have : Nonempty E := ⟨base⟩
  refine ⟨fun n S => measurable_plaquetteActivity support base (perturbation φ β)
    (measurable_perturbation hφ β) S, ?_⟩
  refine ⟨fun n => plaquetteMajorant (support (d := d) (n := n)) (2 * β),
    1, Real.exp (-1), by norm_num, (Real.exp_pos _).le, ?_, ?_, ?_, ?_⟩
  · rw [← Real.exp_add]
    norm_num
  · intro n S v
    exact norm_plaquetteActivity_le support base (perturbation φ β)
      (norm_perturbation_le hφ0 hφ2 hβ) S v
  · intro n
    exact plaquetteMajorant_empty support support_nonempty _
  · intro n
    apply activitySmall_plaquetteMajorant support
      (δ := 2 * β) (κ := 1) (r := 1) (ε := Real.exp (-1))
      (s := 4) (Δ := 16 * (d * d)) (D := 4 * (d * d))
      (by positivity) (by norm_num) (by norm_num) (Real.exp_pos _).le
    · rw [← Real.exp_add]
      norm_num
    · exact card_support_le
    · exact diam_support_le
    · intro p
      convert degree_plaquetteGraph_le d n p using 1
      congr 1
      exact Subsingleton.elim _ _
    · exact card_incident_le d n
    · unfold beta0 at hβ0
      linarith

/-- Expectation against the finite Wilson density over the product reference law. -/
def wilsonExpectation {d n : ℕ} (ν₀ : Measure E) (φ : (Fin 4 → E) → ℝ) (β : ℝ)
    (F : (Link d n → E) → ℂ) : ℂ :=
  (∫ ω, F ω * wilsonDensity φ β ω ∂(Measure.pi fun _ : Link d n => ν₀)) /
    (∫ ω, wilsonDensity φ β ω ∂(Measure.pi fun _ : Link d n => ν₀))

/-- The ratio of Wilson integrals agrees with the polymer expectation. -/
theorem wilsonExpectation_eq_expectation {d n : ℕ} (ν₀ : Measure E)
    [IsProbabilityMeasure ν₀] (base : E) {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (F : (Link d n → E) → ℂ) :
    wilsonExpectation ν₀ φ β F = expectation ν₀ F (activity d base φ β n) univ := by
  have : Nonempty E := ⟨base⟩
  unfold wilsonExpectation expectation
  simp_rw [wilsonDensity_eq_polymerDensity d n base]
  rw [integral_polymerDensity ν₀ (activity d base φ β n)
    (fun S => measurable_plaquetteActivity support base (perturbation φ β)
      (measurable_perturbation hφ β) S)
    (plaquetteMajorant support (2 * β))
    (norm_plaquetteActivity_le support base (perturbation φ β)
      (norm_perturbation_le hφ0 hφ2 hβ))]

/-- The Wilson normalizing integral is nonzero throughout the stated regime. -/
theorem integral_wilsonDensity_ne_zero (d n : ℕ) (ν₀ : Measure E)
    [IsProbabilityMeasure ν₀] (base : E) {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    (∫ ω, wilsonDensity φ β ω ∂(Measure.pi fun _ : Link d n => ν₀)) ≠ 0 := by
  have : Nonempty E := ⟨base⟩
  have hc := crossingInput d base hφ hφ0 hφ2 hβ hβ0
  obtain ⟨bound, rate, ε, hr, he0, he, hbound, hempty, hsmall⟩ := hc.exists_bounds
  simp_rw [wilsonDensity_eq_polymerDensity d n base]
  rw [integral_polymerDensity ν₀ (activity d base φ β n)
    (hc.measurable_activity n) (bound n) (hbound n)]
  exact (removalBound_of_dobrushin
    (dobrushin_of_activitySmall ν₀ (activity d base φ β n) (bound n)
      (hbound n) (hempty n) hr.le he0 he (hsmall n)) univ).1

/-- Uniform exponential clustering of the Wilson expectations at strong coupling. -/
theorem wilson_clustering (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    {φ : (Fin 4 → E) → ℝ} (hφ : Measurable φ)
    (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (n : ℕ) (S₁ S₂ : Finset (Link d n)), S₁.Nonempty →
      ∀ (F₁ : (S₁ → E) → ℂ) (F₂ : (S₂ → E) → ℂ) (C₁ C₂ : ℝ),
      Measurable F₁ → Measurable F₂ → (∀ v, ‖F₁ v‖ ≤ C₁) → (∀ v, ‖F₂ v‖ ≤ C₂) →
      ‖wilsonExpectation ν₀ φ β (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) -
        wilsonExpectation ν₀ φ β (fun ω => F₁ (restrictTo S₁ ω)) *
          wilsonExpectation ν₀ φ β (fun ω => F₂ (restrictTo S₂ ω))‖ ≤
        3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂) := by
  have : Nonempty E := ⟨base⟩
  obtain ⟨κ, hκ, hc⟩ := CrossingInput.clustering (ν₀ := ν₀)
    (crossingInput d base hφ hφ0 hφ2 hβ hβ0)
  refine ⟨κ, hκ, ?_⟩
  intro n S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hb₁ hb₂
  simp_rw [wilsonExpectation_eq_expectation ν₀ base hφ hφ0 hφ2 hβ]
  exact hc n univ S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hb₁ hb₂

end Potential

/-- A plaquette has uniformly bounded metric tree length. -/
theorem treeLength_support_le {d n : ℕ} (p : Plaquette d n) : treeLength (support p) ≤ 4 := by
  have hc : ((support p).card : ℝ) ≤ 4 := by exact_mod_cast card_support_le p
  have ht := treeLength_le_card_mul_diam (support p)
  have hd := mul_le_mul_of_nonneg_left (diam_support_le p) (Nat.cast_nonneg (support p).card : (0 : ℝ) ≤ _)
  linarith

#print axioms dist_link_eq_zero_iff
#print axioms norm_coordinateCircle_eq
#print axioms sum_exp_dist_le
#print axioms diam_support_le
#print axioms card_incident_le
#print axioms degree_plaquetteGraph_le
#print axioms wilsonDensity_eq_polymerDensity
#print axioms beta0_pos
#print axioms beta0_eq
#print axioms crossingInput
#print axioms wilsonExpectation_eq_expectation
#print axioms integral_wilsonDensity_ne_zero
#print axioms wilson_clustering

end Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing
