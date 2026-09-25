import Mettapedia.Combinatorics.PolymerGas.Decay
import Mettapedia.Combinatorics.PolymerGas.Measure
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Polymer gases on a metric space of blocks

When the blocks carry a pseudometric, a polymer has a diameter and a distance to
any block set (the least distance from one of its blocks).  Along an overlap of
`a` and `s` the distance to a block set grows by at most the diameter of `s`
(`polymerDist_le_add_polymerDiam`), which is the Lipschitz property required by
the exponential supersolution of `PolymerGas.Decay`.  For families `Γ₁`, `Γ₂` of
polymers meeting `S₁` and `S₂`, a polymer meeting `S₂ ∪ ⋃ Γ₂` lies at distance at
least `d(S₁, S₂)` minus the total diameters of the families and itself from
`S₁ ∪ ⋃ Γ₁` (`polymerDist_ge_of_meeting`); a family whose union reaches the other
support, or two families that touch, have total diameter at least `d(S₁, S₂)`.

Sums over the polymers through a block (`blockSum`) control sums over polymers
overlapping a given polymer (`sum_le_sum_blockSum`), and a bound `1/2` on the
block sums of the activity bounds weighted by `e^{|γ|}` gives the
Kotecký–Preiss criterion with `a γ = |γ|` (`koteckyPreiss_of_blockSum`).
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Mettapedia.Combinatorics.PolymerGas

variable {X : Type*} [PseudoMetricSpace X]

/-- The distance from a polymer `a` to a block set `Y`: the least distance from a
block of `a` to `Y` (zero for the empty polymer). -/
def polymerDist (Y a : Finset X) : ℝ :=
  if h : a.Nonempty then a.inf' h fun p => Metric.infDist p (Y : Set X) else 0

/-- The diameter of a polymer. -/
def polymerDiam (a : Finset X) : ℝ := Metric.diam (a : Set X)

theorem polymerDist_nonneg (Y a : Finset X) : 0 ≤ polymerDist Y a := by
  unfold polymerDist
  split_ifs with h
  · exact Finset.le_inf' h _ fun p _ => Metric.infDist_nonneg
  · exact le_rfl

theorem polymerDiam_nonneg (a : Finset X) : 0 ≤ polymerDiam a := Metric.diam_nonneg

theorem polymerDist_le_infDist {Y a : Finset X} {p : X} (hp : p ∈ a) :
    polymerDist Y a ≤ Metric.infDist p (Y : Set X) := by
  have ha : a.Nonempty := ⟨p, hp⟩
  simp only [polymerDist, ha, ↓reduceDIte]
  exact Finset.inf'_le _ hp

theorem exists_infDist_eq_polymerDist {Y a : Finset X} (ha : a.Nonempty) :
    ∃ q ∈ a, Metric.infDist q (Y : Set X) = polymerDist Y a := by
  simp only [polymerDist, ha, ↓reduceDIte]
  obtain ⟨q, hq, heq⟩ := Finset.exists_mem_eq_inf' ha fun p => Metric.infDist p (Y : Set X)
  exact ⟨q, hq, heq.symm⟩

theorem dist_le_polymerDiam {a : Finset X} {p q : X} (hp : p ∈ a) (hq : q ∈ a) :
    dist p q ≤ polymerDiam a :=
  Metric.dist_le_diam_of_mem (a : Set X).toFinite.isBounded hp hq

theorem polymerDist_eq_zero_of_not_disjoint {Y a : Finset X} (h : ¬ Disjoint a Y) :
    polymerDist Y a = 0 := by
  obtain ⟨p, hpa, hpY⟩ := Finset.not_disjoint_iff.mp h
  exact le_antisymm ((polymerDist_le_infDist hpa).trans
    (Metric.infDist_zero_of_mem (s := (Y : Set X)) hpY).le) (polymerDist_nonneg Y a)

/-- **Lipschitz property along overlaps.**  If `a` and `s` overlap, the distance of
`a` to `Y` exceeds that of `s` by at most the diameter of `s`. -/
theorem polymerDist_le_add_polymerDiam {Y a s : Finset X} (has : ¬ Disjoint a s) :
    polymerDist Y a ≤ polymerDist Y s + polymerDiam s := by
  obtain ⟨p, hpa, hps⟩ := Finset.not_disjoint_iff.mp has
  obtain ⟨q, hqs, hq⟩ := exists_infDist_eq_polymerDist (Y := Y) ⟨p, hps⟩
  calc polymerDist Y a ≤ Metric.infDist p (Y : Set X) := polymerDist_le_infDist hpa
    _ ≤ Metric.infDist q (Y : Set X) + dist p q := Metric.infDist_le_infDist_add_dist
    _ ≤ polymerDist Y s + polymerDiam s := by
        rw [hq]
        linarith [dist_le_polymerDiam hps hqs]

/-! ## Distances between supports and families of polymers meeting them -/

variable [DecidableEq X]

/-- The total diameter of a family of polymers. -/
def familyExtent (Γ : Finset (Finset X)) : ℝ := ∑ γ ∈ Γ, polymerDiam γ

theorem familyExtent_nonneg (Γ : Finset (Finset X)) : 0 ≤ familyExtent Γ :=
  sum_nonneg fun γ _ => polymerDiam_nonneg γ

theorem polymerDiam_le_familyExtent {Γ : Finset (Finset X)} {γ : Finset X} (hγ : γ ∈ Γ) :
    polymerDiam γ ≤ familyExtent Γ :=
  single_le_sum (fun γ _ => polymerDiam_nonneg γ) hγ

/-- The distance from a block `p` of `S₂` to `S₁ ∪ ⋃ Γ₁`, where every polymer of `Γ₁`
meets `S₁`, is at least the distance from `S₂` to `S₁` minus the extent of `Γ₁`. -/
theorem infDist_union_ge {S₁ S₂ : Finset X} (hS₁ : S₁.Nonempty) {Γ₁ : Finset (Finset X)}
    (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁) {p : X} (hp : p ∈ S₂) :
    polymerDist S₁ S₂ - familyExtent Γ₁ ≤
      Metric.infDist p ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X) := by
  have hne : ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X).Nonempty := by
    obtain ⟨x, hx⟩ := hS₁
    exact ⟨x, by simp [hx]⟩
  rw [Metric.le_infDist hne]
  intro y hy
  have hD : polymerDist S₁ S₂ ≤ Metric.infDist p (S₁ : Set X) := polymerDist_le_infDist hp
  have hext := familyExtent_nonneg Γ₁
  simp only [coe_union, Set.mem_union, mem_coe, coe_biUnion, Set.mem_iUnion, id,
    exists_prop] at hy
  rcases hy with hy | ⟨γ, hγ, hyγ⟩
  · have := Metric.infDist_le_dist_of_mem (x := p) (mem_coe.mpr hy)
    linarith
  · obtain ⟨y', hy'γ, hy'S⟩ := Finset.not_disjoint_iff.mp (hΓ₁ γ hγ)
    have h1 := Metric.infDist_le_dist_of_mem (x := p) (mem_coe.mpr hy'S)
    have h2 : dist p y' ≤ dist p y + dist y y' := dist_triangle p y y'
    have h3 : dist y y' ≤ polymerDiam γ := dist_le_polymerDiam hyγ hy'γ
    have h4 := polymerDiam_le_familyExtent hγ
    linarith

/-- The distance from a block of `S₂ ∪ ⋃ Γ₂` to `S₁ ∪ ⋃ Γ₁`, where the polymers of
`Γ₁` meet `S₁` and those of `Γ₂` meet `S₂`, is at least the distance from `S₂` to
`S₁` minus both extents. -/
theorem infDist_union_ge_of_mem_union {S₁ S₂ : Finset X} (hS₁ : S₁.Nonempty)
    {Γ₁ Γ₂ : Finset (Finset X)} (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁)
    (hΓ₂ : ∀ γ ∈ Γ₂, ¬ Disjoint γ S₂) {p : X} (hp : p ∈ S₂ ∪ Γ₂.biUnion id) :
    polymerDist S₁ S₂ - familyExtent Γ₁ - familyExtent Γ₂ ≤
      Metric.infDist p ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X) := by
  have hext := familyExtent_nonneg Γ₂
  rcases mem_union.mp hp with hp | hp
  · have := infDist_union_ge hS₁ hΓ₁ hp
    linarith
  · obtain ⟨γ, hγ, hpγ⟩ := mem_biUnion.mp hp
    obtain ⟨p', hp'γ, hp'S⟩ := Finset.not_disjoint_iff.mp (hΓ₂ γ hγ)
    have h1 := infDist_union_ge hS₁ hΓ₁ hp'S
    have h2 : Metric.infDist p' ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X) ≤
        Metric.infDist p ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X) + dist p' p :=
      Metric.infDist_le_infDist_add_dist
    have h3 : dist p' p ≤ polymerDiam γ := dist_le_polymerDiam hp'γ hpγ
    have h4 := polymerDiam_le_familyExtent hγ
    linarith

/-- A polymer meeting `S₂ ∪ ⋃ Γ₂` lies at distance at least
`d(S₁, S₂) - ext Γ₁ - ext Γ₂ - diam b` from `S₁ ∪ ⋃ Γ₁`. -/
theorem polymerDist_ge_of_meeting {S₁ S₂ : Finset X} (hS₁ : S₁.Nonempty)
    {Γ₁ Γ₂ : Finset (Finset X)} (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁)
    (hΓ₂ : ∀ γ ∈ Γ₂, ¬ Disjoint γ S₂) {b : Finset X}
    (hb : ¬ Disjoint b (S₂ ∪ Γ₂.biUnion id)) :
    polymerDist S₁ S₂ - familyExtent Γ₁ - familyExtent Γ₂ - polymerDiam b ≤
      polymerDist (S₁ ∪ Γ₁.biUnion id) b := by
  obtain ⟨p, hpb, hpY⟩ := Finset.not_disjoint_iff.mp hb
  obtain ⟨q, hqb, hq⟩ := exists_infDist_eq_polymerDist
    (Y := S₁ ∪ Γ₁.biUnion id) ⟨p, hpb⟩
  have h1 := infDist_union_ge_of_mem_union hS₁ hΓ₁ hΓ₂ hpY
  have h2 : Metric.infDist p ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X) ≤
      Metric.infDist q ((S₁ ∪ Γ₁.biUnion id : Finset X) : Set X) + dist p q :=
    Metric.infDist_le_infDist_add_dist
  have h3 : dist p q ≤ polymerDiam b := dist_le_polymerDiam hpb hqb
  rw [← hq]
  linarith

/-- If `S₁ ∪ ⋃ Γ₁` reaches `S₂`, the extent of `Γ₁` is at least the distance from
`S₂` to `S₁`. -/
theorem polymerDist_le_familyExtent_of_reach {S₁ S₂ : Finset X} {Γ₁ : Finset (Finset X)}
    (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁) (hreach : ¬ Disjoint (S₁ ∪ Γ₁.biUnion id) S₂) :
    polymerDist S₁ S₂ ≤ familyExtent Γ₁ := by
  obtain ⟨p, hpY, hpS₂⟩ := Finset.not_disjoint_iff.mp hreach
  have hD : polymerDist S₁ S₂ ≤ Metric.infDist p (S₁ : Set X) := polymerDist_le_infDist hpS₂
  rcases mem_union.mp hpY with hp | hp
  · rw [Metric.infDist_zero_of_mem (s := (S₁ : Set X)) hp] at hD
    linarith [familyExtent_nonneg Γ₁]
  · obtain ⟨γ, hγ, hpγ⟩ := mem_biUnion.mp hp
    obtain ⟨y', hy'γ, hy'S⟩ := Finset.not_disjoint_iff.mp (hΓ₁ γ hγ)
    have h1 := Metric.infDist_le_dist_of_mem (x := p) (mem_coe.mpr hy'S)
    have h2 : dist p y' ≤ polymerDiam γ := dist_le_polymerDiam hpγ hy'γ
    have h3 := polymerDiam_le_familyExtent hγ
    linarith

/-- If a polymer of `Γ₂` meets `S₁ ∪ ⋃ Γ₁`, the two extents together are at least
the distance from `S₂` to `S₁`. -/
theorem polymerDist_le_familyExtent_add_of_meet {S₁ S₂ : Finset X} (hS₁ : S₁.Nonempty)
    {Γ₁ Γ₂ : Finset (Finset X)} (hΓ₁ : ∀ γ ∈ Γ₁, ¬ Disjoint γ S₁)
    (hΓ₂ : ∀ γ ∈ Γ₂, ¬ Disjoint γ S₂) {γ₂ : Finset X} (hγ₂ : γ₂ ∈ Γ₂)
    (hmeet : ¬ Disjoint γ₂ (S₁ ∪ Γ₁.biUnion id)) :
    polymerDist S₁ S₂ ≤ familyExtent Γ₁ + familyExtent Γ₂ := by
  obtain ⟨p, hpγ, hpY⟩ := Finset.not_disjoint_iff.mp hmeet
  obtain ⟨p', hp'γ, hp'S⟩ := Finset.not_disjoint_iff.mp (hΓ₂ γ₂ hγ₂)
  have h1 := infDist_union_ge hS₁ hΓ₁ hp'S
  have h2 := Metric.infDist_le_dist_of_mem (x := p') (mem_coe.mpr hpY)
  have h3 : dist p' p ≤ polymerDiam γ₂ := dist_le_polymerDiam hp'γ hpγ
  have h4 := polymerDiam_le_familyExtent hγ₂
  linarith

/-! ## Sums over the polymers through a block -/

section BlockSums

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The sum of `f` over all polymers containing the block `x`. -/
def blockSum (f : Finset Y → ℝ) (x : Y) : ℝ :=
  ∑ γ ∈ (Finset.univ : Finset (Finset Y)).filter (x ∈ ·), f γ

/-- A sum over polymers overlapping `a` is bounded by the block sums over `a`. -/
theorem sum_le_sum_blockSum {f : Finset Y → ℝ} (hf : ∀ γ, 0 ≤ f γ) {a : Finset Y}
    {S : Finset (Finset Y)} (hS : ∀ s ∈ S, ¬ Disjoint a s) :
    ∑ s ∈ S, f s ≤ ∑ x ∈ a, blockSum f x := by
  have hrw : ∑ x ∈ a, blockSum f x =
      ∑ s ∈ (univ : Finset (Finset Y)), ∑ x ∈ a, (if x ∈ s then f s else 0) := by
    unfold blockSum
    simp_rw [sum_filter]
    exact sum_comm
  rw [hrw]
  have hnn : ∀ s x, 0 ≤ (if x ∈ s then f s else 0) := fun s x => by
    split_ifs
    · exact hf s
    · exact le_rfl
  have hterm : ∀ s ∈ S, f s ≤ ∑ x ∈ a, (if x ∈ s then f s else 0) := by
    intro s hs
    obtain ⟨x, hxa, hxs⟩ := Finset.not_disjoint_iff.mp (hS s hs)
    calc f s = (if x ∈ s then f s else 0) := by simp [hxs]
      _ ≤ ∑ y ∈ a, (if y ∈ s then f s else 0) :=
        single_le_sum (f := fun y => if y ∈ s then f s else 0) (fun y _ => hnn s y) hxa
  calc ∑ s ∈ S, f s ≤ ∑ s ∈ S, ∑ x ∈ a, (if x ∈ s then f s else 0) := sum_le_sum hterm
    _ ≤ ∑ s ∈ (univ : Finset (Finset Y)), ∑ x ∈ a, (if x ∈ s then f s else 0) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) fun s _ _ =>
        sum_nonneg fun x _ => hnn s x

theorem sum_blockSum_le {f : Finset Y → ℝ} {ε : ℝ} (hε : ∀ x, blockSum f x ≤ ε)
    (a : Finset Y) : ∑ x ∈ a, blockSum f x ≤ a.card * ε := by
  calc ∑ x ∈ a, blockSum f x ≤ ∑ _x ∈ a, ε := sum_le_sum fun x _ => hε x
    _ = a.card * ε := by rw [sum_const, nsmul_eq_mul]

/-- **Kotecký–Preiss from block sums.**  If the empty polymer has no activity and
the activity bounds weighted by `e^{|γ|}` sum to at most `1/2` over the polymers
through every block, the Kotecký–Preiss criterion holds with `a γ = |γ|` for the
overlap graph. -/
theorem koteckyPreiss_of_blockSum {w : Finset Y → ℂ} {k : Finset Y → ℝ}
    (hw : ∀ γ, ‖w γ‖ ≤ k γ) (hk0 : k ∅ = 0)
    (hsmall : ∀ x, blockSum (fun γ => k γ * Real.exp γ.card) x ≤ 1 / 2) :
    KoteckyPreissCondition (overlapGraph Y) w fun γ => (γ.card : ℝ) where
  nonneg γ := Nat.cast_nonneg _
  bound γ S hS := by
    have hkn : ∀ γ, 0 ≤ k γ := fun γ => (norm_nonneg _).trans (hw γ)
    have hf : ∀ γ, 0 ≤ k γ * Real.exp γ.card := fun γ =>
      mul_nonneg (hkn γ) (Real.exp_pos _).le
    rcases γ.eq_empty_or_nonempty with hγ | ⟨x₀, hx₀⟩
    · subst hγ
      have hSe : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro u hu
        exact (hS u hu).2 (Finset.disjoint_empty_left u)
      subst hSe
      have := hw ∅
      rw [hk0] at this
      simp [norm_le_zero_iff.mp this]
    · have hsum : ∑ u ∈ S, ‖w u‖ * Real.exp u.card ≤ γ.card * (1 / 2) := by
        calc ∑ u ∈ S, ‖w u‖ * Real.exp u.card ≤ ∑ u ∈ S, k u * Real.exp u.card :=
              sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (hw u) (Real.exp_pos _).le
          _ ≤ ∑ x ∈ γ, blockSum (fun γ => k γ * Real.exp γ.card) x :=
              sum_le_sum_blockSum hf fun u hu => (hS u hu).2
          _ ≤ γ.card * (1 / 2) := sum_blockSum_le hsmall γ
      have hself : ‖w γ‖ * Real.exp γ.card ≤ 1 / 2 := by
        calc ‖w γ‖ * Real.exp γ.card ≤ k γ * Real.exp γ.card :=
              mul_le_mul_of_nonneg_right (hw γ) (Real.exp_pos _).le
          _ ≤ blockSum (fun γ => k γ * Real.exp γ.card) x₀ := by
              unfold blockSum
              exact single_le_sum (f := fun γ => k γ * Real.exp γ.card)
                (fun γ _ => hf γ) (mem_filter.mpr ⟨mem_univ _, hx₀⟩)
          _ ≤ 1 / 2 := hsmall x₀
      have hcard : (1 : ℝ) ≤ γ.card := by exact_mod_cast Finset.card_pos.mpr ⟨x₀, hx₀⟩
      linarith

end BlockSums

/-! ## Sums over families of polymers -/

section Families

variable {Y : Type*} [DecidableEq Y]

/-- The sum over all subfamilies of `T` of the product of a nonnegative weight is
at most `exp` of the total weight. -/
theorem sum_powerset_prod_le_exp {T : Finset (Finset Y)} {v : Finset Y → ℝ}
    (hv : ∀ γ, 0 ≤ v γ) :
    ∑ Γ ∈ T.powerset, ∏ γ ∈ Γ, v γ ≤ Real.exp (∑ γ ∈ T, v γ) := by
  rw [← Finset.prod_one_add, Real.exp_sum]
  exact Finset.prod_le_prod (fun γ _ => by linarith [hv γ]) fun γ _ => by
    linarith [Real.add_one_le_exp (v γ)]

/-- The number of blocks of `S ∪ ⋃ Γ` is at most `|S| + ∑_{γ ∈ Γ} |γ|`. -/
theorem card_union_biUnion_le (S : Finset Y) (Γ : Finset (Finset Y)) :
    ((S ∪ Γ.biUnion id).card : ℝ) ≤ S.card + ∑ γ ∈ Γ, (γ.card : ℝ) := by
  have h1 := Finset.card_union_le S (Γ.biUnion id)
  have h2 := Finset.card_biUnion_le (s := Γ) (t := id)
  have : ((S ∪ Γ.biUnion id).card : ℝ) ≤ (S.card + ∑ γ ∈ Γ, γ.card : ℕ) := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  simpa using this

end Families

section MeetingSums

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A sum over the polymers of `Λ` meeting `S` is bounded by the block sums over `S`. -/
theorem sum_meeting_le {f : Finset Y → ℝ} (hf : ∀ γ, 0 ≤ f γ) (Λ : Finset (Finset Y))
    (S : Finset Y) : ∑ γ ∈ meeting Λ S, f γ ≤ ∑ x ∈ S, blockSum f x :=
  sum_le_sum_blockSum hf fun γ hγ => fun h => (mem_filter.mp hγ).2 h.symm

end MeetingSums

#print axioms polymerDist_le_add_polymerDiam
#print axioms polymerDist_ge_of_meeting
#print axioms koteckyPreiss_of_blockSum

end Mettapedia.Combinatorics.PolymerGas
