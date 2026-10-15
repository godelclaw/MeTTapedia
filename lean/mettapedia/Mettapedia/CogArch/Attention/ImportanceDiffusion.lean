import Mettapedia.CogArch.Attention.Equilibrium

/-!
# ECAN importance diffusion and its PageRank core

Upstream ECAN (iCog-Labs-Dev/metta-attention, commit 3e1c814, a port of the
OpenCog attention agents) diffuses short-term importance as a trade. A source
atom gives a fraction `spread` (`MAX_SPREAD_PERCENTAGE`) of its STI: the share
`hebbianShare` (`HEBBIAN_MAX_ALLOCATION_PERCENTAGE`) goes to its asymmetric
Hebbian targets in proportion to link mean times confidence, divided by the
number of targets, and the rest is split evenly over the atoms it is incident
with or contains. Only atoms in the attentional focus are sources.

This module states that rule exactly and proves:

* for every fixed source set the diffusion is transport by a row-stochastic
  kernel, so STI is conserved whatever the source set (`diffuse_eq_transport`);
* when every atom is a source, rent is proportional to holdings and stimulus is
  exogenous, the cycle is a restart walk whose unique equilibrium is the
  personalized PageRank vector of the diffusion kernel (`cycle_fixed_iff_ppr`),
  reached geometrically (`cycle_converges`); its total is set by the stimulus
  alone (`equilibrium_mass`) and it is additive in the stimulus
  (`equilibrium_add`);
* what that linear core does not have: wages paid to focus atoms make every
  focus set self-sustaining, so the response depends on history and is not
  additive (`focusWages_fixed`, `wage_not_additive`); upstream's rent rule keeps
  the bank's funds in a band around its target, independently of the stimulus
  level (`funds_band_invariant`);
* convex mixtures of diffusion mechanisms and separately funded mechanisms are
  again conservative (`transport_mix`, `parallel_mass`).

Modelling choices: shares are computed from one snapshot (synchronous
application); an atom with no incident atoms gives nothing structurally (the
upstream focus agent divides by zero there); rent is per cycle, without the
elapsed-time multiplier. Real arithmetic; floating point is not certified.
-/

noncomputable section
namespace Mettapedia.CogArch.Attention.ImportanceDiffusion
open scoped BigOperators Classical
open Finset
open Mettapedia.ProbabilityTheory.MarkovChain
open FiniteMassTransport (Kernel transport mass restart restartRounds restartingWalk)

variable {ι : Type*} [Fintype ι]

/-- Upstream diffusion parameters and the graph they act on. -/
structure Diffusion (ι : Type*) where
  spread : ℝ
  hebbianShare : ℝ
  incident : ι → Finset ι
  hebbian : ι → Finset ι
  /-- Hebbian link mean times confidence. -/
  strength : ι → ι → ℝ
  spread_nonneg : 0 ≤ spread
  spread_le_one : spread ≤ 1
  hebbianShare_nonneg : 0 ≤ hebbianShare
  hebbianShare_le_one : hebbianShare ≤ 1
  strength_nonneg : ∀ a j, 0 ≤ strength a j
  strength_le_one : ∀ a j, strength a j ≤ 1

namespace Diffusion

variable (D : Diffusion ι)

def structural (a j : ι) : ℝ :=
  if j ∈ D.incident a then D.spread * (1 - D.hebbianShare) / (D.incident a).card else 0

def associative (a j : ι) : ℝ :=
  if j ∈ D.hebbian a then
    D.spread * D.hebbianShare * D.strength a j / (D.hebbian a).card else 0

/-- Fraction of a source's STI that reaches `j`. -/
def share (a j : ι) : ℝ := D.structural a j + D.associative a j

/-- Fraction of its STI a source gives away. -/
def given (a : ι) : ℝ := ∑ j, D.share a j

omit [Fintype ι] in
theorem structural_nonneg (a j : ι) : 0 ≤ D.structural a j := by
  unfold structural
  split_ifs
  · exact div_nonneg (mul_nonneg D.spread_nonneg (sub_nonneg.mpr D.hebbianShare_le_one))
      (Nat.cast_nonneg _)
  · exact le_rfl

omit [Fintype ι] in
theorem associative_nonneg (a j : ι) : 0 ≤ D.associative a j := by
  unfold associative
  split_ifs
  · exact div_nonneg (mul_nonneg (mul_nonneg D.spread_nonneg D.hebbianShare_nonneg)
      (D.strength_nonneg a j)) (Nat.cast_nonneg _)
  · exact le_rfl

omit [Fintype ι] in
theorem share_nonneg (a j : ι) : 0 ≤ D.share a j :=
  add_nonneg (D.structural_nonneg a j) (D.associative_nonneg a j)

theorem given_nonneg (a : ι) : 0 ≤ D.given a :=
  Finset.sum_nonneg fun j _ => D.share_nonneg a j

theorem sum_structural_le (a : ι) :
    ∑ j, D.structural a j ≤ D.spread * (1 - D.hebbianShare) := by
  have hc : 0 ≤ D.spread * (1 - D.hebbianShare) :=
    mul_nonneg D.spread_nonneg (sub_nonneg.mpr D.hebbianShare_le_one)
  unfold structural
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  by_cases h : (D.incident a).card = 0
  · simp [h, hc]
  · have hne : ((D.incident a).card : ℝ) ≠ 0 := by exact_mod_cast h
    rw [mul_div_cancel₀ _ hne]

theorem sum_associative_le (a : ι) :
    ∑ j, D.associative a j ≤ D.spread * D.hebbianShare := by
  have hc : 0 ≤ D.spread * D.hebbianShare := mul_nonneg D.spread_nonneg D.hebbianShare_nonneg
  unfold associative
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  by_cases h : (D.hebbian a).card = 0
  · rw [Finset.card_eq_zero.mp h]
    simpa using hc
  · have hne : ((D.hebbian a).card : ℝ) ≠ 0 := by exact_mod_cast h
    calc ∑ j ∈ D.hebbian a, D.spread * D.hebbianShare * D.strength a j / (D.hebbian a).card
        ≤ ∑ _j ∈ D.hebbian a, D.spread * D.hebbianShare / (D.hebbian a).card := by
          apply Finset.sum_le_sum
          intro j _
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_of_le_one_right hc (D.strength_le_one a j)
      _ = D.spread * D.hebbianShare := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hne]

theorem given_le_spread (a : ι) : D.given a ≤ D.spread := by
  have h1 := D.sum_structural_le a
  have h2 := D.sum_associative_le a
  unfold given share
  rw [Finset.sum_add_distrib]
  nlinarith

theorem given_le_one (a : ι) : D.given a ≤ 1 := (D.given_le_spread a).trans D.spread_le_one

/-! ## Diffusion from a fixed source set is a stochastic kernel -/

/-- Sources keep what they do not give; non-sources keep everything. -/
def matrix (S : Finset ι) : Matrix ι ι ℝ := fun a j =>
  if a ∈ S then (if a = j then 1 - D.given a else 0) + D.share a j
  else if a = j then 1 else 0

theorem matrix_nonneg (S : Finset ι) (a j : ι) : 0 ≤ D.matrix S a j := by
  unfold matrix
  have hg := sub_nonneg.mpr (D.given_le_one a)
  split_ifs <;> first
    | exact add_nonneg hg (D.share_nonneg a j)
    | exact add_nonneg le_rfl (D.share_nonneg a j)
    | norm_num

theorem matrix_row_sum (S : Finset ι) (a : ι) : ∑ j, D.matrix S a j = 1 := by
  unfold matrix
  by_cases ha : a ∈ S
  · simp only [ha, if_true, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ]
    unfold given
    ring
  · simp [ha]

def kernel (S : Finset ι) : Kernel ι :=
  ⟨D.matrix S, Matrix.mem_rowStochastic_iff_sum.mpr ⟨D.matrix_nonneg S, D.matrix_row_sum S⟩⟩

/-- Upstream diffusion as a trade: each source `a` pays `x a * share a j` to
`j` and loses `x a * given a`. -/
def diffuse (S : Finset ι) (x : ι → ℝ) (j : ι) : ℝ :=
  x j - (if j ∈ S then D.given j * x j else 0) + ∑ a ∈ S, x a * D.share a j

theorem diffuse_eq_transport (S : Finset ι) (x : ι → ℝ) :
    D.diffuse S x = transport (D.kernel S) x := by
  funext j
  have hterm : ∀ a, x a * D.matrix S a j =
      (if a = j then (if a ∈ S then x a * (1 - D.given a) else x a) else 0) +
        (if a ∈ S then x a * D.share a j else 0) := by
    intro a
    unfold matrix
    by_cases haj : a = j
    · subst haj
      by_cases ha : a ∈ S <;> simp [ha]; ring
    · by_cases ha : a ∈ S <;> simp [ha, haj]
  simp only [transport, FiniteMassTransport.Kernel.share, kernel]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_mem, Finset.univ_inter]
  unfold diffuse
  by_cases hj : j ∈ S
  · simp [hj]
    ring
  · simp [hj]

/-- Diffusion conserves STI for every source set. -/
theorem diffuse_mass (S : Finset ι) (x : ι → ℝ) : mass (D.diffuse S x) = mass x := by
  rw [diffuse_eq_transport]
  exact FiniteMassTransport.transport_mass _ x

theorem diffuse_nonneg (S : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (j : ι) :
    0 ≤ D.diffuse S x j := by
  rw [diffuse_eq_transport]
  exact FiniteMassTransport.transport_nonneg _ x hx j

/-- Upstream's attentional focus: atoms at or above the threshold. -/
def focus (θ : ℝ) (x : ι → ℝ) : Finset ι := Finset.univ.filter fun i => θ ≤ x i

/-- Focus-gated diffusion: the source set depends on the state. -/
def gated (θ : ℝ) (x : ι → ℝ) : ι → ℝ := D.diffuse (focus θ x) x

/-- Gating changes which kernel applies, never the total. -/
theorem gated_mass (θ : ℝ) (x : ι → ℝ) : mass (D.gated θ x) = mass x :=
  D.diffuse_mass _ x

/-! ## The linear core is personalized PageRank -/

/-- One linear ECAN cycle: every atom diffuses, holdings are retained at rate `ρ`
(rent proportional to holdings) and exogenous stimulus `u` is added. -/
def cycle (ρ : ℝ) (u x : ι → ℝ) (j : ι) : ℝ := ρ * D.diffuse Finset.univ x j + u j

theorem cycle_eq_restart (ρ : ℝ) (hρ1 : ρ < 1) (u x : ι → ℝ) :
    D.cycle ρ u x = restart (D.kernel Finset.univ) ρ (fun i => u i / (1 - ρ)) x := by
  have hne : (1 - ρ) ≠ 0 := by linarith
  funext j
  simp only [cycle, restart, D.diffuse_eq_transport]
  field_simp
  ring

/-- The PageRank walk on the full diffusion kernel, restarting with probability `1-ρ`. -/
def walk (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : Restart.RestartWalk ι :=
  restartingWalk (D.kernel Finset.univ) ρ hρ0 hρ1

/-- Personalized PageRank of the stimulus: the candidate equilibrium. -/
def equilibrium (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (u : ι → ℝ) : ι → ℝ :=
  (D.walk ρ hρ0 hρ1).ppr fun i => u i / (1 - ρ)

/-- The linear cycle's fixed points are exactly the PageRank vector. -/
theorem cycle_fixed_iff_ppr (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (u x : ι → ℝ) :
    D.cycle ρ u x = x ↔ x = D.equilibrium ρ hρ0 hρ1 u := by
  rw [D.cycle_eq_restart ρ hρ1, FiniteMassTransport.restart_eq_walk_step _ ρ hρ0 hρ1]
  constructor
  · exact fun h => (D.walk ρ hρ0 hρ1).ppr_unique h
  · rintro rfl
    exact (D.walk ρ hρ0 hρ1).ppr_fixed _

/-- From any start the cycle approaches the PageRank vector at rate `ρ`. -/
theorem cycle_converges (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (u x : ι → ℝ) (n : ℕ) :
    FiniteMassTransport.distance ((D.cycle ρ u)^[n] x) (D.equilibrium ρ hρ0 hρ1 u) ≤
      ρ ^ n * FiniteMassTransport.distance x (D.equilibrium ρ hρ0 hρ1 u) := by
  have hiter : ∀ m, (D.cycle ρ u)^[m] x =
      restartRounds (D.kernel Finset.univ) ρ (fun i => u i / (1 - ρ)) m x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, D.cycle_eq_restart ρ hρ1]
      rfl
  rw [hiter]
  apply FiniteMassTransport.restart_error_bound _ ρ hρ0
  rw [← D.cycle_eq_restart ρ hρ1]
  exact (D.cycle_fixed_iff_ppr ρ hρ0 hρ1 u _).mpr rfl

/-- The equilibrium total is set by the stimulus alone. -/
theorem equilibrium_mass (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (u : ι → ℝ) :
    mass (D.equilibrium ρ hρ0 hρ1 u) = mass u / (1 - ρ) := by
  have hfix := (D.cycle_fixed_iff_ppr ρ hρ0 hρ1 u _).mpr rfl
  have hm : mass (D.cycle ρ u (D.equilibrium ρ hρ0 hρ1 u)) =
      ρ * mass (D.equilibrium ρ hρ0 hρ1 u) + mass u := by
    simp only [mass, cycle, Finset.sum_add_distrib, ← Finset.mul_sum]
    have := D.diffuse_mass Finset.univ (D.equilibrium ρ hρ0 hρ1 u)
    simp only [mass] at this
    rw [this]
  rw [hfix] at hm
  have hne : (1 - ρ) ≠ 0 := by linarith
  field_simp
  linarith

/-- Stimuli superpose: the equilibrium of a sum is the sum of equilibria. -/
theorem equilibrium_add (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (u v : ι → ℝ) :
    D.equilibrium ρ hρ0 hρ1 (u + v) =
      D.equilibrium ρ hρ0 hρ1 u + D.equilibrium ρ hρ0 hρ1 v := by
  unfold equilibrium
  rw [← Restart.RestartWalk.ppr_add]
  congr 1
  funext i
  simp [add_div]

end Diffusion

/-! ## What the linear core leaves out -/

/-- Wages paid to atoms in focus: stimulus that depends on the state. -/
def focusWages (ρ w θ : ℝ) (x : ι → ℝ) (j : ι) : ℝ :=
  ρ * x j + if θ ≤ x j then w else 0

omit [Fintype ι] in
/-- Every focus set sustains itself: atoms in `A` sit at `w/(1-ρ)`, the rest at zero.
With `n` atoms there are `2^n` fixed points, against one for the linear core. -/
theorem focusWages_fixed (ρ w θ : ℝ) (hρ1 : ρ < 1) (hθ : 0 < θ) (hw : (1 - ρ) * θ ≤ w)
    (A : Finset ι) :
    focusWages ρ w θ (fun i => if i ∈ A then w / (1 - ρ) else 0) =
      fun i => if i ∈ A then w / (1 - ρ) else 0 := by
  have hpos : 0 < 1 - ρ := by linarith
  have hθw : θ ≤ w / (1 - ρ) := by rw [le_div_iff₀ hpos]; linarith
  funext j
  unfold focusWages
  by_cases hj : j ∈ A
  · simp only [hj, if_true, hθw]
    field_simp
    ring
  · simp [hj, not_le.mpr hθ]

omit [Fintype ι] in
/-- Below the threshold an atom stays below it. -/
theorem focusWages_out (ρ w θ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x : ι → ℝ) (j : ι)
    (hx0 : 0 ≤ x j) (hx : x j < θ) :
    0 ≤ focusWages ρ w θ x j ∧ focusWages ρ w θ x j < θ := by
  unfold focusWages
  simp only [not_le.mpr hx, if_false, add_zero]
  exact ⟨mul_nonneg hρ0 hx0, lt_of_le_of_lt (mul_le_of_le_one_left hx0 hρ1) hx⟩

omit [Fintype ι] in
/-- In focus an atom stays in focus once wages cover the rent at the threshold. -/
theorem focusWages_in (ρ w θ : ℝ) (hρ0 : 0 ≤ ρ) (hw : (1 - ρ) * θ ≤ w) (x : ι → ℝ) (j : ι)
    (hx : θ ≤ x j) : θ ≤ focusWages ρ w θ x j := by
  unfold focusWages
  simp only [hx, if_true]
  nlinarith

omit [Fintype ι] in
/-- Focus-dependent stimulus does not superpose. -/
theorem wage_not_additive (ρ w θ : ℝ) (hθ : 0 < θ) (hw : w ≠ 0) (j : ι) :
    focusWages ρ w θ (fun _ => θ / 2 + θ / 2) j ≠
      focusWages ρ w θ (fun _ => θ / 2) j + focusWages ρ w θ (fun _ => θ / 2) j := by
  unfold focusWages
  have hhalf : ¬ θ ≤ θ / 2 := by linarith
  simp only [add_halves, le_refl, if_true, hhalf, if_false, add_zero]
  intro h
  apply hw
  linarith

/-- Upstream rent per focus atom: zero at or above the funds target, otherwise the
base rent raised by the shortfall relative to the buffer, at most doubled. -/
def rent (base target buffer funds : ℝ) : ℝ :=
  if target - funds ≤ 0 then 0
  else base + base * max (min ((target - funds) / buffer) 1) (-0.99)

theorem rent_above_target (base target buffer funds : ℝ) (h : target ≤ funds) :
    rent base target buffer funds = 0 := by
  simp [rent, sub_nonpos.mpr h]

theorem rent_below_target (base target buffer funds : ℝ) (hb : 0 < base)
    (hbuf : 0 < buffer) (h : funds < target) :
    base < rent base target buffer funds ∧ rent base target buffer funds ≤ 2 * base := by
  have hpos : 0 < (target - funds) / buffer := div_pos (by linarith) hbuf
  have hmin : 0 < min ((target - funds) / buffer) 1 := lt_min hpos one_pos
  have hmax : max (min ((target - funds) / buffer) 1) (-0.99) =
      min ((target - funds) / buffer) 1 := max_eq_left (by linarith)
  have hle : min ((target - funds) / buffer) 1 ≤ 1 := min_le_right _ _
  simp only [rent, not_le.mpr (sub_pos.mpr h), if_false, hmax]
  constructor <;> nlinarith

/-- One bank cycle: rent from `n` focus atoms comes in, wages go out. -/
def fundsStep (n base target buffer wages funds : ℝ) : ℝ :=
  funds + n * rent base target buffer funds - wages

/-- Funds below target rise when the rent base covers the wages. -/
theorem funds_rise_below_target (n base target buffer wages funds : ℝ) (hn : 0 < n)
    (hb : 0 < base) (hbuf : 0 < buffer) (hw : wages ≤ n * base) (h : funds < target) :
    funds < fundsStep n base target buffer wages funds := by
  have := (rent_below_target base target buffer funds hb hbuf h).1
  unfold fundsStep
  nlinarith

/-- The band from `target - wages` to `target + 2 n base` is invariant, however
large the stimulus paid out as wages, as long as rent can cover it. -/
theorem funds_band_invariant (n base target buffer wages funds : ℝ) (hn : 0 ≤ n)
    (hb : 0 < base) (hbuf : 0 < buffer) (hw0 : 0 ≤ wages) (hw : wages ≤ n * base)
    (hlo : target - wages ≤ funds) (hhi : funds ≤ target + 2 * n * base) :
    target - wages ≤ fundsStep n base target buffer wages funds ∧
      fundsStep n base target buffer wages funds ≤ target + 2 * n * base := by
  unfold fundsStep
  by_cases h : funds < target
  · obtain ⟨hr1, hr2⟩ := rent_below_target base target buffer funds hb hbuf h
    constructor <;> nlinarith
  · rw [rent_above_target base target buffer funds (not_lt.mp h)]
    constructor <;> nlinarith

/-! ## Mechanisms in parallel -/

/-- A convex mixture of two diffusion kernels is a kernel. -/
def mix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (K L : Kernel ι) : Kernel ι :=
  ⟨fun i j => t * FiniteMassTransport.Kernel.share K i j +
      (1 - t) * FiniteMassTransport.Kernel.share L i j,
    Matrix.mem_rowStochastic_iff_sum.mpr ⟨fun i j => add_nonneg
        (mul_nonneg ht0 (FiniteMassTransport.Kernel.nonneg K i j))
        (mul_nonneg (sub_nonneg.mpr ht1) (FiniteMassTransport.Kernel.nonneg L i j)),
      fun i => by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          FiniteMassTransport.Kernel.row_sum]
        ring⟩⟩

/-- Mixing mechanisms on one fund mixes their transports. -/
theorem transport_mix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (K L : Kernel ι) (x : ι → ℝ) :
    transport (mix t ht0 ht1 K L) x = t • transport K x + (1 - t) • transport L x := by
  funext j
  simp only [transport, mix, FiniteMassTransport.Kernel.share, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Mechanisms run on separate funds conserve the combined total. -/
theorem parallel_mass (K L : Kernel ι) (x y : ι → ℝ) :
    mass (transport K x + transport L y) = mass x + mass y := by
  simp only [mass, Pi.add_apply, Finset.sum_add_distrib]
  have hx := FiniteMassTransport.transport_mass K x
  have hy := FiniteMassTransport.transport_mass L y
  simp only [mass] at hx hy
  rw [hx, hy]

end Mettapedia.CogArch.Attention.ImportanceDiffusion
