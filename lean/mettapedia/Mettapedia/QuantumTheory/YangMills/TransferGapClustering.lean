import Mettapedia.QuantumTheory.YangMills.FiniteOSReconstruction
import Mettapedia.QuantumTheory.YangMills.Clustering
import Mathlib.Tactic

/-!
# Transfer Spectral Gap implies Clustering (finite OS setting)

The abstract finite-dimensional half of the OS gap/clustering equivalence:

* **Gap ⟹ clustering.**  For a reflection-positive symmetric finite kernel
  with a self-adjoint linear transfer operator, a normalized invariant vacuum,
  and a one-step contraction by `q` on the vacuum-orthogonal complement, the
  truncated two-point function `⟨f, Tⁿ g⟩ - ⟨f, Ω⟩⟨Ω, g⟩` decays like `qⁿ`,
  i.e. exponentially at rate `-log q` — the transfer gap.
  (`truncatedTwoPoint_sq_le`, `abs_truncatedTwoPoint_le_exp`.)

* **Moments ⟹ gap, per-vector constants.**  Conversely, a per-vector moment
  bound `⟨v, Tⁿ v⟩ ≤ C_v qⁿ` on a single normalizable eigenvector forces its
  eigenvalue below `q`; only the rate is uniform, the constant may depend on
  the vector.  (`eigenvalue_abs_le_of_moment_decay`.)

* **Additive tails defeat the moment route.**  The same conclusion FAILS if
  the moment bound carries an additive constant `+ δ`:
  `moment_decay_additive_defeat` exhibits the identity transfer with
  eigenvalue `1` satisfying `⟨v, Tⁿ v⟩ ≤ 0 * (1/2)ⁿ + 1`.  This pins the
  audit point that large-field remainders must not survive as `t`-independent
  additive errors in correlation bounds.

Everything is finite linear algebra over a `Fintype` of configurations; no
continuum statement is made.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

universe u

variable {Ω : Type u} [Fintype Ω]

/-! ## Bilinearity of the finite OS pairing -/

theorem osBilinearForm_add_left (K : Ω → Ω → ℝ)
    (f g h : FiniteObservable Ω) :
    osBilinearForm K (f + g) h
      = osBilinearForm K f h + osBilinearForm K g h := by
  unfold osBilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.add_apply]
  ring

theorem osBilinearForm_add_right (K : Ω → Ω → ℝ)
    (f g h : FiniteObservable Ω) :
    osBilinearForm K f (g + h)
      = osBilinearForm K f g + osBilinearForm K f h := by
  unfold osBilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.add_apply]
  ring

theorem osBilinearForm_smul_left (K : Ω → Ω → ℝ) (a : ℝ)
    (f g : FiniteObservable Ω) :
    osBilinearForm K (a • f) g = a * osBilinearForm K f g := by
  unfold osBilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem osBilinearForm_smul_right (K : Ω → Ω → ℝ) (a : ℝ)
    (f g : FiniteObservable Ω) :
    osBilinearForm K f (a • g) = a * osBilinearForm K f g := by
  unfold osBilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem osBilinearForm_sub_right (K : Ω → Ω → ℝ)
    (f g h : FiniteObservable Ω) :
    osBilinearForm K f (g - h)
      = osBilinearForm K f g - osBilinearForm K f h := by
  unfold osBilinearForm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.sub_apply]
  ring

/-! ## Cauchy-Schwarz for a reflection-positive symmetric pairing -/

/-- Cauchy-Schwarz holds for any positive-semidefinite symmetric finite OS
pairing; definiteness is not needed. -/
theorem osBilinearForm_sq_le_mul_self
    {K : Ω → Ω → ℝ}
    (hpos : OSReflectionPositive K) (hsym : OSSymmetric K)
    (f g : FiniteObservable Ω) :
    (osBilinearForm K f g) ^ 2
      ≤ osBilinearForm K f f * osBilinearForm K g g := by
  have hexp : ∀ t : ℝ,
      0 ≤ osBilinearForm K f f + 2 * t * osBilinearForm K f g
        + t ^ 2 * osBilinearForm K g g := by
    intro t
    have h := hpos (f + t • g)
    have hexpand : osBilinearForm K (f + t • g) (f + t • g)
        = osBilinearForm K f f + 2 * t * osBilinearForm K f g
          + t ^ 2 * osBilinearForm K g g := by
      rw [osBilinearForm_add_left, osBilinearForm_add_right,
        osBilinearForm_add_right, osBilinearForm_smul_left,
        osBilinearForm_smul_right, osBilinearForm_smul_left,
        osBilinearForm_smul_right, hsym g f]
      ring
    rw [hexpand] at h
    exact h
  rcases eq_or_lt_of_le (hpos g) with hg0 | hgpos
  · -- degenerate direction: `⟨g, g⟩ = 0` forces `⟨f, g⟩ = 0`
    have hb0 : osBilinearForm K f g = 0 := by
      by_contra hbne
      have hbne' : osBilinearForm K f g ≠ 0 := hbne
      have h := hexp
        (-(osBilinearForm K f f + 1) / (2 * osBilinearForm K f g))
      rw [← hg0] at h
      have h2b : 2 * (-(osBilinearForm K f f + 1)
            / (2 * osBilinearForm K f g)) * osBilinearForm K f g
          = -(osBilinearForm K f f + 1) := by
        field_simp
      rw [h2b] at h
      have hzero : (-(osBilinearForm K f f + 1)
          / (2 * osBilinearForm K f g)) ^ 2 * 0 = 0 := by
        ring
      rw [hzero] at h
      linarith
    rw [hb0, ← hg0]
    norm_num
  · have hcne : osBilinearForm K g g ≠ 0 := ne_of_gt hgpos
    have h := hexp (-osBilinearForm K f g / osBilinearForm K g g)
    have hkey : osBilinearForm K f f
        + 2 * (-osBilinearForm K f g / osBilinearForm K g g)
          * osBilinearForm K f g
        + (-osBilinearForm K f g / osBilinearForm K g g) ^ 2
          * osBilinearForm K g g
        = osBilinearForm K f f
          - osBilinearForm K f g ^ 2 / osBilinearForm K g g := by
      field_simp
      ring
    rw [hkey] at h
    have hdiv : osBilinearForm K f g ^ 2 / osBilinearForm K g g
        ≤ osBilinearForm K f f := by linarith
    calc osBilinearForm K f g ^ 2
        = osBilinearForm K f g ^ 2 / osBilinearForm K g g
            * osBilinearForm K g g := (div_mul_cancel₀ _ hcne).symm
      _ ≤ osBilinearForm K f f * osBilinearForm K g g :=
          mul_le_mul_of_nonneg_right hdiv hgpos.le

/-! ## The normalized transfer-gap system -/

/-- A finite reflection-positive transfer system with normalized invariant
vacuum and a one-step spectral-gap contraction on the vacuum-orthogonal
complement.  The field `gapContraction` is the finite-dimensional content of
"the transfer matrix has spectral gap `-log q` above the vacuum". -/
structure NormalizedTransferGapSystem (Ω : Type u) [Fintype Ω] where
  K : Ω → Ω → ℝ
  T : FiniteObservable Ω → FiniteObservable Ω
  vac : FiniteObservable Ω
  q : ℝ
  reflectionPositive : OSReflectionPositive K
  symmetric : OSSymmetric K
  selfAdjoint : OSTransferSelfAdjoint K T
  Tadd : ∀ f g : FiniteObservable Ω, T (f + g) = T f + T g
  Tsmul : ∀ (a : ℝ) (f : FiniteObservable Ω), T (a • f) = a • T f
  vacInvariant : T vac = vac
  vacNormalized : osBilinearForm K vac vac = 1
  qNonneg : 0 ≤ q
  gapContraction : ∀ f : FiniteObservable Ω,
    osBilinearForm K vac f = 0 →
      osBilinearForm K (T f) (T f) ≤ q ^ 2 * osBilinearForm K f f

variable (S : NormalizedTransferGapSystem Ω)

/-- Vacuum component of an observable. -/
def vacuumComponent (f : FiniteObservable Ω) : ℝ :=
  osBilinearForm S.K S.vac f

/-- Vacuum-subtracted (connected) part of an observable. -/
def vacuumSubtract (f : FiniteObservable Ω) : FiniteObservable Ω :=
  f - vacuumComponent S f • S.vac

/-- Truncated (connected) two-point function at time separation `n`. -/
def truncatedTwoPoint (f g : FiniteObservable Ω) (n : ℕ) : ℝ :=
  osBilinearForm S.K f (S.T^[n] g)
    - osBilinearForm S.K f S.vac * osBilinearForm S.K S.vac g

/-- The transfer mass gap: `-log q`. -/
def transferMassGap : ℝ :=
  -Real.log S.q

theorem vacuumSubtract_orthogonal (f : FiniteObservable Ω) :
    osBilinearForm S.K S.vac (vacuumSubtract S f) = 0 := by
  unfold vacuumSubtract
  rw [osBilinearForm_sub_right, osBilinearForm_smul_right, S.vacNormalized]
  unfold vacuumComponent
  ring

/-- The transfer preserves orthogonality to the vacuum. -/
theorem transfer_preserves_vacuum_orthogonal
    {f : FiniteObservable Ω}
    (h : osBilinearForm S.K S.vac f = 0) :
    osBilinearForm S.K S.vac (S.T f) = 0 := by
  calc osBilinearForm S.K S.vac (S.T f)
      = osBilinearForm S.K (S.T f) S.vac := S.symmetric _ _
    _ = osBilinearForm S.K f (S.T S.vac) := S.selfAdjoint f S.vac
    _ = osBilinearForm S.K f S.vac := by rw [S.vacInvariant]
    _ = osBilinearForm S.K S.vac f := S.symmetric _ _
    _ = 0 := h

theorem iterate_preserves_vacuum_orthogonal
    {f : FiniteObservable Ω}
    (h : osBilinearForm S.K S.vac f = 0) (n : ℕ) :
    osBilinearForm S.K S.vac (S.T^[n] f) = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact transfer_preserves_vacuum_orthogonal S ih

/-- The iterated transfer contracts the vacuum-orthogonal complement by
`qⁿ` in the OS norm. -/
theorem iterate_gapContraction
    {f : FiniteObservable Ω}
    (h : osBilinearForm S.K S.vac f = 0) (n : ℕ) :
    osBilinearForm S.K (S.T^[n] f) (S.T^[n] f)
      ≤ (S.q ^ n) ^ 2 * osBilinearForm S.K f f := by
  induction n with
  | zero => simp
  | succ n ih =>
      have horth := iterate_preserves_vacuum_orthogonal S h n
      have hstep := S.gapContraction (S.T^[n] f) horth
      have hq2 : (0 : ℝ) ≤ S.q ^ 2 := sq_nonneg _
      calc osBilinearForm S.K (S.T^[n + 1] f) (S.T^[n + 1] f)
          = osBilinearForm S.K (S.T (S.T^[n] f)) (S.T (S.T^[n] f)) := by
            rw [Function.iterate_succ_apply']
        _ ≤ S.q ^ 2 * osBilinearForm S.K (S.T^[n] f) (S.T^[n] f) := hstep
        _ ≤ S.q ^ 2 * ((S.q ^ n) ^ 2 * osBilinearForm S.K f f) :=
            mul_le_mul_of_nonneg_left ih hq2
        _ = (S.q ^ (n + 1)) ^ 2 * osBilinearForm S.K f f := by
            rw [pow_succ]
            ring

/-- The iterated transfer fixes an added vacuum component. -/
theorem iterate_add_vacuum
    (f : FiniteObservable Ω) (a : ℝ) (n : ℕ) :
    S.T^[n] (f + a • S.vac) = S.T^[n] f + a • S.vac := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, S.Tadd, S.Tsmul, S.vacInvariant,
        Function.iterate_succ_apply']

/-- The truncated two-point function is exactly the pairing of the
vacuum-subtracted parts through the iterated transfer. -/
theorem truncatedTwoPoint_eq
    (f g : FiniteObservable Ω) (n : ℕ) :
    truncatedTwoPoint S f g n
      = osBilinearForm S.K (vacuumSubtract S f)
          (S.T^[n] (vacuumSubtract S g)) := by
  have hfdecomp : f = vacuumSubtract S f + vacuumComponent S f • S.vac := by
    funext x
    simp only [vacuumSubtract, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hgdecomp : g = vacuumSubtract S g + vacuumComponent S g • S.vac := by
    funext x
    simp only [vacuumSubtract, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hTg : S.T^[n] g
      = S.T^[n] (vacuumSubtract S g) + vacuumComponent S g • S.vac := by
    conv_lhs => rw [hgdecomp]
    exact iterate_add_vacuum S (vacuumSubtract S g) (vacuumComponent S g) n
  have horthf : osBilinearForm S.K (vacuumSubtract S f) S.vac = 0 := by
    rw [S.symmetric]
    exact vacuumSubtract_orthogonal S f
  have horthTg :
      osBilinearForm S.K S.vac (S.T^[n] (vacuumSubtract S g)) = 0 :=
    iterate_preserves_vacuum_orthogonal S (vacuumSubtract_orthogonal S g) n
  have hfvac : osBilinearForm S.K f S.vac = vacuumComponent S f :=
    S.symmetric f S.vac
  have hexpand : osBilinearForm S.K f (S.T^[n] g)
      = osBilinearForm S.K (vacuumSubtract S f)
          (S.T^[n] (vacuumSubtract S g))
        + vacuumComponent S f * vacuumComponent S g := by
    conv_lhs => rw [hfdecomp, hTg]
    rw [osBilinearForm_add_left, osBilinearForm_add_right,
      osBilinearForm_add_right, osBilinearForm_smul_right,
      osBilinearForm_smul_left, osBilinearForm_smul_left,
      osBilinearForm_smul_right, horthf, horthTg, S.vacNormalized]
    ring
  unfold truncatedTwoPoint
  rw [hexpand, hfvac]
  unfold vacuumComponent
  ring

/-- **Gap implies clustering, squared form.**  The truncated two-point
function at time separation `n` is bounded by `q^(2n)` times the product of
the connected OS norms. -/
theorem truncatedTwoPoint_sq_le
    (f g : FiniteObservable Ω) (n : ℕ) :
    truncatedTwoPoint S f g n ^ 2
      ≤ (S.q ^ n) ^ 2 *
        (osBilinearForm S.K (vacuumSubtract S f) (vacuumSubtract S f) *
          osBilinearForm S.K (vacuumSubtract S g) (vacuumSubtract S g)) := by
  rw [truncatedTwoPoint_eq]
  have hcs := osBilinearForm_sq_le_mul_self S.reflectionPositive S.symmetric
    (vacuumSubtract S f) (S.T^[n] (vacuumSubtract S g))
  have hcontr := iterate_gapContraction S (vacuumSubtract_orthogonal S g) n
  have hf0 : 0 ≤ osBilinearForm S.K (vacuumSubtract S f)
      (vacuumSubtract S f) :=
    S.reflectionPositive _
  nlinarith [hcs, hcontr, hf0, mul_le_mul_of_nonneg_left hcontr hf0]

/-- The connected clustering prefactor for a pair of observables. -/
def clusteringPrefactor (f g : FiniteObservable Ω) : ℝ :=
  Real.sqrt
    (osBilinearForm S.K (vacuumSubtract S f) (vacuumSubtract S f) *
      osBilinearForm S.K (vacuumSubtract S g) (vacuumSubtract S g))

theorem clusteringPrefactor_nonneg (f g : FiniteObservable Ω) :
    0 ≤ clusteringPrefactor S f g :=
  Real.sqrt_nonneg _

/-- **Gap implies clustering.**  Absolute-value form with the explicit
prefactor. -/
theorem abs_truncatedTwoPoint_le
    (f g : FiniteObservable Ω) (n : ℕ) :
    |truncatedTwoPoint S f g n|
      ≤ clusteringPrefactor S f g * S.q ^ n := by
  have hsq := truncatedTwoPoint_sq_le S f g n
  have hqn : (0 : ℝ) ≤ S.q ^ n := pow_nonneg S.qNonneg n
  calc |truncatedTwoPoint S f g n|
      = Real.sqrt (truncatedTwoPoint S f g n ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((S.q ^ n) ^ 2 *
          (osBilinearForm S.K (vacuumSubtract S f) (vacuumSubtract S f) *
            osBilinearForm S.K (vacuumSubtract S g) (vacuumSubtract S g))) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((S.q ^ n) ^ 2) * clusteringPrefactor S f g := by
        rw [Real.sqrt_mul (sq_nonneg _)]
        rfl
    _ = clusteringPrefactor S f g * S.q ^ n := by
        rw [Real.sqrt_sq hqn]
        ring

/-- **Gap implies clustering, exponential form.**  For positive `q` the decay
rate is exactly the transfer mass gap `-log q`. -/
theorem abs_truncatedTwoPoint_le_exp
    (hq : 0 < S.q) (f g : FiniteObservable Ω) (n : ℕ) :
    |truncatedTwoPoint S f g n|
      ≤ clusteringPrefactor S f g
        * Real.exp (-transferMassGap S * n) := by
  have hqe : S.q ^ n = Real.exp (-transferMassGap S * (n : ℝ)) := by
    have h1 : -transferMassGap S * (n : ℝ) = (n : ℝ) * Real.log S.q := by
      unfold transferMassGap
      ring
    rw [h1, Real.exp_nat_mul, Real.exp_log hq]
  rw [← hqe]
  exact abs_truncatedTwoPoint_le S f g n

/-! ## Converse: per-vector moment decay forces the eigenvalue bound -/

/-- **Moment decay implies eigenvalue bound (per-vector constants).**  If a
normalizable eigenvector has moments `⟨v, Tⁿ v⟩ ≤ C_v qⁿ` for a constant
`C_v` that may depend on `v`, then its eigenvalue satisfies `|μ| ≤ q`.  Only
the rate `q` is uniform; this is the per-vector weakening of the uniform
moment hypotheses. -/
theorem eigenvalue_abs_le_of_moment_decay
    {K : Ω → Ω → ℝ}
    {T : FiniteObservable Ω → FiniteObservable Ω}
    {v : FiniteObservable Ω} {μ q Cv : ℝ}
    (hq : 0 ≤ q)
    (heig : T v = μ • v)
    (hTsmul : ∀ (a : ℝ) (w : FiniteObservable Ω), T (a • w) = a • T w)
    (hvpos : 0 < osBilinearForm K v v)
    (hmom : ∀ n : ℕ, osBilinearForm K v (T^[n] v) ≤ Cv * q ^ n) :
    |μ| ≤ q := by
  have hiter : ∀ n : ℕ, T^[n] v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTsmul, heig, smul_smul,
          pow_succ]
  by_contra habs
  push Not at habs
  have hμsq : q ^ 2 < μ ^ 2 := by
    have h1 : q ^ 2 < |μ| ^ 2 := by nlinarith [habs, hq, abs_nonneg μ]
    calc q ^ 2 < |μ| ^ 2 := h1
      _ = μ ^ 2 := sq_abs μ
  have hgrow : ∀ n : ℕ,
      (μ ^ 2) ^ n * osBilinearForm K v v ≤ Cv * (q ^ 2) ^ n := by
    intro n
    have h := hmom (2 * n)
    rw [hiter (2 * n), osBilinearForm_smul_right] at h
    calc (μ ^ 2) ^ n * osBilinearForm K v v
        = μ ^ (2 * n) * osBilinearForm K v v := by rw [← pow_mul]
      _ ≤ Cv * q ^ (2 * n) := h
      _ = Cv * (q ^ 2) ^ n := by rw [← pow_mul]
  rcases eq_or_lt_of_le (sq_nonneg q) with hq0 | hqpos
  · -- `q² = 0`: the first even moment already forces `μ² ≤ 0`
    have h1 := hgrow 1
    rw [← hq0] at h1
    have hμpos : 0 < μ ^ 2 := by
      rw [← hq0] at hμsq
      exact hμsq
    nlinarith [h1, hvpos, hμpos]
  · -- `q² > 0`: geometric growth of `(μ²/q²)ⁿ` beats the fixed bound
    have hr : 1 < μ ^ 2 / q ^ 2 := (one_lt_div hqpos).mpr hμsq
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
      (Cv / osBilinearForm K v v) hr
    have hqn : 0 < (q ^ 2) ^ n := pow_pos hqpos n
    have hle : (μ ^ 2 / q ^ 2) ^ n ≤ Cv / osBilinearForm K v v := by
      rw [div_pow, div_le_div_iff₀ hqn hvpos]
      exact hgrow n
    exact absurd hle (not_le.mpr hn)

/-- **Additive tails defeat the moment argument.**  The identity transfer on
a single site has eigenvalue `1`, positive pairing, and satisfies the
`δ`-shifted moment bound `⟨v, Tⁿ v⟩ ≤ 0 * (1/2)ⁿ + 1`, yet `1 > 1/2`: an
additive `t`-independent error in the moment bound destroys the gap
conclusion. -/
theorem moment_decay_additive_defeat :
    ∃ (K : Fin 1 → Fin 1 → ℝ)
      (T : FiniteObservable (Fin 1) → FiniteObservable (Fin 1))
      (v : FiniteObservable (Fin 1)) (μ q Cv δ : ℝ),
      0 ≤ q ∧ 0 < δ ∧
      T v = μ • v ∧
      (∀ (a : ℝ) (w : FiniteObservable (Fin 1)), T (a • w) = a • T w) ∧
      0 < osBilinearForm K v v ∧
      (∀ n : ℕ, osBilinearForm K v (T^[n] v) ≤ Cv * q ^ n + δ) ∧
      q < |μ| := by
  refine ⟨fun _ _ => 1, id, fun _ => 1, 1, 1 / 2, 0, 1,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    simp
  · intro a w
    rfl
  · norm_num [osBilinearForm]
  · intro n
    norm_num [osBilinearForm, Function.iterate_id]
  · norm_num

/-! ## Prefactor absorption for spatial clustering -/

/-- A uniform bound `|corr x y| ≤ A * exp (-m * dist x y)` with any constant
prefactor `A` yields `HasExponentialClusteringAtRate` at every rate strictly
below `m`: beyond a finite radius the prefactor is absorbed into the rate
slack. -/
theorem hasExponentialClusteringAtRate_of_uniform_exp_bound
    {corr : SpatialCorrelation} {A m C : ℝ}
    (hCm : C < m)
    (hbound : ∀ x y : Space, |corr x y| ≤ A * Real.exp (-m * dist x y)) :
    HasExponentialClusteringAtRate corr C := by
  set A' := max A 1 with hA'
  have hA1 : (1 : ℝ) ≤ A' := le_max_right _ _
  have hA'pos : (0 : ℝ) < A' := lt_of_lt_of_le one_pos hA1
  have hmC : 0 < m - C := sub_pos.mpr hCm
  refine ⟨max 0 (Real.log A' / (m - C)), le_max_left _ _, ?_⟩
  intro x y hR
  have hd : Real.log A' / (m - C) ≤ dist x y :=
    le_trans (le_max_right _ _) hR
  have hlog : Real.log A' ≤ (m - C) * dist x y := by
    rw [div_le_iff₀ hmC] at hd
    linarith
  have hA'le : A' ≤ Real.exp ((m - C) * dist x y) := by
    calc A' = Real.exp (Real.log A') := (Real.exp_log hA'pos).symm
      _ ≤ Real.exp ((m - C) * dist x y) := Real.exp_le_exp.mpr hlog
  calc |corr x y| ≤ A * Real.exp (-m * dist x y) := hbound x y
    _ ≤ A' * Real.exp (-m * dist x y) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    _ ≤ Real.exp ((m - C) * dist x y) * Real.exp (-m * dist x y) :=
        mul_le_mul_of_nonneg_right hA'le (Real.exp_nonneg _)
    _ = Real.exp (-C * dist x y) := by
        rw [← Real.exp_add]
        ring_nf

end YangMills
end QuantumTheory
end Mettapedia
