import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The free lattice Maxwell field does not cluster exponentially

As `β → ∞` the fluctuations of weakly coupled `U(1)` lattice gauge theory,
rescaled by `√β`, become the free lattice Maxwell field on `ℤ⁴`: the Gaussian
field with action `½ ∑_{x, μ<ν} F_{μν}(x)²`, where
`F_{μν} = ∇_μ A_ν - ∇_ν A_μ`.  The field strength is gauge invariant.  With
`q_μ = e^{2πi k_μ} - 1` the action in momentum space is
`|q|² |Â|² - |q̄ · Â|²` (Lagrange's identity), whose inverse on transverse
fields, taken between `F̂₀₁ = q₀ Â₁ - q₁ Â₀` on both sides, gives the symbol

`m(k) = (|q₀|² + |q₁|²) / (|q₀|² + |q₁|² + |q₂|² + |q₃|²)`

of the `F₀₁` two-point function.  That function is the sequence of Fourier
coefficients of `m` on the torus `ℝ⁴/ℤ⁴`.

The symbol is `1` on the punctured `0`-axis and `0` on the punctured `2`-axis,
and it is continuous away from the origin, so it agrees almost everywhere with
no continuous function.  An absolutely summable Fourier series converges
uniformly to a continuous function.  Hence the two-point function is not
absolutely summable, and it has no exponential bound `K e^{-μ |n|₁}` with
`μ > 0`.

The barrier lemma `not_summable_norm_mFourierCoeff` holds on any torus: a
square-integrable function that is continuous on an open set and has two
different limits at one point along two subsets of that set has Fourier
coefficients that are not absolutely summable.  It applies to every candidate
two-point function whose symbol has direction-dependent limits at zero
momentum.
-/

set_option autoImplicit false
noncomputable section

open scoped ENNReal Topology
open Set Filter MeasureTheory UnitAddTorus

namespace Mettapedia.QuantumTheory.YangMills.FreeMaxwellNonClustering

attribute [local instance high] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section General

variable {d : Type*} [Fintype d]

/-- If the Fourier coefficients of a square-integrable function on the torus are
absolutely summable, the function agrees almost everywhere with a continuous one:
its Fourier series converges uniformly. -/
theorem ae_eq_continuous_of_summable_norm {f : UnitAddTorus d → ℂ}
    (hf : MemLp f 2 volume) (hsum : Summable fun n => ‖mFourierCoeff f n‖) :
    ∃ g : C(UnitAddTorus d, ℂ), f =ᵐ[volume] g := by
  have hsumC : Summable fun n => mFourierCoeff f n • mFourier n := by
    refine Summable.of_norm ?_
    simpa [norm_smul, mFourier_norm] using hsum
  obtain ⟨g, hg⟩ := hsumC
  refine ⟨g, ?_⟩
  set F : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := hf.toLp f
  have hcoeff (n : d → ℤ) : mFourierCoeff (F : UnitAddTorus d → ℂ) n = mFourierCoeff f n := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hF := hasSum_mFourier_series_L2 F
  simp only [hcoeff] at hF
  have hG : HasSum (fun n => mFourierCoeff f n • mFourierLp 2 n)
      (ContinuousMap.toLp (E := ℂ) 2 volume ℂ g) := by
    have := hg.map (ContinuousMap.toLp (E := ℂ) 2 volume ℂ)
      (ContinuousMap.toLp (E := ℂ) 2 volume ℂ).continuous
    simpa [Function.comp_def, map_smul] using this
  have hFG : F = ContinuousMap.toLp (E := ℂ) 2 volume ℂ g := hF.unique hG
  have h1 : (F : UnitAddTorus d → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have h2 : (ContinuousMap.toLp (E := ℂ) 2 volume ℂ g : UnitAddTorus d → ℂ) =ᵐ[volume] g :=
    ContinuousMap.coeFn_toLp (μ := volume) (p := 2) (𝕜 := ℂ) g
  rw [hFG] at h1
  exact h1.symm.trans h2

/-- **Barrier lemma.**  A square-integrable function on the torus that is
continuous on an open set `U` and has two different limits at one point along
two subsets of `U` has Fourier coefficients that are not absolutely summable. -/
theorem not_summable_norm_mFourierCoeff {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume)
    {U : Set (UnitAddTorus d)} (hU : IsOpen U) (hfU : ContinuousOn f U)
    {x₀ : UnitAddTorus d} {S₁ S₂ : Set (UnitAddTorus d)} (hS₁ : S₁ ⊆ U) (hS₂ : S₂ ⊆ U)
    [(𝓝[S₁] x₀).NeBot] [(𝓝[S₂] x₀).NeBot] {a₁ a₂ : ℂ}
    (hlim₁ : Tendsto f (𝓝[S₁] x₀) (𝓝 a₁)) (hlim₂ : Tendsto f (𝓝[S₂] x₀) (𝓝 a₂))
    (ha : a₁ ≠ a₂) :
    ¬ Summable fun n => ‖mFourierCoeff f n‖ := by
  intro hsum
  obtain ⟨g, hfg⟩ := ae_eq_continuous_of_summable_norm hf hsum
  have heq : EqOn f g U :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hfg) hU hfU g.continuous.continuousOn
  have hvalue (S : Set (UnitAddTorus d)) (hS : S ⊆ U) (a : ℂ) [(𝓝[S] x₀).NeBot]
      (hlim : Tendsto f (𝓝[S] x₀) (𝓝 a)) : a = g x₀ := by
    have hlim' : Tendsto g (𝓝[S] x₀) (𝓝 a) :=
      hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => heq (hS hx))
    exact tendsto_nhds_unique hlim' ((g.continuous.tendsto x₀).mono_left nhdsWithin_le_nhds)
  exact ha ((hvalue S₁ hS₁ a₁ hlim₁).trans (hvalue S₂ hS₂ a₂ hlim₂).symm)

end General

section FreeMaxwell

/-- `k̂_μ² = |e^{2πi x_μ} - 1|²`, the squared lattice momentum in direction `μ`. -/
def momentumSq (μ : Fin 4) (x : UnitAddTorus (Fin 4)) : ℝ :=
  ‖fourier 1 (x μ) - 1‖ ^ 2

theorem continuous_momentumSq (μ : Fin 4) : Continuous (momentumSq μ) :=
  ((((fourier 1).continuous.comp (continuous_apply μ)).sub continuous_const).norm).pow 2

theorem momentumSq_of_eq_zero {μ : Fin 4} {x : UnitAddTorus (Fin 4)} (h : x μ = 0) :
    momentumSq μ x = 0 := by
  simp [momentumSq, h]

theorem momentumSq_pos {μ : Fin 4} {x : UnitAddTorus (Fin 4)} (h : x μ ≠ 0) :
    0 < momentumSq μ x := by
  have hne : fourier 1 (x μ) ≠ 1 := by
    intro hone
    rw [fourier_one] at hone
    have hcircle : AddCircle.toCircle (x μ) = AddCircle.toCircle (0 : UnitAddCircle) := by
      ext
      simpa [AddCircle.toCircle_zero] using hone
    exact h (AddCircle.injective_toCircle one_ne_zero hcircle)
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2

theorem momentumSq_nonneg (μ : Fin 4) (x : UnitAddTorus (Fin 4)) : 0 ≤ momentumSq μ x :=
  sq_nonneg _

/-- `|k̂|² = k̂₀² + k̂₁² + k̂₂² + k̂₃²`. -/
def momentumSqTotal (x : UnitAddTorus (Fin 4)) : ℝ :=
  momentumSq 0 x + momentumSq 1 x + momentumSq 2 x + momentumSq 3 x

theorem continuous_momentumSqTotal : Continuous momentumSqTotal :=
  (((continuous_momentumSq 0).add (continuous_momentumSq 1)).add
    (continuous_momentumSq 2)).add (continuous_momentumSq 3)

/-- The Fourier symbol `(k̂₀² + k̂₁²)/|k̂|²` of the `F₀₁` two-point function of the
free lattice Maxwell field (set to `0` at `k = 0`, a null set). -/
def symbol (x : UnitAddTorus (Fin 4)) : ℝ :=
  (momentumSq 0 x + momentumSq 1 x) / momentumSqTotal x

/-- The `F₀₁` two-point function of the free lattice Maxwell field on `ℤ⁴`. -/
def fieldStrengthCorrelation (n : Fin 4 → ℤ) : ℂ :=
  mFourierCoeff (fun x => (symbol x : ℂ)) n

theorem symbol_mem_Icc (x : UnitAddTorus (Fin 4)) : symbol x ∈ Icc (0 : ℝ) 1 := by
  have h0 := momentumSq_nonneg 0 x
  have h1 := momentumSq_nonneg 1 x
  have h2 := momentumSq_nonneg 2 x
  have h3 := momentumSq_nonneg 3 x
  refine ⟨div_nonneg (by linarith) (by unfold momentumSqTotal; linarith), ?_⟩
  rcases eq_or_lt_of_le (show 0 ≤ momentumSqTotal x by unfold momentumSqTotal; linarith)
    with htotal | htotal
  · simp [symbol, ← htotal]
  · exact (div_le_one htotal).mpr (by unfold momentumSqTotal; linarith)

theorem symbol_memLp : MemLp (fun x => (symbol x : ℂ)) 2 volume := by
  have hmeas : Measurable symbol :=
    (((continuous_momentumSq 0).add (continuous_momentumSq 1)).measurable).div
      continuous_momentumSqTotal.measurable
  refine MemLp.of_bound (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable 1
    (ae_of_all _ fun x => ?_)
  have hx := symbol_mem_Icc x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hx.1], hx.2⟩

/-- Momenta away from the origin. -/
def momentumOffOrigin : Set (UnitAddTorus (Fin 4)) := {x | momentumSqTotal x ≠ 0}

theorem isOpen_momentumOffOrigin : IsOpen momentumOffOrigin :=
  isOpen_ne_fun continuous_momentumSqTotal continuous_const

theorem continuousOn_symbol :
    ContinuousOn (fun x => (symbol x : ℂ)) momentumOffOrigin :=
  Complex.continuous_ofReal.comp_continuousOn
    ((((continuous_momentumSq 0).add (continuous_momentumSq 1)).continuousOn).div
      continuous_momentumSqTotal.continuousOn fun _ hx => hx)

/-- The punctured `0`-axis. -/
def axisZero : Set (UnitAddTorus (Fin 4)) := {x | x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 0 ≠ 0}

/-- The punctured `2`-axis. -/
def axisTwo : Set (UnitAddTorus (Fin 4)) := {x | x 0 = 0 ∧ x 1 = 0 ∧ x 3 = 0 ∧ x 2 ≠ 0}

theorem symbol_axisZero {x : UnitAddTorus (Fin 4)} (hx : x ∈ axisZero) :
    momentumSqTotal x ≠ 0 ∧ symbol x = 1 := by
  obtain ⟨h1, h2, h3, h0⟩ := hx
  have hpos := momentumSq_pos h0
  have htotal : momentumSqTotal x = momentumSq 0 x := by
    simp [momentumSqTotal, momentumSq_of_eq_zero h1, momentumSq_of_eq_zero h2,
      momentumSq_of_eq_zero h3]
  refine ⟨by rw [htotal]; exact hpos.ne', ?_⟩
  rw [symbol, htotal, momentumSq_of_eq_zero h1, add_zero, div_self hpos.ne']

theorem symbol_axisTwo {x : UnitAddTorus (Fin 4)} (hx : x ∈ axisTwo) :
    momentumSqTotal x ≠ 0 ∧ symbol x = 0 := by
  obtain ⟨h0, h1, h3, h2⟩ := hx
  have hpos := momentumSq_pos h2
  have htotal : momentumSqTotal x = momentumSq 2 x := by
    simp [momentumSqTotal, momentumSq_of_eq_zero h0, momentumSq_of_eq_zero h1,
      momentumSq_of_eq_zero h3]
  refine ⟨by rw [htotal]; exact hpos.ne', ?_⟩
  rw [symbol, momentumSq_of_eq_zero h0, momentumSq_of_eq_zero h1, add_zero, zero_div]

theorem coe_ne_zero_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (t : UnitAddCircle) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  have h0 : (0 : ℝ) < n := hn ▸ ht.1
  have h1 : (n : ℝ) < 1 := hn ▸ ht.2
  have h0' : 0 < n := by exact_mod_cast h0
  have h1' : n < 1 := by exact_mod_cast h1
  omega

theorem neBot_axis (μ : Fin 4) (S : Set (UnitAddTorus (Fin 4)))
    (hS : ∀ t ∈ Ioo (0 : ℝ) 1, (Pi.single μ (t : UnitAddCircle) : UnitAddTorus (Fin 4)) ∈ S) :
    (𝓝[S] (0 : UnitAddTorus (Fin 4))).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  have hcont : Continuous fun t : ℝ =>
      (Pi.single μ (t : UnitAddCircle) : UnitAddTorus (Fin 4)) :=
    (continuous_single μ).comp continuous_quotient_mk'
  have htend : Tendsto (fun t : ℝ => (Pi.single μ (t : UnitAddCircle) : UnitAddTorus (Fin 4)))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  exact mem_closure_of_tendsto htend
    (Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) hS)

instance neBot_axisZero : (𝓝[axisZero] (0 : UnitAddTorus (Fin 4))).NeBot :=
  neBot_axis 0 axisZero fun t ht => by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [coe_ne_zero_of_mem_Ioo ht]

instance neBot_axisTwo : (𝓝[axisTwo] (0 : UnitAddTorus (Fin 4))).NeBot :=
  neBot_axis 2 axisTwo fun t ht => by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [coe_ne_zero_of_mem_Ioo ht]

/-- **The free lattice Maxwell field does not cluster.**  The `F₀₁` two-point
function of the free lattice Maxwell field on `ℤ⁴` is not absolutely summable. -/
theorem not_summable_norm_fieldStrengthCorrelation :
    ¬ Summable fun n => ‖fieldStrengthCorrelation n‖ := by
  refine not_summable_norm_mFourierCoeff symbol_memLp isOpen_momentumOffOrigin
    continuousOn_symbol (x₀ := 0) (S₁ := axisZero) (S₂ := axisTwo)
    (fun x hx => (symbol_axisZero hx).1) (fun x hx => (symbol_axisTwo hx).1)
    (a₁ := 1) (a₂ := 0) ?_ ?_ one_ne_zero
  · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    simp [(symbol_axisZero hx).2]
  · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    simp [(symbol_axisTwo hx).2]

theorem summable_exp_neg_abs {μ : ℝ} (hμ : 0 < μ) :
    Summable fun z : ℤ => Real.exp (-μ * |(z : ℝ)|) := by
  have hgeom : Summable fun n : ℕ => Real.exp (-μ) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_nat_of_neg
  · refine hgeom.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  · refine hgeom.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    ring

theorem summable_prod_pi {a : ℤ → ℝ} (h0 : ∀ z, 0 ≤ a z) (ha : Summable a) :
    ∀ k : ℕ, Summable fun n : Fin k → ℤ => ∏ i, a (n i)
  | 0 => Summable.of_finite
  | k + 1 => by
    have hprod := Summable.mul_of_nonneg ha (summable_prod_pi h0 ha k) (fun z => h0 z)
      (fun n => Finset.prod_nonneg fun i _ => h0 (n i))
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => ℤ).summable_iff]
    refine hprod.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- In particular the two-point function has no exponential bound. -/
theorem not_exponentialDecay_fieldStrengthCorrelation (K μ : ℝ) (hμ : 0 < μ) :
    ¬ ∀ n : Fin 4 → ℤ,
      ‖fieldStrengthCorrelation n‖ ≤ K * Real.exp (-μ * ∑ i, |((n i : ℤ) : ℝ)|) := by
  intro hbound
  apply not_summable_norm_fieldStrengthCorrelation
  have hexp : Summable fun n : Fin 4 → ℤ => Real.exp (-μ * ∑ i, |((n i : ℤ) : ℝ)|) := by
    refine (summable_prod_pi (a := fun z : ℤ => Real.exp (-μ * |(z : ℝ)|))
      (fun z => (Real.exp_pos _).le) (summable_exp_neg_abs hμ) 4).congr fun n => ?_
    rw [Finset.mul_sum, Real.exp_sum]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hexp.mul_left K)

end FreeMaxwell

#print axioms not_summable_norm_mFourierCoeff
#print axioms not_summable_norm_fieldStrengthCorrelation
#print axioms not_exponentialDecay_fieldStrengthCorrelation

end Mettapedia.QuantumTheory.YangMills.FreeMaxwellNonClustering
