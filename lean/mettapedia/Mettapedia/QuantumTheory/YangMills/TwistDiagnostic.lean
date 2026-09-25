import Mettapedia.Combinatorics.PolymerGas.Twist
import Mettapedia.QuantumTheory.YangMills.CrossingInput

/-!
# The twist free energy as a diagnostic of the crossing input

On a torus, inserting a twist through a stack of plaquettes (the centre element
`-1` of `SU(2)`, or a flux `π` for `U(1)`) changes the partition function from `Z`
to `Z_tw`; `F = -log (Z_tw / Z)` is the twist free energy.  In a polymer
representation whose activities are built from plaquette factors, the twist can
be moved off any polymer that does not wind around the torus by a change of
variables that flips link variables by the centre element, so only the integrated
activities of winding polymers change.  Those meet any fixed cut through the torus
and have diameter at least a fixed fraction of the side.

`TwistCompatibleCrossing` records this situation: untwisted and twisted
activities for every volume, under common Kotecký–Preiss bounds with a positive
rate, whose integrated activities differ only on polymers of diameter at least
`D L` meeting a block set `Y L`.  Then
`|log (‖Z_tw‖ / ‖Z‖)| ≤ 2 |Y L| ε e^{-κ D L}` (`abs_logTwistRatio_le`), so the twist
free energy tends to zero when `|Y L| e^{-κ D L}` does for every `κ > 0`
(`tendsto_logTwistRatio`).  This holds for cuts of polynomial size and diameters
growing linearly in the side (`tendsto_card_mul_exp_of_poly_linear`).  The
untwisted half is a crossing input (`TwistCompatibleCrossing.crossingInput`).

**Calibration by the twist.**  A family whose twist free energy stays away from
zero admits no twist-compatible crossing input (`false_of_twistFreeEnergy_ge`;
on tori with polynomial cuts and linear winding diameters,
`false_of_twistFreeEnergy_ge_of_poly_linear`).
Unlike the calibration at `β = ∞` (`CrossingInput.false_of_tendsto_dominating`),
this one is testable at finite coupling, since the twist free energy can be
measured by Monte Carlo.  That the twist changes only winding polymers is the
hypothesis `differ`.  It follows from two properties, that moving the twist does
not change integrated activities and that polymers away from the twist do not see
it (`differ_of_movable`); these are not derived here from a lattice gauge
measure.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Filter Topology
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.TwistDiagnostic

open Mettapedia.QuantumTheory.YangMills.CrossingInput

variable {ι : Type*} (Blocks : ι → Type*) [∀ L, Fintype (Blocks L)]
  [∀ L, DecidableEq (Blocks L)] [∀ L, PseudoMetricSpace (Blocks L)]
  (E : Type*) [MeasurableSpace E] [Nonempty E] (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

/-- Untwisted activities `K` and twisted activities `Ktw` for every volume `L`,
under common per-block Kotecký–Preiss bounds with a positive rate, whose
integrated activities differ only on polymers that meet `Y L` and have diameter
at least `D L`. -/
structure TwistCompatibleCrossing (K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ)
    (Y : ∀ L, Finset (Blocks L)) (D : ι → ℝ) : Prop where
  exists_bounds : ∃ (bound : ∀ L, Finset (Blocks L) → ℝ) (rate smallness : ℝ),
    0 < rate ∧ 0 ≤ smallness ∧ smallness * Real.exp 1 ≤ 1 ∧
      (∀ L S v, ‖K L S v‖ ≤ bound L S) ∧ (∀ L S v, ‖Ktw L S v‖ ≤ bound L S) ∧
      (∀ L, bound L ∅ = 0) ∧ ∀ L, ActivitySmall (bound L) rate smallness
  differ : ∀ L (γ : Finset (Blocks L)),
    integratedActivity ν₀ (K L) γ ≠ integratedActivity ν₀ (Ktw L) γ →
      ¬ Disjoint (Y L) γ ∧ D L ≤ polymerDiam γ

variable {Blocks E ν₀}

omit [Nonempty E] [IsProbabilityMeasure ν₀] in
/-- **Where the winding hypothesis comes from.**  Let the twist sit at one of
several positions `p`, with twisted activities `Ktw p` and a set `stack p` of
blocks it touches.  If moving the twist does not change integrated activities (a
change of variables by the centre element) and a polymer disjoint from the stack
at `p` does not see the twist at `p`, then a polymer whose integrated activity
changes meets every stack; in particular it meets `stack p₀` and has diameter at
least the distance between `stack p₀` and `stack q₀`. -/
theorem differ_of_movable {X : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
    {Pos : Type*}
    (K : ∀ S : Finset X, (S → E) → ℂ) (Ktw : Pos → ∀ S : Finset X, (S → E) → ℂ)
    (stack : Pos → Finset X)
    (hmove : ∀ p q S, integratedActivity ν₀ (Ktw p) S = integratedActivity ν₀ (Ktw q) S)
    (hlocal : ∀ p S, Disjoint (stack p) S → Ktw p S = K S) (p₀ q₀ : Pos) {D₀ : ℝ}
    (hsep : ∀ a ∈ stack p₀, ∀ b ∈ stack q₀, D₀ ≤ dist a b) (γ : Finset X)
    (hne : integratedActivity ν₀ K γ ≠ integratedActivity ν₀ (Ktw p₀) γ) :
    ¬ Disjoint (stack p₀) γ ∧ D₀ ≤ polymerDiam γ := by
  have hmeet : ∀ q, ¬ Disjoint (stack q) γ := by
    intro q hq
    apply hne
    rw [hmove p₀ q γ]
    unfold integratedActivity
    rw [hlocal q γ hq]
  refine ⟨hmeet p₀, ?_⟩
  obtain ⟨a, ha₀, haγ⟩ := Finset.not_disjoint_iff.mp (hmeet p₀)
  obtain ⟨b, hb₀, hbγ⟩ := Finset.not_disjoint_iff.mp (hmeet q₀)
  exact (hsep a ha₀ b hb₀).trans (dist_le_polymerDiam haγ hbγ)

/-- The logarithm of the ratio of the moduli of the twisted and untwisted
partition functions over the polymer set `Λ`: minus the twist free energy. -/
def logTwistRatio (K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ) (L : ι)
    (Λ : Finset (Finset (Blocks L))) : ℝ :=
  Real.log (‖partitionFunction (overlapGraph (Blocks L)) (integratedActivity ν₀ (Ktw L)) Λ‖ /
    ‖partitionFunction (overlapGraph (Blocks L)) (integratedActivity ν₀ (K L)) Λ‖)

omit [Nonempty E] [IsProbabilityMeasure ν₀] in
/-- The untwisted activities of a twist-compatible family satisfy the crossing
input. -/
theorem TwistCompatibleCrossing.crossingInput
    {K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ} {Y : ∀ L, Finset (Blocks L)}
    {D : ι → ℝ} (h : TwistCompatibleCrossing Blocks E ν₀ K Ktw Y D)
    (hmeas : ∀ L S, Measurable (K L S)) : CrossingInput Blocks E K := by
  obtain ⟨bound, rate, smallness, hrate, hs0, hs, hle, _, hempty, hsmall⟩ := h.exists_bounds
  exact ⟨hmeas, bound, rate, smallness, hrate, hs0, hs, hle, hempty, hsmall⟩

/-- **The twist free energy is exponentially small.**  With constants independent
of the volume, `|log (‖Z_tw‖ / ‖Z‖)| ≤ 2 |Y L| ε e^{-κ D L}`. -/
theorem abs_logTwistRatio_le {K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ}
    {Y : ∀ L, Finset (Blocks L)} {D : ι → ℝ}
    (h : TwistCompatibleCrossing Blocks E ν₀ K Ktw Y D) :
    ∃ κ > 0, ∃ ε, 0 ≤ ε ∧ ∀ (L : ι) (Λ : Finset (Finset (Blocks L))),
      |logTwistRatio (ν₀ := ν₀) K Ktw L Λ| ≤ 2 * ((Y L).card * ε * Real.exp (-κ * D L)) := by
  obtain ⟨bound, rate, smallness, hrate, hs0, hs, hle, hle', hempty, hsmall⟩ := h.exists_bounds
  exact ⟨rate, hrate, smallness, hs0, fun L Λ =>
    abs_log_norm_partitionFunction_div_le ν₀ (K L) (Ktw L) (bound L) (hle L) (hle' L)
      (hempty L) hrate.le hs0 hs (hsmall L) Λ (Y L) (D L) (fun γ _ hne => h.differ L γ hne)⟩

/-- The twist free energy tends to zero along any filter on which
`|Y L| e^{-κ D L}` tends to zero for every `κ > 0`. -/
theorem tendsto_logTwistRatio {K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ}
    {Y : ∀ L, Finset (Blocks L)} {D : ι → ℝ}
    (h : TwistCompatibleCrossing Blocks E ν₀ K Ktw Y D) {l : Filter ι}
    (hYD : ∀ κ > 0, Tendsto (fun L => ((Y L).card : ℝ) * Real.exp (-κ * D L)) l (𝓝 0))
    (Λ : ∀ L, Finset (Finset (Blocks L))) :
    Tendsto (fun L => logTwistRatio (ν₀ := ν₀) K Ktw L (Λ L)) l (𝓝 0) := by
  obtain ⟨κ, hκ, ε, hε, hbound⟩ := abs_logTwistRatio_le h
  have hlim : Tendsto (fun L => 2 * ε * (((Y L).card : ℝ) * Real.exp (-κ * D L))) l (𝓝 0) := by
    have := (hYD κ hκ).const_mul (2 * ε)
    rwa [mul_zero] at this
  refine squeeze_zero_norm (fun L => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (hbound L (Λ L)).trans (le_of_eq ?_)
  ring

/-- **Calibration by the twist.**  If the twist free energy stays at least
`f₀ > 0` eventually along a nontrivial filter on which `|Y L| e^{-κ D L} → 0` for
every `κ > 0`, no twist-compatible crossing input exists. -/
theorem false_of_twistFreeEnergy_ge {K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ}
    {Y : ∀ L, Finset (Blocks L)} {D : ι → ℝ}
    (h : TwistCompatibleCrossing Blocks E ν₀ K Ktw Y D) {l : Filter ι} [l.NeBot]
    (hYD : ∀ κ > 0, Tendsto (fun L => ((Y L).card : ℝ) * Real.exp (-κ * D L)) l (𝓝 0))
    (Λ : ∀ L, Finset (Finset (Blocks L))) {f₀ : ℝ} (hf₀ : 0 < f₀)
    (hF : ∀ᶠ L in l, f₀ ≤ |logTwistRatio (ν₀ := ν₀) K Ktw L (Λ L)|) : False := by
  have hsmall : ∀ᶠ L in l, |logTwistRatio (ν₀ := ν₀) K Ktw L (Λ L)| < f₀ := by
    have := (tendsto_logTwistRatio h hYD Λ).abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds hf₀)
  obtain ⟨L, hL₁, hL₂⟩ := (hF.and hsmall).exists
  linarith

/-- On tori indexed by the side `L`, cuts of size at most `C L^m` and diameters at
least `α L - β` with `α > 0` make `|Y L| e^{-κ D L}` tend to zero for every
`κ > 0`. -/
theorem tendsto_card_mul_exp_of_poly_linear {Blocks : ℕ → Type*} [∀ L, Fintype (Blocks L)]
    {Y : ∀ L, Finset (Blocks L)} {D : ℕ → ℝ} (C : ℝ) (m : ℕ) (α β : ℝ) (hα : 0 < α)
    (hY : ∀ L, ((Y L).card : ℝ) ≤ C * (L : ℝ) ^ m) (hD : ∀ L, α * L - β ≤ D L) :
    ∀ κ > 0, Tendsto (fun L => ((Y L).card : ℝ) * Real.exp (-κ * D L)) atTop (𝓝 0) := by
  intro κ hκ
  have hc : 0 < κ * α := mul_pos hκ hα
  have hlim : Tendsto (fun L : ℕ => (κ * α * L) ^ m * Real.exp (-(κ * α * L))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
      (Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop)
  set A : ℝ := C * Real.exp (κ * β) / (κ * α) ^ m with hA
  have hlim2 : Tendsto (fun L : ℕ => A * ((κ * α * L) ^ m * Real.exp (-(κ * α * L))))
      atTop (𝓝 0) := by
    have := hlim.const_mul A
    rwa [mul_zero] at this
  refine squeeze_zero (fun L => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    (fun L => ?_) hlim2
  have hC : 0 ≤ C * (L : ℝ) ^ m := (Nat.cast_nonneg _).trans (hY L)
  have hpow : (κ * α) ^ m ≠ 0 := pow_ne_zero m hc.ne'
  calc ((Y L).card : ℝ) * Real.exp (-κ * D L)
      ≤ C * (L : ℝ) ^ m * Real.exp (-κ * (α * L - β)) := by
        apply mul_le_mul (hY L) _ (Real.exp_pos _).le hC
        apply Real.exp_le_exp.mpr
        nlinarith [hD L]
    _ = A * ((κ * α * L) ^ m * Real.exp (-(κ * α * L))) := by
        rw [hA, show -κ * (α * L - β) = κ * β + -(κ * α * L) by ring, Real.exp_add]
        field_simp
        ring

/-- **Calibration by the twist on tori.**  On tori indexed by the side, with cuts
of polynomial size and winding diameters growing linearly, no twist-compatible
crossing family has twist free energy bounded below by a positive constant. -/
theorem false_of_twistFreeEnergy_ge_of_poly_linear {Blocks : ℕ → Type*}
    [∀ L, Fintype (Blocks L)] [∀ L, DecidableEq (Blocks L)] [∀ L, PseudoMetricSpace (Blocks L)]
    {K Ktw : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ} {Y : ∀ L, Finset (Blocks L)}
    {D : ℕ → ℝ} (h : TwistCompatibleCrossing Blocks E ν₀ K Ktw Y D) (C : ℝ) (m : ℕ)
    (α β : ℝ) (hα : 0 < α) (hY : ∀ L, ((Y L).card : ℝ) ≤ C * (L : ℝ) ^ m)
    (hD : ∀ L, α * L - β ≤ D L) (Λ : ∀ L, Finset (Finset (Blocks L))) {f₀ : ℝ} (hf₀ : 0 < f₀)
    (hF : ∀ L, f₀ ≤ |logTwistRatio (ν₀ := ν₀) K Ktw L (Λ L)|) : False :=
  false_of_twistFreeEnergy_ge h (tendsto_card_mul_exp_of_poly_linear C m α β hα hY hD) Λ hf₀
    (Eventually.of_forall hF)

#print axioms abs_logTwistRatio_le
#print axioms false_of_twistFreeEnergy_ge
#print axioms tendsto_card_mul_exp_of_poly_linear
#print axioms false_of_twistFreeEnergy_ge_of_poly_linear
#print axioms differ_of_movable

end Mettapedia.QuantumTheory.YangMills.TwistDiagnostic
