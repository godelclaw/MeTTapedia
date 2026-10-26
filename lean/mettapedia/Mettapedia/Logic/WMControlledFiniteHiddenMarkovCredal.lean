import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference
import Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
import Mettapedia.PLN.TruthValues.PLNIndefiniteTruthBridge
import Mettapedia.PLN.TruthValues.PLNWeightTV
import Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
import Mettapedia.UniversalAI.BayesianAgents.Core

/-!
# Controlled-HMM posterior intervals and trace-mass value envelopes

A finite family gives normalized filtering-posterior intervals on supported
histories. Its value computations use a different observation: the unnormalized
mass of the completed trace extended by the next cycle. These rows sum to the
past trace probability, so they are subprobabilities rather than conditional
next-observation distributions.

Static policy values retain one model throughout. Recursive envelopes re-select
a model's row at each history after the action is given, using that model's own
filter. They contain every fixed-model value and can be strictly wider. The
finite-horizon convention has separate value/action stages: `V 1 = 0`, and
`V 2` includes one reward. Posterior intervals and trace-mass decision intervals
have separate meanings; the latter do not establish normalized HMM planning.

Model persistence and order of play also matter for robust POMDP semantics:
https://www.ijcai.org/proceedings/2024/740
The normalized conditional planning interface is a separate extension.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal

open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
open Mettapedia.UniversalAI.BayesianAgents.Core
open scoped ENNReal NNReal BigOperators

universe uA uI

variable {Action : Type uA} {ι : Type uI} {latent obs : ℕ}

/-- Lower/upper truth-value interval for an observed-only credal posterior. -/
structure IndefiniteTruthValue where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1

/-- Lower observed-only filtering strength across a finite family of controlled
HMMs. -/
noncomputable def lowerFilteringPosteriorStrength
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => (filteringPosteriorMass (Θ i) zs q).toReal)

/-- Upper observed-only filtering strength across a finite family of controlled
HMMs. -/
noncomputable def upperFilteringPosteriorStrength
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => (filteringPosteriorMass (Θ i) zs q).toReal)

theorem lowerFilteringPosteriorStrength_nonneg
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) :
    0 ≤ lowerFilteringPosteriorStrength Θ zs q := by
  exact Finset.le_inf' _ _ fun _ _ => ENNReal.toReal_nonneg

theorem upperFilteringPosteriorStrength_le_one
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent)
    (hobs : ∀ i, observedCycleProb (Θ i) zs ≠ 0) :
    upperFilteringPosteriorStrength Θ zs q ≤ 1 := by
  exact Finset.sup'_le _ _ fun i _ => by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (filteringPosteriorMass_le_one (Θ i) zs q (hobs i))

theorem lowerFilteringPosteriorStrength_le
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) (i : ι) :
    lowerFilteringPosteriorStrength Θ zs q ≤
      (filteringPosteriorMass (Θ i) zs q).toReal := by
  unfold lowerFilteringPosteriorStrength
  exact Finset.inf'_le (fun j => (filteringPosteriorMass (Θ j) zs q).toReal) (Finset.mem_univ i)

theorem le_upperFilteringPosteriorStrength
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) (i : ι) :
    (filteringPosteriorMass (Θ i) zs q).toReal ≤
      upperFilteringPosteriorStrength Θ zs q := by
  unfold upperFilteringPosteriorStrength
  exact Finset.le_sup' (fun j => (filteringPosteriorMass (Θ j) zs q).toReal) (Finset.mem_univ i)

theorem lowerFilteringPosteriorStrength_le_upper
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) :
    lowerFilteringPosteriorStrength Θ zs q ≤
      upperFilteringPosteriorStrength Θ zs q := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  exact (lowerFilteringPosteriorStrength_le Θ zs q i0).trans
    (le_upperFilteringPosteriorStrength Θ zs q i0)

/-- Credal observed-only WM truth value from a finite family of controlled
HMMs. -/
noncomputable def filteringCredalTruthValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent)
    (hobs : ∀ i, observedCycleProb (Θ i) zs ≠ 0) :
    IndefiniteTruthValue where
  lower := lowerFilteringPosteriorStrength Θ zs q
  upper := upperFilteringPosteriorStrength Θ zs q
  valid := lowerFilteringPosteriorStrength_le_upper Θ zs q
  lower_nonneg := lowerFilteringPosteriorStrength_nonneg Θ zs q
  upper_le_one := upperFilteringPosteriorStrength_le_one Θ zs q hobs

/-- Convert a cycle count to a PLN-style credibility using the weight-primary
`w2c` view with prior scale `κ`. This keeps credibility separate from interval
width. -/
noncomputable def cycleCountCredibility
    (κ : ℝ)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  Mettapedia.PLN.TruthValues.PLNWeightTV.w2c ((zs.length : ℝ) / κ)

theorem cycleCountCredibility_mem_unit
    (κ : ℝ)
    (hκ : 0 < κ)
    (zs : List (CycleObservation Action obs)) :
    cycleCountCredibility (Action := Action) (obs := obs) κ zs ∈ Set.Icc 0 1 := by
  unfold cycleCountCredibility
  have hw_nonneg : 0 ≤ (zs.length : ℝ) / κ := by
    exact div_nonneg (Nat.cast_nonneg zs.length) (le_of_lt hκ)
  exact Mettapedia.PLN.TruthValues.PLNWeightTV.WTV.w2c_bounds _ hw_nonneg

/-- Generic bridge from the local controlled-HMM credal interval into the live
PLN indefinite truth-value interface. -/
noncomputable abbrev IndefiniteTruthValue.toPLNITV
    (tv : IndefiniteTruthValue)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  Mettapedia.PLN.TruthValues.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    tv.lower tv.upper credibility tv.valid tv.lower_nonneg tv.upper_le_one hcred

/-- Operational bridge: turn a controlled-HMM credal filtering interval into the
live PLN `ITV` interface, using cycle-count credibility. -/
noncomputable def filteringCredalPLNITV
    [Fintype ι] [Nonempty ι]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent)
    (hobs : ∀ i, observedCycleProb (Θ i) zs ≠ 0) :
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  (filteringCredalTruthValue Θ zs q hobs).toPLNITV
    (cycleCountCredibility (Action := Action) (obs := obs) κ zs)
    (cycleCountCredibility_mem_unit (Action := Action) (obs := obs) κ hκ zs)

/-- The mass of the completed trace extended by the chosen action and observation. -/
def traceMassRow (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (a : Action) (y : Fin obs) : ℝ≥0∞ :=
  observationMassGivenAction θ (filteringMass θ zs) a y

/-- A row sums to the probability of the past trace, not generally to one. -/
@[simp] theorem traceMassRow_sum (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (a : Action) :
    ∑ y : Fin obs, traceMassRow θ zs a y = observedCycleProb θ zs :=
  observationMassGivenAction_sum_eq θ (filteringMass θ zs) a

/-- The mass of an extended trace is its selected observation entry. -/
theorem observedCycleProb_append_eq_traceMassRow
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (a : Action) (y : Fin obs) :
    observedCycleProb θ (zs ++ [(a, y)]) = traceMassRow θ zs a y := by
  rw [observedCycleProb, filteringMass_append_singleton]; rfl

/-- Every trace-mass row is a subprobability row. -/
theorem traceMassRow_sum_le_one (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (a : Action) :
    ∑ y : Fin obs, traceMassRow θ zs a y ≤ 1 := by
  rw [traceMassRow_sum]; exact observedCycleProb_le_one θ zs

/-- An impossible past trace gives an entirely zero row. -/
theorem traceMassRow_eq_zero (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (a : Action) (y : Fin obs)
    (h : observedCycleProb θ zs = 0) : traceMassRow θ zs a y = 0 := by
  apply le_antisymm
  rotate_left
  · exact zero_le
  calc
    traceMassRow θ zs a y ≤ ∑ z : Fin obs, traceMassRow θ zs a z :=
      Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ y)
    _ = 0 := (traceMassRow_sum θ zs a).trans h

/-- Positive emissions keep every finite trace possible, even with deterministic latent steps. -/
theorem observedCycleProb_ne_zero_of_emissions
    (θ : ControlledFiniteHMMParam Action latent obs)
    (he : ∀ x y, emissionProb θ x y ≠ 0) (zs : List (CycleObservation Action obs)) :
    observedCycleProb θ zs ≠ 0 := by
  induction zs using List.reverseRecOn with
  | nil => simp
  | append_singleton zs z ih =>
      rcases z with ⟨a, y⟩
      intro h
      rw [observedCycleProb, filteringMass_append_singleton] at h
      have hp (x : Fin latent) : predictiveLatentMass θ (filteringMass θ zs) a x = 0 := by
        have hx := (Finset.sum_eq_zero_iff.mp h) x (Finset.mem_univ x)
        exact (mul_eq_zero.mp hx).resolve_right (by simpa only [ENNReal.coe_eq_zero] using he x y)
      apply ih
      change (∑ x : Fin latent, filteringMass θ zs x) = 0
      rw [← predictiveLatentMass_sum_eq θ (filteringMass θ zs) a]
      exact Finset.sum_eq_zero fun x _ => hp x

/-- At positive trace mass, raw weights are trace probability times posterior prediction. -/
theorem traceMassRow_eq_trace_mul_posterior (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (a : Action) (y : Fin obs)
    (h : observedCycleProb θ zs ≠ 0) :
    traceMassRow θ zs a y = observedCycleProb θ zs *
      observationMassGivenAction θ (filteringPosteriorMass θ zs) a y := by
  simp only [traceMassRow, observationMassGivenAction, filteringStepMass,
    predictiveLatentMass, filteringPosteriorMass, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  rw [← mul_assoc, ← mul_assoc, ENNReal.mul_div_cancel h (observedCycleProb_ne_top θ zs)]

/-- Reward plus continuation, weighted by the unnormalized mass of the extended trace. -/
noncomputable def traceMassContinuation [PerceptReward (Fin obs)]
    (θ : ControlledFiniteHMMParam Action latent obs) (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (a : Action)
    (v : List (CycleObservation Action obs) → ℝ) : ℝ :=
  ∑ y : Fin obs, (traceMassRow θ zs a y).toReal *
    (PerceptReward.reward y + γ.val * v (zs ++ [(a, y)]))

/-- Nonnegative trace weights and discount preserve continuation inequalities. -/
theorem traceMassContinuation_mono [PerceptReward (Fin obs)]
    (θ : ControlledFiniteHMMParam Action latent obs) (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (a : Action)
    {v w : List (CycleObservation Action obs) → ℝ} (h : ∀ ws, v ws ≤ w ws) :
    traceMassContinuation θ γ zs a v ≤ traceMassContinuation θ γ zs a w := by
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (h _) γ.nonneg)) ENNReal.toReal_nonneg

private theorem foldMax_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) :
    Finset.univ.fold max 0 f ≤ Finset.univ.fold max 0 g := by
  rw [Finset.fold_max_le]
  exact ⟨(Finset.le_fold_max _).2 (Or.inl le_rfl), fun a ha =>
    (h a).trans ((Finset.le_fold_max _).2 (Or.inr ⟨a, ha, le_rfl⟩))⟩

section OneStepTraceMassValue

variable [PerceptReward (Fin obs)]

/-- Trace-mass-weighted immediate reward from a completed trace and a chosen
action, under the subprobability environment bridge. -/
noncomputable def oneStepTraceMassQValue
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℝ :=
  ∑ y : Fin obs,
    (observationMassGivenAction θ (filteringMass θ zs) a y).toReal *
      PerceptReward.reward y

omit [PerceptReward (Fin obs)] in
theorem historyOfCycles_wellFormed
    (zs : List (CycleObservation Action obs)) :
    History.wellFormed (Action := Action) (Percept := Fin obs)
      (historyOfCycles zs) = true := by
  induction zs with
  | nil =>
      simp [historyOfCycles, History.wellFormed]
  | cons z zs ih =>
      cases z with
      | mk a y =>
          simp [historyOfCycles, History.wellFormed, ih]

omit [PerceptReward (Fin obs)] in
theorem historyOfCycles_append_act_wellFormed
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    History.wellFormed (Action := Action) (Percept := Fin obs)
      (historyOfCycles zs ++ [HistElem.act a]) = true := by
  induction zs with
  | nil =>
      simp [historyOfCycles, History.wellFormed]
  | cons z zs ih =>
      cases z with
      | mk a' y =>
          simp [historyOfCycles, History.wellFormed, ih]

omit [PerceptReward (Fin obs)] in
@[simp] theorem historyOfCycles_append_singleton
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    historyOfCycles (zs ++ [(a, y)]) =
      historyOfCycles zs ++ [HistElem.act a, HistElem.per y] := by
  induction zs with
  | nil =>
      simp [historyOfCycles]
  | cons z zs ih =>
      cases z with
      | mk a' y' =>
          simp [historyOfCycles, ih]

private theorem qValue_succ_eq_traceMassContinuation
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs) (π : Agent Action (Fin obs))
    (γ : DiscountFactor) (zs : List (CycleObservation Action obs)) (a : Action) (n : ℕ) :
    qValue (toEnvironment θ) π γ (historyOfCycles zs) a (n + 1) =
      traceMassContinuation θ γ zs a (fun ws => value (toEnvironment θ) π γ (historyOfCycles ws) n) := by
  rw [qValue_succ]
  simp [traceMassContinuation, traceMassRow, historyOfCycles_append_act_wellFormed,
    toEnvironment, environmentProb_historyOfCycles_append_act, historyOfCycles_append_singleton]

private theorem optimalQValue_succ_eq_traceMassContinuation
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs) (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (a : Action) (n : ℕ) :
    optimalQValue (toEnvironment θ) γ (historyOfCycles zs) a (n + 1) =
      traceMassContinuation θ γ zs a (fun ws => optimalValue (toEnvironment θ) γ (historyOfCycles ws) n) := by
  rw [optimalQValue_succ]
  simp [traceMassContinuation, traceMassRow, historyOfCycles_append_act_wellFormed,
    toEnvironment, environmentProb_historyOfCycles_append_act, historyOfCycles_append_singleton]

theorem oneStepTraceMassQValue_nonneg
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    0 ≤ oneStepTraceMassQValue θ zs a := by
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg ENNReal.toReal_nonneg (PerceptReward.nonneg y)

theorem oneStepTraceMassQValue_le_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    oneStepTraceMassQValue θ zs a ≤ 1 := by
  have finite (y : Fin obs) : traceMassRow θ zs a y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ y)).trans
        (traceMassRow_sum_le_one θ zs a))
  calc
    oneStepTraceMassQValue θ zs a ≤ ∑ y : Fin obs, (traceMassRow θ zs a y).toReal :=
      Finset.sum_le_sum fun y _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (PerceptReward.le_one y)
    _ = (∑ y : Fin obs, traceMassRow θ zs a y).toReal :=
      (ENNReal.toReal_sum (fun y _ => finite y)).symm
    _ ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (traceMassRow_sum_le_one θ zs a)

theorem qValue_historyOfCycles_one_eq_oneStepTraceMassQValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    qValue (toEnvironment θ) π γ (historyOfCycles zs) a 1 =
      oneStepTraceMassQValue θ zs a := by
  rw [qValue_succ_eq_traceMassContinuation]
  simp [traceMassContinuation, traceMassRow, oneStepTraceMassQValue, value_zero]

theorem optimalQValue_historyOfCycles_one_eq_oneStepTraceMassQValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    optimalQValue (toEnvironment θ) γ (historyOfCycles zs) a 1 =
      oneStepTraceMassQValue θ zs a := by
  rw [optimalQValue_succ_eq_traceMassContinuation]
  simp [traceMassContinuation, traceMassRow, oneStepTraceMassQValue, optimalValue_zero]

/-- The one-step optimal decision value from a completed trace: maximum over the
available one-step `qValue`s. In the BayesianAgents horizon convention, this
matches `optimalValue ... 2`. -/
noncomputable def oneStepTraceMassOptimalValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  (Finset.univ : Finset Action).fold max 0 (fun a => oneStepTraceMassQValue θ zs a)

theorem oneStepTraceMassOptimalValue_nonneg
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    0 ≤ oneStepTraceMassOptimalValue θ zs := by
  exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem oneStepTraceMassOptimalValue_le_one
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    oneStepTraceMassOptimalValue θ zs ≤ 1 := by
  exact (Finset.fold_max_le _).2 ⟨by norm_num, fun a _ => oneStepTraceMassQValue_le_one θ zs a⟩

theorem optimalValue_historyOfCycles_two_eq_oneStepTraceMassOptimalValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) :
    optimalValue (toEnvironment θ) γ (historyOfCycles zs) 2 =
      oneStepTraceMassOptimalValue θ zs := by
  rw [optimalValue_succ]
  simp [historyOfCycles_wellFormed, oneStepTraceMassOptimalValue,
    optimalQValue_historyOfCycles_one_eq_oneStepTraceMassQValue]

/-- Lower one-step `qValue` envelope across a finite family of controlled HMMs. -/
noncomputable def lowerOneStepTraceMassQValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => oneStepTraceMassQValue (Θ i) zs a)

/-- Upper one-step `qValue` envelope across a finite family of controlled HMMs. -/
noncomputable def upperOneStepTraceMassQValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => oneStepTraceMassQValue (Θ i) zs a)

theorem lowerOneStepTraceMassQValue_le
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    lowerOneStepTraceMassQValue Θ zs a ≤ oneStepTraceMassQValue (Θ i) zs a := by
  unfold lowerOneStepTraceMassQValue
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_upperOneStepTraceMassQValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    oneStepTraceMassQValue (Θ i) zs a ≤ upperOneStepTraceMassQValue Θ zs a := by
  unfold upperOneStepTraceMassQValue
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun j : ι => oneStepTraceMassQValue (Θ j) zs a)
    (Finset.mem_univ i)

theorem lowerOneStepTraceMassQValue_le_upper
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    lowerOneStepTraceMassQValue Θ zs a ≤ upperOneStepTraceMassQValue Θ zs a := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  exact (lowerOneStepTraceMassQValue_le Θ zs a i0).trans
    (le_upperOneStepTraceMassQValue Θ zs a i0)

theorem lowerOneStepTraceMassQValue_nonneg
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    0 ≤ lowerOneStepTraceMassQValue Θ zs a := by
  exact Finset.le_inf' _ _ fun i _ => oneStepTraceMassQValue_nonneg (Θ i) zs a

theorem upperOneStepTraceMassQValue_le_one
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    upperOneStepTraceMassQValue Θ zs a ≤ 1 := by
  exact Finset.sup'_le _ _ fun i _ => oneStepTraceMassQValue_le_one (Θ i) zs a

/-- Credal one-step value envelope across a finite family of controlled HMMs. -/
noncomputable def oneStepTraceMassQValueCredalTruthValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    IndefiniteTruthValue where
  lower := lowerOneStepTraceMassQValue Θ zs a
  upper := upperOneStepTraceMassQValue Θ zs a
  valid := lowerOneStepTraceMassQValue_le_upper Θ zs a
  lower_nonneg := lowerOneStepTraceMassQValue_nonneg Θ zs a
  upper_le_one := upperOneStepTraceMassQValue_le_one Θ zs a

/-- One-step `qValue` envelope rendered as the live PLN indefinite truth-value
interface. -/
noncomputable abbrev oneStepTraceMassQValuePLNITV
    [Fintype ι] [Nonempty ι]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  IndefiniteTruthValue.toPLNITV
    (oneStepTraceMassQValueCredalTruthValue Θ zs a)
    (cycleCountCredibility (Action := Action) (obs := obs) κ zs)
    (cycleCountCredibility_mem_unit (Action := Action) (obs := obs) κ hκ zs)

/-- Any family member's one-step `qValue` lies inside the credal envelope. -/
theorem qValue_historyOfCycles_one_mem_envelope
    [Fintype ι] [Nonempty ι]
    [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    lowerOneStepTraceMassQValue Θ zs a ≤
        qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ∧
      qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ≤
        upperOneStepTraceMassQValue Θ zs a := by
  have hq :=
    qValue_historyOfCycles_one_eq_oneStepTraceMassQValue
      (θ := Θ i) (π := π) (γ := γ) (zs := zs) (a := a)
  constructor
  · simpa [hq] using lowerOneStepTraceMassQValue_le Θ zs a i
  · simpa [hq] using le_upperOneStepTraceMassQValue Θ zs a i

theorem qValue_historyOfCycles_one_mem_PLNITV_interval
    [Fintype ι] [Nonempty ι]
    [Fintype Action]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    let itv := oneStepTraceMassQValuePLNITV (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ zs a
    itv.lower ≤ qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ∧
      qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ≤ itv.upper := by
  simpa [oneStepTraceMassQValuePLNITV, IndefiniteTruthValue.toPLNITV,
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    oneStepTraceMassQValueCredalTruthValue]
    using qValue_historyOfCycles_one_mem_envelope Θ π γ zs a i

/-- Lower one-step optimal decision value across a finite family of controlled
HMMs. This corresponds to the BayesianAgents quantity `optimalValue ... 2`. -/
noncomputable def lowerOneStepTraceMassOptimalValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => oneStepTraceMassOptimalValue (Θ i) zs)

/-- Upper one-step optimal decision value across a finite family of controlled
HMMs. -/
noncomputable def upperOneStepTraceMassOptimalValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => oneStepTraceMassOptimalValue (Θ i) zs)

theorem lowerOneStepTraceMassOptimalValue_le
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    lowerOneStepTraceMassOptimalValue Θ zs ≤ oneStepTraceMassOptimalValue (Θ i) zs := by
  unfold lowerOneStepTraceMassOptimalValue
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_upperOneStepTraceMassOptimalValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    oneStepTraceMassOptimalValue (Θ i) zs ≤ upperOneStepTraceMassOptimalValue Θ zs := by
  unfold upperOneStepTraceMassOptimalValue
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun j : ι => oneStepTraceMassOptimalValue (Θ j) zs)
    (Finset.mem_univ i)

theorem lowerOneStepTraceMassOptimalValue_le_upper
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    lowerOneStepTraceMassOptimalValue Θ zs ≤ upperOneStepTraceMassOptimalValue Θ zs := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  exact (lowerOneStepTraceMassOptimalValue_le Θ zs i0).trans
    (le_upperOneStepTraceMassOptimalValue Θ zs i0)

theorem lowerOneStepTraceMassOptimalValue_nonneg
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    0 ≤ lowerOneStepTraceMassOptimalValue Θ zs := by
  exact Finset.le_inf' _ _ fun i _ => oneStepTraceMassOptimalValue_nonneg (Θ i) zs

theorem upperOneStepTraceMassOptimalValue_le_one
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    upperOneStepTraceMassOptimalValue Θ zs ≤ 1 := by
  exact Finset.sup'_le _ _ fun i _ => oneStepTraceMassOptimalValue_le_one (Θ i) zs

/-- Credal one-step optimal decision value envelope rendered as the local
bounded interval type. -/
noncomputable def oneStepTraceMassOptimalValueCredalTruthValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    IndefiniteTruthValue where
  lower := lowerOneStepTraceMassOptimalValue Θ zs
  upper := upperOneStepTraceMassOptimalValue Θ zs
  valid := lowerOneStepTraceMassOptimalValue_le_upper Θ zs
  lower_nonneg := lowerOneStepTraceMassOptimalValue_nonneg Θ zs
  upper_le_one := upperOneStepTraceMassOptimalValue_le_one Θ zs

/-- One-step optimal decision envelope as the live PLN indefinite truth-value
interface. -/
noncomputable abbrev oneStepTraceMassOptimalValuePLNITV
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  IndefiniteTruthValue.toPLNITV
    (oneStepTraceMassOptimalValueCredalTruthValue Θ zs)
    (cycleCountCredibility (Action := Action) (obs := obs) κ zs)
    (cycleCountCredibility_mem_unit (Action := Action) (obs := obs) κ hκ zs)

theorem optimalValue_historyOfCycles_two_mem_envelope
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    lowerOneStepTraceMassOptimalValue Θ zs ≤
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ∧
      optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ≤
        upperOneStepTraceMassOptimalValue Θ zs := by
  have hopt :=
    optimalValue_historyOfCycles_two_eq_oneStepTraceMassOptimalValue
      (θ := Θ i) (γ := γ) (zs := zs)
  constructor
  · simpa [hopt] using lowerOneStepTraceMassOptimalValue_le Θ zs i
  · simpa [hopt] using le_upperOneStepTraceMassOptimalValue Θ zs i

theorem optimalValue_historyOfCycles_two_mem_PLNITV_interval
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    let itv := oneStepTraceMassOptimalValuePLNITV (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ zs
    itv.lower ≤ optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ∧
      optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ≤ itv.upper := by
  simpa [oneStepTraceMassOptimalValuePLNITV, IndefiniteTruthValue.toPLNITV,
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    oneStepTraceMassOptimalValueCredalTruthValue]
    using optimalValue_historyOfCycles_two_mem_envelope Θ γ zs i

end OneStepTraceMassValue

section RecursiveTraceMassEnvelope

variable [PerceptReward (Fin obs)] [Fintype Action]

mutual

/-- Lower row-reselecting trace-mass fixed-policy value envelope across a finite family of
controlled HMMs. -/
noncomputable def lowerRecursiveTraceMassValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      ∑ a : Action,
        (π.policy (historyOfCycles zs) a).toReal *
          lowerRecursiveTraceMassQValueEnvelope Θ π γ zs a n

/-- Lower row-reselecting trace-mass fixed-policy Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def lowerRecursiveTraceMassQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.inf' Finset.univ_nonempty
        (fun i => traceMassContinuation (Θ i) γ zs a
          (fun ws => lowerRecursiveTraceMassValueEnvelope Θ π γ ws n))

end

mutual

/-- Upper row-reselecting trace-mass fixed-policy value envelope across a finite family of
controlled HMMs. -/
noncomputable def upperRecursiveTraceMassValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      ∑ a : Action,
        (π.policy (historyOfCycles zs) a).toReal *
          upperRecursiveTraceMassQValueEnvelope Θ π γ zs a n

/-- Upper row-reselecting trace-mass fixed-policy Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def upperRecursiveTraceMassQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => traceMassContinuation (Θ i) γ zs a
          (fun ws => upperRecursiveTraceMassValueEnvelope Θ π γ ws n))

end

mutual

/-- Lower row-reselecting trace-mass optimal value envelope across a finite family of controlled
HMMs. -/
noncomputable def lowerRecursiveTraceMassOptimalValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      (Finset.univ : Finset Action).fold max 0
        (fun a => lowerRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n)

/-- Lower row-reselecting trace-mass optimal Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def lowerRecursiveTraceMassOptimalQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.inf' Finset.univ_nonempty
        (fun i => traceMassContinuation (Θ i) γ zs a
          (fun ws => lowerRecursiveTraceMassOptimalValueEnvelope Θ γ ws n))

end

mutual

/-- Upper row-reselecting trace-mass optimal value envelope across a finite family of controlled
HMMs. -/
noncomputable def upperRecursiveTraceMassOptimalValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      (Finset.univ : Finset Action).fold max 0
        (fun a => upperRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n)

/-- Upper row-reselecting trace-mass optimal Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def upperRecursiveTraceMassOptimalQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => traceMassContinuation (Θ i) γ zs a
          (fun ws => upperRecursiveTraceMassOptimalValueEnvelope Θ γ ws n))

end

mutual

theorem qValue_historyOfCycles_mem_recursiveTraceMassEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action) (i : ι),
      lowerRecursiveTraceMassQValueEnvelope Θ π γ zs a n ≤
          qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n ∧
        qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n ≤
          upperRecursiveTraceMassQValueEnvelope Θ π γ zs a n
  | 0, zs, a, i => by
      simp [lowerRecursiveTraceMassQValueEnvelope, upperRecursiveTraceMassQValueEnvelope, qValue_zero]
  | n + 1, zs, a, i => by
      rw [qValue_succ_eq_traceMassContinuation]
      constructor
      · apply le_trans (Finset.inf'_le _ (Finset.mem_univ i))
        exact traceMassContinuation_mono _ _ _ _ fun ws =>
          (value_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (π := π) (γ := γ) n ws i).1
      · exact (traceMassContinuation_mono _ _ _ _ fun ws =>
          (value_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (π := π) (γ := γ) n ws i).2).trans
            (Finset.le_sup' (fun j => traceMassContinuation (Θ j) γ zs a
              (fun ws => upperRecursiveTraceMassValueEnvelope Θ π γ ws n))
              (Finset.mem_univ i))

theorem value_historyOfCycles_mem_recursiveTraceMassEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (i : ι),
      lowerRecursiveTraceMassValueEnvelope Θ π γ zs n ≤
          value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n ∧
        value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n ≤
          upperRecursiveTraceMassValueEnvelope Θ π γ zs n
  | 0, zs, i => by
      simp [lowerRecursiveTraceMassValueEnvelope, upperRecursiveTraceMassValueEnvelope, value_zero]
  | n + 1, zs, i => by
      rw [value_succ]
      simp only [historyOfCycles_wellFormed]
      constructor
      · exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (qValue_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (π := π) (γ := γ) n zs a i).1 ENNReal.toReal_nonneg
      · exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (qValue_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (π := π) (γ := γ) n zs a i).2 ENNReal.toReal_nonneg

end

mutual

theorem optimalQValue_historyOfCycles_mem_recursiveTraceMassEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action) (i : ι),
      lowerRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n ≤
          optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a n ∧
        optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a n ≤
          upperRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n
  | 0, zs, a, i => by
      simp [lowerRecursiveTraceMassOptimalQValueEnvelope, upperRecursiveTraceMassOptimalQValueEnvelope, optimalQValue_zero]
  | n + 1, zs, a, i => by
      rw [optimalQValue_succ_eq_traceMassContinuation]
      constructor
      · apply le_trans (Finset.inf'_le _ (Finset.mem_univ i))
        exact traceMassContinuation_mono _ _ _ _ fun ws =>
          (optimalValue_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (γ := γ) n ws i).1
      · exact (traceMassContinuation_mono _ _ _ _ fun ws =>
          (optimalValue_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (γ := γ) n ws i).2).trans
            (Finset.le_sup' (fun j => traceMassContinuation (Θ j) γ zs a
              (fun ws => upperRecursiveTraceMassOptimalValueEnvelope Θ γ ws n))
              (Finset.mem_univ i))

theorem optimalValue_historyOfCycles_mem_recursiveTraceMassEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (i : ι),
      lowerRecursiveTraceMassOptimalValueEnvelope Θ γ zs n ≤
          optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ∧
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ≤
          upperRecursiveTraceMassOptimalValueEnvelope Θ γ zs n
  | 0, zs, i => by
      simp [lowerRecursiveTraceMassOptimalValueEnvelope, upperRecursiveTraceMassOptimalValueEnvelope, optimalValue_zero]
  | n + 1, zs, i => by
      rw [optimalValue_succ]
      simp only [historyOfCycles_wellFormed]
      exact ⟨foldMax_mono fun a => (optimalQValue_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (γ := γ) n zs a i).1,
        foldMax_mono fun a => (optimalQValue_historyOfCycles_mem_recursiveTraceMassEnvelope (Θ := Θ) (γ := γ) n zs a i).2⟩

end

end RecursiveTraceMassEnvelope

section StaticTraceMass

variable [PerceptReward (Fin obs)] [Fintype Action] [Fintype ι] [Nonempty ι]

/-- Worst fixed-model policy value: one model is retained for the whole computation. -/
noncomputable def lowerStaticTraceMassValue
    (Θ : ι → ControlledFiniteHMMParam Action latent obs) (π : Agent Action (Fin obs))
    (γ : DiscountFactor) (zs : List (CycleObservation Action obs)) (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n)

/-- Best fixed-model policy value, using the same policy for every model. -/
noncomputable def upperStaticTraceMassValue
    (Θ : ι → ControlledFiniteHMMParam Action latent obs) (π : Agent Action (Fin obs))
    (γ : DiscountFactor) (zs : List (CycleObservation Action obs)) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n)

/-- Re-selecting rows at later histories can widen the fixed-policy value range. -/
theorem staticTraceMassValue_mem_reselectingEnvelope
    (Θ : ι → ControlledFiniteHMMParam Action latent obs) (π : Agent Action (Fin obs))
    (γ : DiscountFactor) (zs : List (CycleObservation Action obs)) (n : ℕ) :
    lowerRecursiveTraceMassValueEnvelope Θ π γ zs n ≤ lowerStaticTraceMassValue Θ π γ zs n ∧
      lowerStaticTraceMassValue Θ π γ zs n ≤ upperStaticTraceMassValue Θ π γ zs n ∧
      upperStaticTraceMassValue Θ π γ zs n ≤ upperRecursiveTraceMassValueEnvelope Θ π γ zs n := by
  let v i := value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n
  have h i := value_historyOfCycles_mem_recursiveTraceMassEnvelope Θ π γ n zs i
  exact ⟨Finset.le_inf' _ _ (fun i _ => (h i).1),
    (Finset.inf'_le v (Finset.mem_univ (Classical.choice inferInstance))).trans
      (Finset.le_sup' v (Finset.mem_univ (Classical.choice inferInstance))),
    Finset.sup'_le _ _ (fun i _ => (h i).2)⟩

end StaticTraceMass

section RecursiveEnvelopeRestriction

variable [PerceptReward (Fin obs)] [Fintype Action]
variable {κ : Type*}

mutual

/-- Restricting to a reindexed subfamily can only raise the lower recursive
optimal `Q` envelope. This is the credal monotonicity theorem corresponding to
learning by narrowing the admissible model family. -/
theorem lowerRecursiveTraceMassOptimalQValueEnvelope_le_reindex
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action),
      lowerRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n ≤
        lowerRecursiveTraceMassOptimalQValueEnvelope (fun k => Θ (f k)) γ zs a n
  | 0, zs, a => by simp [lowerRecursiveTraceMassOptimalQValueEnvelope]
  | n + 1, zs, a => by
      unfold lowerRecursiveTraceMassOptimalQValueEnvelope
      refine Finset.le_inf' _ _ fun k _ => ?_
      apply le_trans (Finset.inf'_le _ (Finset.mem_univ (f k)))
      exact traceMassContinuation_mono _ _ _ _ fun ws =>
        lowerRecursiveTraceMassOptimalValueEnvelope_le_reindex (Θ := Θ) (f := f) (γ := γ) n ws

/-- Restricting to a reindexed subfamily can only lower the upper recursive
optimal `Q` envelope. -/
theorem upperRecursiveTraceMassOptimalQValueEnvelope_reindex_le
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action),
      upperRecursiveTraceMassOptimalQValueEnvelope (fun k => Θ (f k)) γ zs a n ≤
        upperRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n
  | 0, zs, a => by simp [upperRecursiveTraceMassOptimalQValueEnvelope]
  | n + 1, zs, a => by
      unfold upperRecursiveTraceMassOptimalQValueEnvelope
      refine Finset.sup'_le _ _ fun k _ => ?_
      exact (traceMassContinuation_mono _ _ _ _ fun ws =>
        upperRecursiveTraceMassOptimalValueEnvelope_reindex_le (Θ := Θ) (f := f) (γ := γ) n ws).trans
          (Finset.le_sup' (fun j => traceMassContinuation (Θ j) γ zs a
            (fun ws => upperRecursiveTraceMassOptimalValueEnvelope Θ γ ws n))
            (Finset.mem_univ (f k)))

/-- Restricting to a reindexed subfamily can only raise the lower recursive
optimal value envelope. -/
theorem lowerRecursiveTraceMassOptimalValueEnvelope_le_reindex
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)),
      lowerRecursiveTraceMassOptimalValueEnvelope Θ γ zs n ≤
        lowerRecursiveTraceMassOptimalValueEnvelope (fun k => Θ (f k)) γ zs n
  | 0, zs => by simp [lowerRecursiveTraceMassOptimalValueEnvelope]
  | n + 1, zs =>
      foldMax_mono fun a =>
        lowerRecursiveTraceMassOptimalQValueEnvelope_le_reindex
          (Θ := Θ) (f := f) (γ := γ) n zs a

/-- Restricting to a reindexed subfamily can only lower the upper recursive
optimal value envelope. -/
theorem upperRecursiveTraceMassOptimalValueEnvelope_reindex_le
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)),
      upperRecursiveTraceMassOptimalValueEnvelope (fun k => Θ (f k)) γ zs n ≤
        upperRecursiveTraceMassOptimalValueEnvelope Θ γ zs n
  | 0, zs => by simp [upperRecursiveTraceMassOptimalValueEnvelope]
  | n + 1, zs =>
      foldMax_mono fun a =>
        upperRecursiveTraceMassOptimalQValueEnvelope_reindex_le
          (Θ := Θ) (f := f) (γ := γ) n zs a

end

/- Credal learning monotonicity: narrowing the controlled-HMM family via a
reindexing map shrinks the recursive optimal decision interval. -/
set_option linter.unusedSectionVars false
theorem recursiveTraceMassOptimalValueEnvelope_mono_reindex
    [Fintype ι] [Nonempty ι]
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (n : ℕ) :
    lowerRecursiveTraceMassOptimalValueEnvelope Θ γ zs n ≤
        lowerRecursiveTraceMassOptimalValueEnvelope (fun k => Θ (f k)) γ zs n ∧
      upperRecursiveTraceMassOptimalValueEnvelope (fun k => Θ (f k)) γ zs n ≤
        upperRecursiveTraceMassOptimalValueEnvelope Θ γ zs n := by
  exact ⟨
    lowerRecursiveTraceMassOptimalValueEnvelope_le_reindex (Θ := Θ) (f := f) (γ := γ) n zs,
    upperRecursiveTraceMassOptimalValueEnvelope_reindex_le (Θ := Θ) (f := f) (γ := γ) n zs
  ⟩
set_option linter.unusedSectionVars true

end RecursiveEnvelopeRestriction

section RecursiveEnvelopeSingletonCollapse

variable [PerceptReward (Fin obs)] [Fintype Action]

mutual

/-- In a singleton controlled-HMM family, the lower and upper recursive optimal
`Q` envelopes coincide. -/
theorem recursiveTraceMassOptimalQValueEnvelope_eq_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action),
      lowerRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n =
        upperRecursiveTraceMassOptimalQValueEnvelope Θ γ zs a n
  | 0, zs, a => by
      simp [lowerRecursiveTraceMassOptimalQValueEnvelope, upperRecursiveTraceMassOptimalQValueEnvelope]
  | n + 1, zs, a => by
      let i₀ : ι := Classical.choice inferInstance
      have hi (i : ι) : i = i₀ := Subsingleton.elim _ _
      simp only [lowerRecursiveTraceMassOptimalQValueEnvelope, upperRecursiveTraceMassOptimalQValueEnvelope, hi,
        Finset.inf'_const, Finset.sup'_const]
      congr 1
      funext ws
      exact recursiveTraceMassOptimalValueEnvelope_eq_of_subsingleton (Θ := Θ) (γ := γ) n ws

/-- In a singleton controlled-HMM family, the lower and upper recursive optimal
value envelopes coincide. -/
theorem recursiveTraceMassOptimalValueEnvelope_eq_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)),
      lowerRecursiveTraceMassOptimalValueEnvelope Θ γ zs n =
        upperRecursiveTraceMassOptimalValueEnvelope Θ γ zs n
  | 0, zs => by
      simp [lowerRecursiveTraceMassOptimalValueEnvelope, upperRecursiveTraceMassOptimalValueEnvelope]
  | n + 1, zs => by
      unfold lowerRecursiveTraceMassOptimalValueEnvelope upperRecursiveTraceMassOptimalValueEnvelope
      congr 1
      funext a
      exact recursiveTraceMassOptimalQValueEnvelope_eq_of_subsingleton (Θ := Θ) (γ := γ) n zs a

end

/- In a singleton controlled-HMM family, the recursive credal optimal-value
envelope collapses exactly to the model's optimal value. -/
set_option linter.unusedSectionVars false
theorem recursiveTraceMassOptimalValueEnvelope_eq_model_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (n : ℕ)
    (zs : List (CycleObservation Action obs))
    (i : ι) :
    lowerRecursiveTraceMassOptimalValueEnvelope Θ γ zs n =
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ∧
      upperRecursiveTraceMassOptimalValueEnvelope Θ γ zs n =
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n := by
  have hmem :=
    optimalValue_historyOfCycles_mem_recursiveTraceMassEnvelope
      (Θ := Θ) (γ := γ) n zs i
  have hcollapse :=
    recursiveTraceMassOptimalValueEnvelope_eq_of_subsingleton
      (Θ := Θ) (γ := γ) n zs
  constructor
  · apply le_antisymm
    · exact hmem.1
    · simpa [hcollapse] using hmem.2
  · apply le_antisymm
    · simpa [hcollapse] using hmem.1
    · exact hmem.2
set_option linter.unusedSectionVars true

end RecursiveEnvelopeSingletonCollapse

section LabelSwapWitness

/-- Tiny local Dirac helper for the credal witness models. -/
private def diracPM {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : MeasureTheory.ProbabilityMeasure α :=
  ⟨MeasureTheory.Measure.dirac a, MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

@[simp] private theorem diracPM_apply_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α]
    (a b : α) :
    diracPM a ({b} : Set α) = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h
    simp [diracPM]
  · simp [diracPM, h]

@[simp] private theorem singleton_indicator_one_toNNReal
    {α : Type*} [DecidableEq α] (a b : α) :
    (((Set.singleton a).indicator (1 : α → ENNReal)) b).toNNReal = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h
    have hb : b ∈ Set.singleton b := Set.mem_singleton b
    have hind : (((Set.singleton b).indicator (1 : α → ENNReal)) b) = 1 := by
      rw [Set.indicator_of_mem hb]
      simp
    simp [hind]
  · have hb : b ∉ Set.singleton a := by
      intro hb
      exact h (Set.mem_singleton_iff.mp hb)
    have hind : (((Set.singleton a).indicator (1 : α → ENNReal)) b) = 0 := by
      rw [Set.indicator_of_notMem hb]
    simp [h, hind]

/-- Unit-action version of the first label-swap witness. -/
noncomputable def hiddenLabelSwapControlledHMM₀ : ControlledFiniteHMMParam Unit 2 2 where
  init := diracPM 0
  trans := fun _ i => diracPM i
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1

/-- Same observed process, swapped hidden labels. -/
noncomputable def hiddenLabelSwapControlledHMM₁ : ControlledFiniteHMMParam Unit 2 2 where
  init := diracPM 1
  trans := fun _ i => diracPM i
  emission := fun
    | 0 => diracPM 1
    | 1 => diracPM 0

noncomputable def hiddenLabelSwapFamily : Fin 2 → ControlledFiniteHMMParam Unit 2 2
  | 0 => hiddenLabelSwapControlledHMM₀
  | 1 => hiddenLabelSwapControlledHMM₁

@[simp] theorem hiddenLabelSwapControlled_observedCycleProb_singleton_model0 :
    observedCycleProb hiddenLabelSwapControlledHMM₀ [((), 0)] = 1 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    observedCycleProb_append_singleton]
  unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₀, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_observedCycleProb_singleton_model1 :
    observedCycleProb hiddenLabelSwapControlledHMM₁ [((), 0)] = 1 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    observedCycleProb_append_singleton]
  unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₁, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_filteringMass_model0 :
    filteringMass hiddenLabelSwapControlledHMM₀ [((), 0)] 0 = 1 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    filteringMass_append_singleton]
  unfold filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₀, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_filteringMass_model1 :
    filteringMass hiddenLabelSwapControlledHMM₁ [((), 0)] 0 = 0 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    filteringMass_append_singleton]
  unfold filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₁, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_filteringPosteriorMass_model0 :
    filteringPosteriorMass hiddenLabelSwapControlledHMM₀ [((), 0)] 0 = 1 := by
  unfold filteringPosteriorMass
  rw [hiddenLabelSwapControlled_observedCycleProb_singleton_model0,
    hiddenLabelSwapControlled_filteringMass_model0]
  simp

@[simp] theorem hiddenLabelSwapControlled_filteringPosteriorMass_model1 :
    filteringPosteriorMass hiddenLabelSwapControlledHMM₁ [((), 0)] 0 = 0 := by
  unfold filteringPosteriorMass
  rw [hiddenLabelSwapControlled_observedCycleProb_singleton_model1,
    hiddenLabelSwapControlled_filteringMass_model1]
  simp

theorem hiddenLabelSwapFamily_observed_nonzero (i : Fin 2) :
    observedCycleProb (hiddenLabelSwapFamily i) [((), 0)] ≠ 0 := by
  fin_cases i <;> simp [hiddenLabelSwapFamily]

theorem hiddenLabelSwapFamily_lower_eq_zero :
    lowerFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 = 0 := by
  apply le_antisymm
  · calc
      lowerFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0
        ≤ (filteringPosteriorMass (hiddenLabelSwapFamily 1) [((), 0)] 0).toReal :=
            lowerFilteringPosteriorStrength_le hiddenLabelSwapFamily [((), 0)] 0 1
      _ = 0 := by
          have hzero :
              (filteringPosteriorMass (hiddenLabelSwapFamily 1) [((), 0)] 0).toReal = 0 := by
            exact congrArg ENNReal.toReal hiddenLabelSwapControlled_filteringPosteriorMass_model1
          exact hzero
  · exact lowerFilteringPosteriorStrength_nonneg hiddenLabelSwapFamily [((), 0)] 0

theorem hiddenLabelSwapFamily_upper_eq_one :
    upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 = 1 := by
  apply le_antisymm
  · exact upperFilteringPosteriorStrength_le_one hiddenLabelSwapFamily [((), 0)] 0
      hiddenLabelSwapFamily_observed_nonzero
  · have hmem :
        (1 : ℝ) ≤ upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 := by
        calc
          (1 : ℝ) = (filteringPosteriorMass (hiddenLabelSwapFamily 0) [((), 0)] 0).toReal := by
            simp [hiddenLabelSwapFamily]
          _ ≤ upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 := by
            exact le_upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 0
    exact hmem

/-- Positive example: the credal truth value for the unit-action label-swap
family spans the full interval `[0,1]`. -/
example :
    (filteringCredalTruthValue hiddenLabelSwapFamily [((), 0)] 0
      hiddenLabelSwapFamily_observed_nonzero).lower = 0 := by
  exact hiddenLabelSwapFamily_lower_eq_zero

/-- Negative example: the observed-only credal interval need not collapse to a
point, even for a singleton observed cycle. -/
example :
    (filteringCredalTruthValue hiddenLabelSwapFamily [((), 0)] 0
      hiddenLabelSwapFamily_observed_nonzero).upper = 1 := by
  exact hiddenLabelSwapFamily_upper_eq_one

end LabelSwapWitness

section ReselectionControl

private def quarterWeight (high : Bool) (y : Fin 2) : ℝ≥0 :=
  if y = 1 then (if high then 3 / 4 else 1 / 4)
  else (if high then 1 / 4 else 3 / 4)

private def quarterCoin (high : Bool) : MeasureTheory.ProbabilityMeasure (Fin 2) := by
  let p : PMF (Fin 2) := PMF.ofFintype (fun y => (quarterWeight high y : ℝ≥0∞))
    (by
      rw [Fin.sum_univ_two, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj]
      cases high <;> norm_num [quarterWeight])
  exact ⟨p.toMeasure, by infer_instance⟩

@[simp] private theorem quarterCoin_singleton (high : Bool) (y : Fin 2) :
    (quarterCoin high).toMeasure (Set.singleton y) = (quarterWeight high y : ℝ≥0∞) := by
  change (PMF.ofFintype (fun y => (quarterWeight high y : ℝ≥0∞)) _).toMeasure (Set.singleton y) = _
  exact PMF.toMeasure_apply_singleton _ y (measurableSet_singleton y)

@[simp] private theorem quarterCoin_nnreal (high : Bool) (y : Fin 2) :
    quarterCoin high (Set.singleton y) = quarterWeight high y := by
  apply ENNReal.coe_injective
  rw [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, quarterCoin_singleton]

/-- A clock with success probabilities `(1/4,3/4)` or `(3/4,1/4)` in its first two cycles. -/
noncomputable def alternatingRewardHMM (i : Fin 2) : ControlledFiniteHMMParam Unit 3 2 where
  init := diracPM 0
  trans := fun _ x => diracPM (if x = 0 then 1 else 2)
  emission := fun x => quarterCoin (if x = 1 then decide (i = 1) else decide (i = 0))

private theorem alternatingReward_initial (i : Fin 2) (y : Fin 2) :
    traceMassRow (alternatingRewardHMM i) [] () y = (quarterWeight (decide (i = 1)) y : ℝ≥0∞) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 := Ne.symm h02
  have h21 := Ne.symm h12
  fin_cases i <;> fin_cases y <;>
    norm_num [*, traceMassRow, observationMassGivenAction, filteringMass, filteringMassAux,
      initialLatentMass, filteringStepMass, predictiveLatentMass, alternatingRewardHMM,
      stepProb, emissionProb, initProb, diracPM, Fin.sum_univ_three, quarterWeight, quarterCoin_nnreal, quarterCoin_singleton]

private theorem alternatingReward_after_one (i : Fin 2) (b y : Fin 2) :
    traceMassRow (alternatingRewardHMM i) [((), b)] () y =
      (quarterWeight (decide (i = 1)) b : ℝ≥0∞) * (quarterWeight (decide (i = 0)) y : ℝ≥0∞) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 := Ne.symm h02
  have h21 := Ne.symm h12
  fin_cases i <;> fin_cases b <;> fin_cases y <;>
    norm_num [*, traceMassRow, observationMassGivenAction, filteringMass, filteringMassAux,
      initialLatentMass, filteringStepMass, predictiveLatentMass, alternatingRewardHMM,
      stepProb, emissionProb, initProb, diracPM, Fin.sum_univ_three, quarterWeight, quarterCoin_nnreal, quarterCoin_singleton]

/-- Every finite trace in the separating family has positive mass. -/
theorem alternatingReward_all_traces_possible (i : Fin 2) (zs : List (CycleObservation Unit 2)) :
    observedCycleProb (alternatingRewardHMM i) zs ≠ 0 := by
  apply observedCycleProb_ne_zero_of_emissions
  intro x y
  change (quarterCoin _ (Set.singleton y)) ≠ 0
  intro h
  have hh := congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) h
  simp only [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    quarterCoin_singleton, ENNReal.coe_zero, ENNReal.coe_eq_zero] at hh
  unfold quarterWeight at hh
  split_ifs at hh <;> norm_num at hh

private def unitPolicy : Agent Unit (Fin 2) where
  policy := fun _ _ => 1
  policy_sum_one := by intros; simp

local instance : PerceptReward (Fin 2) where
  reward y := if y = 1 then 1 else 0
  reward_nonneg y := by split_ifs <;> norm_num
  reward_le_one y := by split_ifs <;> norm_num

private def undiscounted : DiscountFactor := ⟨1, by norm_num, by norm_num⟩

private theorem inf_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f 0) (f 1) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (Finset.mem_univ 0)) (Finset.inf'_le _ (Finset.mem_univ 1))
  · exact Finset.le_inf' _ _ fun i _ => by fin_cases i <;> simp

private theorem unitValue_succ (θ : ControlledFiniteHMMParam Unit 3 2)
    (zs : List (CycleObservation Unit 2)) (n : ℕ) :
    value (toEnvironment θ) unitPolicy undiscounted (historyOfCycles zs) (n + 1) =
      qValue (toEnvironment θ) unitPolicy undiscounted (historyOfCycles zs) () n := by
  rw [value_succ]
  simp [unitPolicy, historyOfCycles_wellFormed]

/-- Both fixed models have positive trace mass; row re-selection is still strictly more pessimistic. -/
theorem alternatingReward_static_lower :
    lowerStaticTraceMassValue alternatingRewardHMM unitPolicy undiscounted [] 4 = 23 / 32 := by
  simp only [lowerStaticTraceMassValue, inf_fin_two, unitValue_succ,
    qValue_succ_eq_traceMassContinuation, value_zero]
  norm_num [traceMassContinuation, alternatingReward_initial, alternatingReward_after_one,
    undiscounted, PerceptReward.reward, quarterWeight, Fin.sum_univ_two]

/-- The same family, policy and horizon give a smaller value when rows may be re-selected. -/
theorem alternatingReward_reselecting_lower :
    lowerRecursiveTraceMassValueEnvelope alternatingRewardHMM unitPolicy undiscounted [] 4 = 11 / 32 := by
  simp only [lowerRecursiveTraceMassValueEnvelope, lowerRecursiveTraceMassQValueEnvelope,
    inf_fin_two]
  norm_num [traceMassContinuation, unitPolicy, undiscounted, PerceptReward.reward,
    alternatingReward_initial, alternatingReward_after_one, quarterWeight, Fin.sum_univ_two]

/-- A supported history still has subunit next-row mass. -/
theorem alternatingReward_row_mass :
    ∑ y : Fin 2, traceMassRow (alternatingRewardHMM 0) [((), 0)] () y = 3 / 4 := by
  rw [traceMassRow_sum]
  change observedCycleProb (alternatingRewardHMM 0) ([] ++ [((), 0)]) = _
  rw [observedCycleProb_append_eq_traceMassRow, alternatingReward_initial]
  norm_num [quarterWeight]

example : (∑ y : Fin 2, traceMassRow (alternatingRewardHMM 0) [((), 0)] () y) ≠ 1 := by
  rw [alternatingReward_row_mass]
  intro h
  have hh := congrArg ENNReal.toReal h
  norm_num at hh

/-- Static and history-dependent row choices need not give the same fixed-policy value. -/
theorem alternatingReward_reselection_strict :
    lowerRecursiveTraceMassValueEnvelope alternatingRewardHMM unitPolicy undiscounted [] 4 <
      lowerStaticTraceMassValue alternatingRewardHMM unitPolicy undiscounted [] 4 := by
  rw [alternatingReward_reselecting_lower, alternatingReward_static_lower]
  norm_num

end ReselectionControl

end Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal
