import Mettapedia.PLN.Core.FiniteJointPushforward
import Mettapedia.PLN.Comparisons.ScreeningErrorBounds
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation

/-!
# Dependence-error bounds on actual Bayesian-network worlds

The CPT joint weights supply the probability table; normalization and
nonnegativity are proved by the existing discrete BN semantics. Pushing that
table forward along selected Boolean queries derives the joint distribution
used by the PLN error bounds. No conditional-independence premise or assumed
branch allocation enters this bridge.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.ScreeningError

open scoped BigOperators ENNReal
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Core.FiniteJointPushforward
open Mettapedia.PLN.Comparisons.ErrorCharacterization
open Mettapedia.PLN.Comparisons.ScreeningErrorBounds

variable {V : Type*} [Fintype V] [DecidableEq V] {bn : BayesianNetwork V}
  [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]

noncomputable def realWeight (cpt : bn.DiscreteCPT) (world : bn.JointSpace) : ℝ :=
  (cpt.jointWeight world).toReal

omit [DecidableEq V] [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)] in
theorem realWeight_nonneg (cpt : bn.DiscreteCPT) (world : bn.JointSpace) :
    0 ≤ realWeight cpt world := ENNReal.toReal_nonneg

theorem jointWeight_finite (cpt : bn.DiscreteCPT) (world : bn.JointSpace) :
    cpt.jointWeight world ≠ ⊤ := cpt.jointPMF.apply_ne_top world

theorem realWeight_sum_one (cpt : bn.DiscreteCPT) : ∑ world, realWeight cpt world = 1 := by
  have normalized := congrArg ENNReal.toReal cpt.jointWeight_sum_eq_one
  rw [ENNReal.toReal_sum (fun world _ => jointWeight_finite cpt world)] at normalized
  simpa only [realWeight, ENNReal.toReal_one] using normalized

/-- Exact joint observations of the existing CPT semantics. -/
noncomputable def observedJoint {n : ℕ} (cpt : bn.DiscreteCPT)
    (observations : Fin n → bn.JointSpace → Bool) : JointDistribution n :=
  pushforward (realWeight cpt) (realWeight_nonneg cpt) (realWeight_sum_one cpt)
    (fun world i => observations i world)

theorem observed_marginal {n : ℕ} (cpt : bn.DiscreteCPT)
    (observations : Fin n → bn.JointSpace → Bool) (i : Fin n) :
    marginalProb (observedJoint cpt observations) i = mass (realWeight cpt) (observations i) :=
  marginal_pushforward _ _ _ _ _

theorem observed_conditional {n : ℕ} (cpt : bn.DiscreteCPT)
    (observations : Fin n → bn.JointSpace → Bool) (i j : Fin n) :
    condProb (observedJoint cpt observations) i j =
      mass (realWeight cpt) (fun world => observations i world && observations j world) /
        mass (realWeight cpt) (observations j) :=
  conditional_pushforward _ _ _ _ _ _

/-- The query-level screening error bound applies to the independently
computed conditional of the CPT's source worlds. -/
theorem cpt_query_error_le_conservative (cpt : bn.DiscreteCPT)
    (observations : Fin 3 → bn.JointSpace → Bool)
    (possible : 0 < mass (realWeight cpt) (observations 0)) :
    |mass (realWeight cpt) (fun world => observations 2 world && observations 0 world) /
        mass (realWeight cpt) (observations 0) -
      screeningDeduction (observedJoint cpt observations) 0 1 2| ≤
      conservativeErrorEstimate
        (condProb (observedJoint cpt observations) 1 0)
        (condProb (observedJoint cpt observations) 2 1)
        (condProbNeg (observedJoint cpt observations) 2 1) := by
  have hA : 0 < marginalProb (observedJoint cpt observations) 0 := by
    simpa only [observed_marginal] using possible
  have bound := query_error_le_conservative_estimate (observedJoint cpt observations) 0 1 2 hA
  simpa only [completeDeduction, observed_conditional] using bound

/-- The sharper interval radius uses only the five deduction readouts and
holds on the actual BN query without screening. -/
theorem cpt_query_error_le_credal_radius (cpt : bn.DiscreteCPT)
    (observations : Fin 3 → bn.JointSpace → Bool)
    (possible : 0 < mass (realWeight cpt) (observations 0))
    (estimate : ℝ) :
    |mass (realWeight cpt) (fun world => observations 2 world && observations 0 world) /
        mass (realWeight cpt) (observations 0) - estimate| ≤
      intervalErrorRadius
        (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthLower
          (marginalProb (observedJoint cpt observations) 0)
          (marginalProb (observedJoint cpt observations) 1)
          (marginalProb (observedJoint cpt observations) 2)
          (condProb (observedJoint cpt observations) 1 0)
          (condProb (observedJoint cpt observations) 2 1))
        (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthUpper
          (marginalProb (observedJoint cpt observations) 0)
          (marginalProb (observedJoint cpt observations) 1)
          (marginalProb (observedJoint cpt observations) 2)
          (condProb (observedJoint cpt observations) 1 0)
          (condProb (observedJoint cpt observations) 2 1)) estimate := by
  have hA : 0 < marginalProb (observedJoint cpt observations) 0 := by
    simpa only [observed_marginal] using possible
  have bound := query_error_le_credal_radius (observedJoint cpt observations) 0 1 2 hA estimate
  simpa only [completeDeduction, observed_conditional] using bound

section WorldModel

/-- The real-valued finite event sum agrees with the independently constructed
joint probability measure. Measurability is explicit. -/
theorem real_mass_eq_jointMeasure (cpt : bn.DiscreteCPT) (event : bn.JointSpace → Bool)
    (measurable : MeasurableSet {world | event world = true}) :
    mass (realWeight cpt) event = (cpt.jointMeasure {world | event world = true}).toReal := by
  classical
  rw [cpt.jointMeasure_apply_as_sum measurable, ENNReal.toReal_sum]
  · simp only [mass, realWeight, apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    apply Finset.sum_congr rfl
    intro world _
    split_ifs <;> simp_all
  · intro world _
    split_ifs
    · exact jointWeight_finite cpt world
    · exact ENNReal.zero_ne_top

variable [∀ v, DecidableEq (bn.stateSpace v)]
  [∀ v, MeasurableSingletonClass (bn.stateSpace v)]

/-- Value-labeled BN atoms supply Boolean observations without identifying
distinct vertices or distinct state values. -/
def atomObservations (atoms : Fin 3 → Σ v, bn.stateSpace v) : Fin 3 → bn.JointSpace → Bool :=
  fun i world => decide (world (atoms i).1 = (atoms i).2)

theorem atom_mass_eq_jointMeasure (cpt : bn.DiscreteCPT) (atom : Σ v, bn.stateSpace v) :
    mass (realWeight cpt) (fun world => decide (world atom.1 = atom.2)) =
      (cpt.jointMeasure (eventEq (bn := bn) atom.1 atom.2)).toReal := by
  simpa only [decide_eq_true_eq, eventEq] using
    real_mass_eq_jointMeasure cpt (fun world => decide (world atom.1 = atom.2))
      (by simpa only [decide_eq_true_eq, eventEq] using measurable_eventEq (bn := bn) atom.1 atom.2)

theorem atom_measure_ne_zero_of_pos (cpt : bn.DiscreteCPT) (atom : Σ v, bn.stateSpace v)
    (positive : 0 < mass (realWeight cpt) (fun world => decide (world atom.1 = atom.2))) :
    cpt.jointMeasure (eventEq (bn := bn) atom.1 atom.2) ≠ 0 := by
  intro impossible
  rw [atom_mass_eq_jointMeasure, impossible, ENNReal.toReal_zero] at positive
  exact lt_irrefl 0 positive

variable [DecidableRel bn.graph.edges]

/-- The finite-sum conditional is exactly the existing VE-based WM query
strength on a singleton CPT state. -/
theorem wm_link_eq_observed_conditional (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : cpt.jointMeasure (eventEq (bn := bn) (atoms 0).1 (atoms 0).2) ≠ 0) :
    (Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength
      ({cpt} : PLNBNCompilation.BNWorldModel.State (bn := bn))
      (Mettapedia.PLN.WorldModel.AtomQuery.link
        (atoms 0) (atoms 2))).toReal =
      condProb (observedJoint cpt (atomObservations atoms)) 2 0 := by
  rw [PLNBNCompilation.BNWorldModel.queryStrength_singleton_link_toReal cpt
    (atoms 0).1 (atoms 2).1 (atoms 0).2 (atoms 2).2 possible]
  rw [observed_conditional]
  unfold atomObservations
  rw [atom_mass_eq_jointMeasure]
  congr 1
  symm
  simpa only [Bool.and_eq_true, decide_eq_true_eq, eventEq, Set.ofPred_and, MeasureTheory.Measure.real] using
    real_mass_eq_jointMeasure cpt
      (fun world => decide (world (atoms 2).1 = (atoms 2).2) &&
        decide (world (atoms 0).1 = (atoms 0).2))
      (by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, Set.ofPred_and, eventEq] using
          (measurable_eventEq (bn := bn) (atoms 2).1 (atoms 2).2).inter
            (measurable_eventEq (bn := bn) (atoms 0).1 (atoms 0).2))

/-- A dependence-error guarantee for the actual WM/VE answer, rather than
only for an abstract conditional supplied by the caller. -/
theorem wm_query_error_le_conservative (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : 0 < mass (realWeight cpt) (atomObservations atoms 0)) :
    |(Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength
        ({cpt} : PLNBNCompilation.BNWorldModel.State (bn := bn))
        (Mettapedia.PLN.WorldModel.AtomQuery.link
          (atoms 0) (atoms 2))).toReal -
        screeningDeduction (observedJoint cpt (atomObservations atoms)) 0 1 2| ≤
      conservativeErrorEstimate
        (condProb (observedJoint cpt (atomObservations atoms)) 1 0)
        (condProb (observedJoint cpt (atomObservations atoms)) 2 1)
        (condProbNeg (observedJoint cpt (atomObservations atoms)) 2 1) := by
  rw [wm_link_eq_observed_conditional cpt atoms (atom_measure_ne_zero_of_pos cpt (atoms 0) possible)]
  have hA : 0 < marginalProb (observedJoint cpt (atomObservations atoms)) 0 := by
    simpa only [observed_marginal] using possible
  exact query_error_le_conservative_estimate _ _ _ _ hA

/-- The WM query enjoys the sharper five-readout bound as well. The internal
`B` branch may be empty. Sharpness over all compatible joint models does not
assert that the extremizer respects every extra constraint of a fixed BN. -/
theorem wm_query_error_le_credal_radius (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : 0 < mass (realWeight cpt) (atomObservations atoms 0)) (estimate : ℝ) :
    |(Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength
        ({cpt} : PLNBNCompilation.BNWorldModel.State (bn := bn))
        (Mettapedia.PLN.WorldModel.AtomQuery.link (atoms 0) (atoms 2))).toReal - estimate| ≤
      intervalErrorRadius
        (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthLower
          (marginalProb (observedJoint cpt (atomObservations atoms)) 0)
          (marginalProb (observedJoint cpt (atomObservations atoms)) 1)
          (marginalProb (observedJoint cpt (atomObservations atoms)) 2)
          (condProb (observedJoint cpt (atomObservations atoms)) 1 0)
          (condProb (observedJoint cpt (atomObservations atoms)) 2 1))
        (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthUpper
          (marginalProb (observedJoint cpt (atomObservations atoms)) 0)
          (marginalProb (observedJoint cpt (atomObservations atoms)) 1)
          (marginalProb (observedJoint cpt (atomObservations atoms)) 2)
          (condProb (observedJoint cpt (atomObservations atoms)) 1 0)
          (condProb (observedJoint cpt (atomObservations atoms)) 2 1)) estimate := by
  rw [wm_link_eq_observed_conditional cpt atoms (atom_measure_ne_zero_of_pos cpt (atoms 0) possible)]
  have hA : 0 < marginalProb (observedJoint cpt (atomObservations atoms)) 0 := by
    simpa only [observed_marginal] using possible
  exact query_error_le_credal_radius _ _ _ _ hA estimate

end WorldModel

end Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.ScreeningError
