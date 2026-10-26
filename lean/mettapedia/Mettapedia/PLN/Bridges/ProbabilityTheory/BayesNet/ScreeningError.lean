import Mettapedia.PLN.Core.FiniteJointPushforward
import Mettapedia.PLN.Comparisons.ModelErrorBounds
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
import Mettapedia.PLN.WorldModel.ProbabilityPooling

/-!
# Native Bayesian-network query certificates

A CPT supplies a coherent finite observation law, while the native WM computes
its own VE answer. Their interpretation theorem transports screening, credal,
and CMI certificates without identifying the two computations by definition.
The conditioning event must be possible; internal Boolean branches may be empty.

A multiset WM averages normalized component answers, not joint laws. Its radius
therefore retains both mean component dependence and the nonlinear aggregation
gap. Model discrepancy and premise perturbation add separate terms; the latter
requires a middle-event margin. Information is measured in nats.
-/

open scoped BigOperators ENNReal
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.FiniteEventMass Mettapedia.ProbabilityTheory.FiniteEnsemble
open Mettapedia.PLN.Core.CompletePLN Mettapedia.PLN.Core.FiniteJointPushforward
open Mettapedia.PLN.Comparisons.DeductionStability Mettapedia.PLN.Comparisons.ModelErrorBounds
open Mettapedia.PLN.Comparisons.ErrorCharacterization Mettapedia.PLN.Comparisons.ScreeningErrorBounds
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointDistribution
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointBalancedInformation
open Mettapedia.PLN.WorldModel Mettapedia.PLN.WorldModel.ProbabilityPooling

variable {V : Type*} [Fintype V] [DecidableEq V] {bn : BayesianNetwork V}
  [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]

variable (cpt : bn.DiscreteCPT) (observations : Fin 3 → bn.JointSpace → Bool)

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet

namespace ScreeningError
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

/-- Balanced information radius of actual CPT observations, using their native mass. -/
noncomputable def observedInformationRadius (cpt : bn.DiscreteCPT)
    (observations : Fin 3 → bn.JointSpace → Bool) : ℝ :=
  balancedRadius (mass (realWeight cpt) (observations 0))
    (deductionInformation (observedJoint cpt observations) 0 1 2)

/-- The query-level screening error bound applies to the independently
computed conditional of the CPT's source worlds. -/
theorem cpt_query_error_le_conservative
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
  simpa only [credalRadius, deductionPremises, completeDeduction, observed_conditional] using bound

/-- The sharper interval radius uses only the five deduction readouts and
holds on the actual BN query without screening. -/
theorem cpt_query_error_le_credal_radius
    (possible : 0 < mass (realWeight cpt) (observations 0))
    (estimate : ℝ) :
    |mass (realWeight cpt) (fun world => observations 2 world && observations 0 world) /
        mass (realWeight cpt) (observations 0) - estimate| ≤
      credalRadius (marginalProb (observedJoint cpt observations) 0)
        (deductionPremises (observedJoint cpt observations) 0 1 2) estimate := by
  have hA : 0 < marginalProb (observedJoint cpt observations) 0 := by
    simpa only [observed_marginal] using possible
  have bound := query_error_le_credal_radius (observedJoint cpt observations) 0 1 2 hA estimate
  simpa only [credalRadius, deductionPremises, completeDeduction, observed_conditional] using bound

end ScreeningError

open ScreeningError

namespace BalancedInformationError

/-- Query error of the CPT's actual finite worlds. -/
theorem cpt_query_error_le_sqrt_balanced_cmi
    (possible : 0 < mass (realWeight cpt) (observations 0)) :
    |mass (realWeight cpt) (fun world => observations 2 world && observations 0 world) /
        mass (realWeight cpt) (observations 0) -
      estimate (deductionPremises (observedJoint cpt observations) 0 1 2)| ≤
      observedInformationRadius cpt observations := by
  simpa only [completeDeduction, observed_conditional, deductionRadius, balancedRadius,
    informationRadius, observedInformationRadius, observed_marginal] using
    query_error_le_sqrt_balanced_cmi (observedJoint cpt observations) 0 1 2
      (by simpa only [observed_marginal] using possible)

end BalancedInformationError

namespace InformationError

theorem cpt_query_error_le_sqrt_cmi
    (possible : 0 < mass (realWeight cpt) (observations 0)) :
    |mass (realWeight cpt) (fun world => observations 2 world && observations 0 world) /
        mass (realWeight cpt) (observations 0) -
      estimate (deductionPremises (observedJoint cpt observations) 0 1 2)| ≤
      informationRadius (mass (realWeight cpt) (observations 0))
        (deductionInformation (observedJoint cpt observations) 0 1 2) := by
  simpa only [completeDeduction, observed_conditional, deductionRadius, balancedRadius,
    informationRadius, observedInformationRadius, observed_marginal] using
    query_error_le_sqrt_cmi (observedJoint cpt observations) 0 1 2
      (by simpa only [observed_marginal] using possible)

end InformationError

variable [∀ v, DecidableEq (bn.stateSpace v)]
  [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [DecidableRel bn.graph.edges]


namespace ScreeningError

omit [∀ v, DecidableEq (bn.stateSpace v)] [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
  [DecidableRel bn.graph.edges] in
/-- The real-valued finite event sum agrees with the independently constructed
joint probability measure. Measurability is explicit. -/
theorem real_mass_eq_jointMeasure (cpt : bn.DiscreteCPT) (event : bn.JointSpace → Bool)
    (measurable : MeasurableSet {world | event world = true}) :
    mass (realWeight cpt) event = (cpt.jointMeasure {world | event world = true}).toReal := by
  classical
  rw [cpt.jointMeasure_apply_as_sum measurable, ENNReal.toReal_sum]
  · simp only [mass, realWeight]
    exact Finset.sum_congr rfl fun world _ => by split_ifs <;> simp_all
  · intro world _; split_ifs <;> simp_all [jointWeight_finite]

/-- Value-labeled BN atoms supply Boolean observations without identifying
distinct vertices or distinct state values. -/
def atomObservations (atoms : Fin 3 → Σ v, bn.stateSpace v) : Fin 3 → bn.JointSpace → Bool :=
  fun i world => decide (world (atoms i).1 = (atoms i).2)

omit [DecidableRel bn.graph.edges] in
theorem atom_mass_eq_jointMeasure (cpt : bn.DiscreteCPT) (atom : Σ v, bn.stateSpace v) :
    mass (realWeight cpt) (fun world => decide (world atom.1 = atom.2)) =
      (cpt.jointMeasure (eventEq (bn := bn) atom.1 atom.2)).toReal := by
  simpa only [decide_eq_true_eq, eventEq] using
    real_mass_eq_jointMeasure cpt (fun world => decide (world atom.1 = atom.2))
      (by simpa only [decide_eq_true_eq, eventEq] using measurable_eventEq (bn := bn) atom.1 atom.2)

omit [DecidableRel bn.graph.edges] in
theorem atom_measure_ne_zero_of_pos (cpt : bn.DiscreteCPT) (atom : Σ v, bn.stateSpace v)
    (positive : 0 < mass (realWeight cpt) (fun world => decide (world atom.1 = atom.2))) :
    cpt.jointMeasure (eventEq (bn := bn) atom.1 atom.2) ≠ 0 := by
  intro impossible
  rw [atom_mass_eq_jointMeasure, impossible, ENNReal.toReal_zero] at positive
  exact lt_irrefl 0 positive

/-- The real native WM answer, with its existing unit-interval guarantee. -/
noncomputable def queryReadout (models : PLNBNCompilation.BNWorldModel.State (bn := bn))
    (query : Mettapedia.PLN.WorldModel.AtomQuery (Σ v, bn.stateSpace v)) : Set.Icc (0 : ℝ) 1 :=
  ⟨(Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models query).toReal,
    ENNReal.toReal_nonneg, by
      exact (ENNReal.toReal_mono ENNReal.one_ne_top
        (Mettapedia.PLN.Evidence.BinaryEvidence.toStrength_le_one _)).trans_eq ENNReal.toReal_one⟩

/-- Component radius specialized to value-labeled atoms, not to pooled conditionals. -/
noncomputable def componentInformationRadius (model : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  observedInformationRadius model (atomObservations atoms)

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
    |(queryReadout {cpt} (Mettapedia.PLN.WorldModel.AtomQuery.link (atoms 0) (atoms 2)) : ℝ) -
        screeningDeduction (observedJoint cpt (atomObservations atoms)) 0 1 2| ≤
      conservativeErrorEstimate
        (condProb (observedJoint cpt (atomObservations atoms)) 1 0)
        (condProb (observedJoint cpt (atomObservations atoms)) 2 1)
        (condProbNeg (observedJoint cpt (atomObservations atoms)) 2 1) := by
  simpa only [queryReadout, Subtype.coe_mk, wm_link_eq_observed_conditional cpt atoms
    (atom_measure_ne_zero_of_pos cpt _ possible), observed_conditional] using
    cpt_query_error_le_conservative cpt (atomObservations atoms) possible

/-- The WM query enjoys the sharper five-readout bound as well. The internal
`B` branch may be empty. Sharpness over all compatible joint models does not
assert that the extremizer respects every extra constraint of a fixed BN. -/
theorem wm_query_error_le_credal_radius (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : 0 < mass (realWeight cpt) (atomObservations atoms 0)) (estimate : ℝ) :
    |(queryReadout {cpt} (Mettapedia.PLN.WorldModel.AtomQuery.link (atoms 0) (atoms 2)) : ℝ) - estimate| ≤
      credalRadius (marginalProb (observedJoint cpt (atomObservations atoms)) 0)
        (deductionPremises (observedJoint cpt (atomObservations atoms)) 0 1 2) estimate := by
  simpa only [queryReadout, Subtype.coe_mk, wm_link_eq_observed_conditional cpt atoms
    (atom_measure_ne_zero_of_pos cpt _ possible), observed_conditional] using
    cpt_query_error_le_credal_radius cpt (atomObservations atoms) possible estimate

end ScreeningError

namespace BalancedInformationError

/-- The singleton WM answer is evaluated by the existing variable-elimination semantics. -/
theorem wm_query_error_le_sqrt_balanced_cmi (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : 0 < mass (realWeight cpt) (atomObservations atoms 0)) :
    |(queryReadout {cpt} (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) -
      estimate (deductionPremises (observedJoint cpt (atomObservations atoms)) 0 1 2)| ≤
      observedInformationRadius cpt (atomObservations atoms) := by
  change |(BinaryWorldModel.queryStrength _ _).toReal - _| ≤ _
  rw [wm_link_eq_observed_conditional cpt atoms (atom_measure_ne_zero_of_pos cpt _ possible)]
  simpa only [observed_conditional] using cpt_query_error_le_sqrt_balanced_cmi cpt
    (atomObservations atoms) possible

/-- Model mismatch is added to the working law's own dependence certificate. -/
theorem wm_model_and_balanced_information_error_le (source working : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (sourcePossible : 0 < mass (realWeight source) (atomObservations atoms 0))
    (workingPossible : 0 < mass (realWeight working) (atomObservations atoms 0)) :
    |(queryReadout {source} (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) -
      estimate (deductionPremises (observedJoint working (atomObservations atoms)) 0 1 2)| ≤
      queryModelErrorBound (observedJoint source (atomObservations atoms))
        (observedJoint working (atomObservations atoms)) 0 + observedInformationRadius working (atomObservations atoms) := by
  change |(BinaryWorldModel.queryStrength _ _).toReal - _| ≤ _
  rw [wm_link_eq_observed_conditional source atoms (atom_measure_ne_zero_of_pos source _ sourcePossible)]
  simpa only [completeDeduction, deductionRadius, balancedRadius, informationRadius,
    observedInformationRadius, observed_marginal] using
    model_and_balanced_information_error_le (observedJoint source (atomObservations atoms))
      (observedJoint working (atomObservations atoms)) 0 1 2
      (by simpa only [observed_marginal] using sourcePossible)
      (by simpa only [observed_marginal] using workingPossible)

end BalancedInformationError

namespace InformationError

theorem wm_query_error_le_sqrt_cmi (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : 0 < mass (realWeight cpt) (atomObservations atoms 0)) :
    |(queryReadout {cpt} (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) -
      estimate (deductionPremises (observedJoint cpt (atomObservations atoms)) 0 1 2)| ≤
      informationRadius (mass (realWeight cpt) ((atomObservations atoms) 0))
        (deductionInformation (observedJoint cpt (atomObservations atoms)) 0 1 2) := by
  change |(BinaryWorldModel.queryStrength _ _).toReal - _| ≤ _
  rw [wm_link_eq_observed_conditional cpt atoms (atom_measure_ne_zero_of_pos cpt _ possible)]
  simpa only [observed_conditional] using cpt_query_error_le_sqrt_cmi cpt
    (atomObservations atoms) possible

theorem wm_model_and_information_error_le (source working : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (sourcePossible : 0 < mass (realWeight source) (atomObservations atoms 0))
    (workingPossible : 0 < mass (realWeight working) (atomObservations atoms 0)) :
    |(queryReadout {source} (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) -
      estimate (deductionPremises (observedJoint working (atomObservations atoms)) 0 1 2)| ≤
      queryModelErrorBound (observedJoint source (atomObservations atoms))
        (observedJoint working (atomObservations atoms)) 0 + informationRadius (mass (realWeight working) ((atomObservations atoms) 0))
        (deductionInformation (observedJoint working (atomObservations atoms)) 0 1 2) := by
  change |(BinaryWorldModel.queryStrength _ _).toReal - _| ≤ _
  rw [wm_link_eq_observed_conditional source atoms (atom_measure_ne_zero_of_pos source _ sourcePossible)]
  simpa only [completeDeduction, deductionRadius, balancedRadius, informationRadius,
    observedInformationRadius, observed_marginal] using
    model_and_information_error_le (observedJoint source (atomObservations atoms))
      (observedJoint working (atomObservations atoms)) 0 1 2
      (by simpa only [observed_marginal] using sourcePossible)
      (by simpa only [observed_marginal] using workingPossible)

end InformationError

open PLNBNCompilation

variable (models : PLNBNCompilation.BNWorldModel.State (bn := bn))

namespace EnsembleInformationError

/-- Arithmetic mean of the native per-CPT query answers. -/
noncomputable def queryMean (query : AtomQuery (Σ v, bn.stateSpace v)) : ℝ :=
  mean models (fun model => (BNWorldModel.queryProb model query).toReal)

omit [∀ v, Nonempty (bn.stateSpace v)] [∀ v, MeasurableSingletonClass (bn.stateSpace v)] in
/-- The existing BN multiset implementation averages normalized component answers. -/
theorem wm_query_is_model_mean (query : AtomQuery (Σ v, bn.stateSpace v))
    (bounded : ∀ model ∈ models, BNWorldModel.queryProb model query ≤ 1)
    (nonempty : 0 < models.card) :
    (Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models query).toReal =
      queryMean models query := by
  have evidence : BNWorldModel.evidence models query =
      pool (models.map fun model => BNWorldModel.queryProb model query) := by
    simp [BNWorldModel.evidence, BNWorldModel.queryEvidence, BNWorldModel.evidenceOfProb,
      pool, Multiset.map_map]
  change (Mettapedia.PLN.Evidence.BinaryEvidence.toStrength (BNWorldModel.evidence models query)).toReal = _
  rw [evidence, pool_strength_mean]
  · simp [queryMean, mean, Multiset.map_map]
  · intro probability member
    obtain ⟨model, modelMember, same⟩ := Multiset.mem_map.mp member
    rw [← same]
    exact bounded model modelMember
  · simpa using nonempty

/-- Component estimates use one coherent observed joint law. -/
noncomputable def modelEstimate (model : bn.DiscreteCPT) (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  estimate (deductionPremises (observedJoint model (atomObservations atoms)) 0 1 2)

/-- Native pooled readouts need not jointly realize any single probability law. -/
noncomputable def pooledPremises (atoms : Fin 3 → Σ v, bn.stateSpace v) : PremiseValues where
  ab := queryReadout models (AtomQuery.link (atoms 0) (atoms 1))
  bc := queryReadout models (AtomQuery.link (atoms 1) (atoms 2))
  b := queryReadout models (AtomQuery.prop (atoms 1))
  c := queryReadout models (AtomQuery.prop (atoms 2))

/-- Nonlinear deduction after pooling normalized native answers. -/
noncomputable def pooledEstimate (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ := estimate (pooledPremises models atoms)

/-- The discrepancy introduced by exchanging nonlinear estimation and model averaging. -/
noncomputable def aggregationGap (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  |mean models (fun model => modelEstimate model atoms) - pooledEstimate models atoms|

/-- Dependence averaged within components, plus the nonlinear pooling gap. -/
noncomputable def ensembleRadius (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  mean models (fun model => componentInformationRadius model atoms) + aggregationGap models atoms

/-- An ensemble certificate retains both within-model dependence and between-model aggregation error. -/
theorem wm_ensemble_error_le (atoms : Fin 3 → Σ v, bn.stateSpace v) (nonempty : 0 < models.card)
    (possible : ∀ model ∈ models, 0 < mass (realWeight model) (atomObservations atoms 0)) :
    |(queryReadout models (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) - pooledEstimate models atoms| ≤
      ensembleRadius models atoms := by
  change |(BinaryWorldModel.queryStrength _ _).toReal - _| ≤
    mean models (fun model => componentInformationRadius model atoms) + aggregationGap models atoms
  rw [wm_query_is_model_mean models _
    (fun model _ => BNWorldModel.queryProb_link_le_one model _ _ _ _) nonempty]
  apply mean_error_with_aggregation
  intro model member
  have bound := BalancedInformationError.wm_query_error_le_sqrt_balanced_cmi model atoms
    (possible model member)
  dsimp only [queryReadout, Subtype.coe_mk] at bound
  rw [BNWorldModel.queryStrength_singleton_eq_queryProb model _
    (BNWorldModel.queryProb_link_le_one model _ _ _ _)] at bound
  exact bound

end EnsembleInformationError

namespace InputStability

open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.EnsembleInformationError

/-- The actual singleton-CPT query combines dependence and premise-perturbation budgets. -/
theorem wm_query_with_perturbed_readouts (model : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v) (approximate : PremiseValues) (margin : ℝ)
    (possible : 0 < mass (realWeight model) (atomObservations atoms 0))
    (positive : 0 < margin)
    (sourceSeparated : margin ≤ 1-mass (realWeight model) (atomObservations atoms 1))
    (approximateSeparated : margin ≤ 1-(approximate.b : ℝ)) :
    |(queryReadout {model} (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) - estimate approximate| ≤
      componentInformationRadius model atoms + perturbationBudget margin
        (FiniteJointDistribution.deductionPremises (observedJoint model (atomObservations atoms)) 0 1 2) approximate := by
  change |(BinaryWorldModel.queryStrength _ _).toReal - _| ≤ _
  rw [wm_link_eq_observed_conditional model atoms (atom_measure_ne_zero_of_pos model _ possible)]
  have bound := query_error_with_perturbed_readouts (observedJoint model (atomObservations atoms))
    0 1 2 approximate margin (by simpa only [observed_marginal] using possible) positive
    (by simpa only [observed_marginal] using sourceSeparated) approximateSeparated
  simpa only [completeDeduction, observed_marginal, componentInformationRadius, observedInformationRadius, deductionRadius, balancedRadius] using bound

/-- Keep component dependence, nonlinear aggregation and input perturbation as three separate terms. -/
theorem wm_ensemble_with_perturbed_readouts (atoms : Fin 3 → Σ v, bn.stateSpace v) (approximate : PremiseValues) (margin : ℝ)
    (nonempty : 0 < models.card)
    (possible : ∀ model ∈ models, 0 < mass (realWeight model) (atomObservations atoms 0))
    (positive : 0 < margin)
    (sourceSeparated : margin ≤ 1-((pooledPremises models atoms).b : ℝ))
    (approximateSeparated : margin ≤ 1-(approximate.b : ℝ)) :
    |(queryReadout models (AtomQuery.link (atoms 0) (atoms 2)) : ℝ) - estimate approximate| ≤
      mean models (fun model => componentInformationRadius model atoms) + aggregationGap models atoms +
        perturbationBudget margin (pooledPremises models atoms) approximate := by
  exact (abs_sub_le _ (pooledEstimate models atoms) _).trans
    (add_le_add (wm_ensemble_error_le models atoms nonempty possible)
      (estimate_stable (pooledPremises models atoms) approximate margin positive
        sourceSeparated approximateSeparated))

end InputStability

end Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet
