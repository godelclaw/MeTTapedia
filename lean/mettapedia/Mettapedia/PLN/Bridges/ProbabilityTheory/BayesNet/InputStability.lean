import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.EnsembleInformationError
import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability

/-!
# Native BN query certificates with perturbed readouts

These theorems refer to the existing variable-elimination query. A singleton
certificate separates conditional dependence from premise perturbation. The
multiset certificate additionally retains the nonlinear model-aggregation gap.
The input-stability margin concerns the middle event; query support concerns
the antecedent event and is a different condition.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.InputStability

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteEnsemble
open Mettapedia.PLN.Comparisons.DeductionStability
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInputStability
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.ScreeningError
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.EnsembleInformationError
open Mettapedia.InformationTheory.FiniteRV

variable {V : Type*} [Fintype V] [DecidableEq V] {bn : BayesianNetwork V}
  [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
  [∀ v, DecidableEq (bn.stateSpace v)] [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
  [DecidableRel bn.graph.edges]

/-- The actual singleton-CPT query combines dependence and premise-perturbation budgets. -/
theorem wm_query_with_perturbed_readouts (model : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v) (approximate : PremiseValues) (margin : ℝ)
    (possible : 0 < mass (realWeight model) (atomObservations atoms 0))
    (positive : 0 < margin)
    (sourceSeparated : margin ≤ 1-mass (realWeight model) (atomObservations atoms 1))
    (approximateSeparated : margin ≤ 1-(approximate.b : ℝ)) :
    |(BinaryWorldModel.queryStrength ({model} : BNWorldModel.State (bn := bn))
        (AtomQuery.link (atoms 0) (atoms 2))).toReal - estimate approximate| ≤
      modelBudget model atoms + perturbationBudget margin
        (premises (observedJoint model (atomObservations atoms)) 0 1 2) approximate := by
  rw [wm_link_eq_observed_conditional model atoms (atom_measure_ne_zero_of_pos model _ possible)]
  have bound := query_error_with_perturbed_readouts (observedJoint model (atomObservations atoms))
    0 1 2 approximate margin (by simpa only [observed_marginal] using possible) positive
    (by simpa only [observed_marginal] using sourceSeparated) approximateSeparated
  simpa only [completeDeduction, observed_marginal, modelBudget] using bound

omit [∀ v, Nonempty (bn.stateSpace v)] [∀ v, MeasurableSingletonClass (bn.stateSpace v)] in
private theorem readout_unit (models : BNWorldModel.State (bn := bn))
    (query : AtomQuery (Σ v, bn.stateSpace v)) :
    (BinaryWorldModel.queryStrength models query).toReal ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · change (BinaryEvidence.toStrength (BNWorldModel.evidence models query)).toReal ≤ 1
    have bound := ENNReal.toReal_mono ENNReal.one_ne_top
      (BinaryEvidence.toStrength_le_one (BNWorldModel.evidence models query))
    simpa only [ENNReal.toReal_one] using bound

/-- Named premise readouts from the native CPT-multiset world model. -/
noncomputable def pooledPremises (models : BNWorldModel.State (bn := bn))
    (atoms : Fin 3 → Σ v, bn.stateSpace v) : PremiseValues where
  ab := ⟨(BinaryWorldModel.queryStrength models (AtomQuery.link (atoms 0) (atoms 1))).toReal,
    readout_unit models _⟩
  bc := ⟨(BinaryWorldModel.queryStrength models (AtomQuery.link (atoms 1) (atoms 2))).toReal,
    readout_unit models _⟩
  b := ⟨(BinaryWorldModel.queryStrength models (AtomQuery.prop (atoms 1))).toReal,
    readout_unit models _⟩
  c := ⟨(BinaryWorldModel.queryStrength models (AtomQuery.prop (atoms 2))).toReal,
    readout_unit models _⟩

/-- Keep component dependence, nonlinear aggregation and input perturbation as three separate terms. -/
theorem wm_ensemble_with_perturbed_readouts (models : BNWorldModel.State (bn := bn))
    (atoms : Fin 3 → Σ v, bn.stateSpace v) (approximate : PremiseValues) (margin : ℝ)
    (nonempty : 0 < models.card)
    (possible : ∀ model ∈ models, 0 < mass (realWeight model) (atomObservations atoms 0))
    (positive : 0 < margin)
    (sourceSeparated : margin ≤ 1-((pooledPremises models atoms).b : ℝ))
    (approximateSeparated : margin ≤ 1-(approximate.b : ℝ)) :
    |(BinaryWorldModel.queryStrength models (AtomQuery.link (atoms 0) (atoms 2))).toReal -
      estimate approximate| ≤
      mean models (fun model => modelBudget model atoms) + aggregationGap models atoms +
        perturbationBudget margin (pooledPremises models atoms) approximate := by
  exact (abs_sub_le _ (pooledEstimate models atoms) _).trans
    (add_le_add (wm_ensemble_error_le models atoms nonempty possible)
      (estimate_stable (pooledPremises models atoms) approximate margin positive
        sourceSeparated approximateSeparated))

end Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.InputStability
