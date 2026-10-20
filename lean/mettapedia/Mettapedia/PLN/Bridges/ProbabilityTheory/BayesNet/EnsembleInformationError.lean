import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.BalancedInformationError
import Mettapedia.PLN.WorldModel.ProbabilityPooling

/-!
# PLN error for the native multiset BN world model

The native BN world model pools already normalized query answers, giving each
CPT one unit of mass. Its conditional answers are arithmetic model means;
conditioning a mixture of joint distributions is a different operation.
A family of pooled conditional answers need not admit one joint realization;
`PLN.Comparisons.EnsembleIncompatibility` supplies a finite-table control.

The ensemble theorem combines balanced within-model conditional-mutual-
information budgets with the discrepancy between averaging component PLN
estimates and applying PLN to pooled premise answers. That discrepancy uses
premise readouts only. A positive conditioning-event mass is required in every
component. No change to the native world-model update or query is made here.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.EnsembleInformationError

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteEnsemble
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.ScreeningError
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.PLN.WorldModel.ProbabilityPooling
open Mettapedia.InformationTheory.FiniteRV

variable {V : Type*} [Fintype V] [DecidableEq V] {bn : BayesianNetwork V}
  [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
  [∀ v, DecidableEq (bn.stateSpace v)] [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
  [DecidableRel bn.graph.edges]

/-- Arithmetic mean of the native per-CPT query answers. -/
noncomputable def queryMean (models : BNWorldModel.State (bn := bn))
    (query : AtomQuery (Σ v, bn.stateSpace v)) : ℝ :=
  mean models (fun model => (BNWorldModel.queryProb model query).toReal)

omit [∀ v, Nonempty (bn.stateSpace v)] [∀ v, MeasurableSingletonClass (bn.stateSpace v)] in
/-- The existing BN multiset implementation averages normalized component answers. -/
theorem wm_query_is_model_mean (models : BNWorldModel.State (bn := bn))
    (query : AtomQuery (Σ v, bn.stateSpace v))
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

/-- PLN deduction applied to one component's observed premise probabilities. -/
noncomputable def modelEstimate (model : bn.DiscreteCPT) (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  plnDeductionStrength (condProb (observedJoint model (atomObservations atoms)) 1 0)
    (condProb (observedJoint model (atomObservations atoms)) 2 1)
    (marginalProb (observedJoint model (atomObservations atoms)) 1)
    (marginalProb (observedJoint model (atomObservations atoms)) 2)

/-- The balanced CMI certificate in nats for a single component. -/
noncomputable def modelBudget (model : bn.DiscreteCPT) (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  Real.sqrt ((1 - mass (realWeight model) (atomObservations atoms 0)) *
    condMutualInfo (observedJoint model (atomObservations atoms)).prob
      (worldToAssignment 3 · 0) (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) /
        (2 * mass (realWeight model) (atomObservations atoms 0)))

/-- PLN deduction applied to the native ensemble's pooled premise answers. -/
noncomputable def pooledEstimate (models : BNWorldModel.State (bn := bn))
    (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  plnDeductionStrength
    (Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models
      (AtomQuery.link (atoms 0) (atoms 1))).toReal
    (Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models
      (AtomQuery.link (atoms 1) (atoms 2))).toReal
    (Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models (AtomQuery.prop (atoms 1))).toReal
    (Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models (AtomQuery.prop (atoms 2))).toReal

/-- The discrepancy introduced by exchanging nonlinear estimation and model averaging. -/
noncomputable def aggregationGap (models : BNWorldModel.State (bn := bn))
    (atoms : Fin 3 → Σ v, bn.stateSpace v) : ℝ :=
  |mean models (fun model => modelEstimate model atoms) - pooledEstimate models atoms|

/-- An ensemble certificate retains both within-model dependence and between-model aggregation error. -/
theorem wm_ensemble_error_le (models : BNWorldModel.State (bn := bn))
    (atoms : Fin 3 → Σ v, bn.stateSpace v) (nonempty : 0 < models.card)
    (possible : ∀ model ∈ models, 0 < mass (realWeight model) (atomObservations atoms 0)) :
    |(Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength models
      (AtomQuery.link (atoms 0) (atoms 2))).toReal - pooledEstimate models atoms| ≤
      mean models (fun model => modelBudget model atoms) + aggregationGap models atoms := by
  rw [wm_query_is_model_mean models _
    (fun model _ => BNWorldModel.queryProb_link_le_one model _ _ _ _) nonempty]
  apply mean_error_with_aggregation
  intro model member
  have bound := BalancedInformationError.wm_query_error_le_sqrt_balanced_cmi model atoms
    (possible model member)
  rw [BNWorldModel.queryStrength_singleton_eq_queryProb model _
    (BNWorldModel.queryProb_link_le_one model _ _ _ _)] at bound
  exact bound

end Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.EnsembleInformationError
