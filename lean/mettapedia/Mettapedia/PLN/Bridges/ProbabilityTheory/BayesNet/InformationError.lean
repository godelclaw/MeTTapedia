import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.ScreeningError
import Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
import Mettapedia.PLN.Comparisons.ModelErrorBounds

/-!
# Information and model-error certificates for the BN world model

The CPT supplies the joint law and the existing variable-elimination bridge
supplies the WM answer. Conditional mutual information bounds the loss from
using the PLN deduction formula on this law. A second theorem allows a
different working CPT and retains its model discrepancy as a separate term.

All information quantities use natural logarithms. A positive conditioning
mass is required; the intermediate Boolean branches may have zero mass.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.InformationError

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.ScreeningError
open Mettapedia.PLN.Bridges.ProbabilityTheory.FiniteJointInformation
open Mettapedia.PLN.Comparisons.ModelErrorBounds
open Mettapedia.InformationTheory.FiniteRV

variable {V : Type*} [Fintype V] [DecidableEq V] {bn : BayesianNetwork V}
  [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]

/-- The finite-world CPT query has the information-error certificate without
an assumed conditional-independence equation. -/
theorem cpt_query_error_le_sqrt_cmi (cpt : bn.DiscreteCPT)
    (observations : Fin 3 → bn.JointSpace → Bool)
    (possible : 0 < mass (realWeight cpt) (observations 0)) :
    |mass (realWeight cpt) (fun world => observations 2 world && observations 0 world) /
        mass (realWeight cpt) (observations 0) -
      plnDeductionStrength (condProb (observedJoint cpt observations) 1 0)
        (condProb (observedJoint cpt observations) 2 1)
        (marginalProb (observedJoint cpt observations) 1)
        (marginalProb (observedJoint cpt observations) 2)| ≤
      Real.sqrt (condMutualInfo (observedJoint cpt observations).prob
        (worldToAssignment 3 · 0) (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) /
          (2 * mass (realWeight cpt) (observations 0))) := by
  have positive : 0 < marginalProb (observedJoint cpt observations) 0 := by
    simpa only [observed_marginal] using possible
  have bound := query_error_le_sqrt_cmi (observedJoint cpt observations) 0 1 2 positive
  simpa only [completeDeduction, observed_conditional, observed_marginal] using bound

section WorldModel

variable [∀ v, DecidableEq (bn.stateSpace v)]
  [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [DecidableRel bn.graph.edges]

/-- The actual singleton-CPT WM/VE query obeys the same information bound. -/
theorem wm_query_error_le_sqrt_cmi (cpt : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (possible : 0 < mass (realWeight cpt) (atomObservations atoms 0)) :
    |(Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength
        ({cpt} : PLNBNCompilation.BNWorldModel.State (bn := bn))
        (Mettapedia.PLN.WorldModel.AtomQuery.link (atoms 0) (atoms 2))).toReal -
      plnDeductionStrength (condProb (observedJoint cpt (atomObservations atoms)) 1 0)
        (condProb (observedJoint cpt (atomObservations atoms)) 2 1)
        (marginalProb (observedJoint cpt (atomObservations atoms)) 1)
        (marginalProb (observedJoint cpt (atomObservations atoms)) 2)| ≤
      Real.sqrt (condMutualInfo (observedJoint cpt (atomObservations atoms)).prob
        (worldToAssignment 3 · 0) (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) /
          (2 * mass (realWeight cpt) (atomObservations atoms 0))) := by
  rw [wm_link_eq_observed_conditional cpt atoms (atom_measure_ne_zero_of_pos cpt (atoms 0) possible)]
  have positive : 0 < marginalProb (observedJoint cpt (atomObservations atoms)) 0 := by
    simpa only [observed_marginal] using possible
  have bound := query_error_le_sqrt_cmi (observedJoint cpt (atomObservations atoms)) 0 1 2 positive
  simpa only [completeDeduction, observed_marginal] using bound

/-- A different working CPT incurs model error in addition to its own
screening loss. Both CPTs must support the query's conditioning event. -/
theorem wm_model_and_information_error_le (source working : bn.DiscreteCPT)
    (atoms : Fin 3 → Σ v, bn.stateSpace v)
    (sourcePossible : 0 < mass (realWeight source) (atomObservations atoms 0))
    (workingPossible : 0 < mass (realWeight working) (atomObservations atoms 0)) :
    |(Mettapedia.PLN.WorldModel.BinaryWorldModel.queryStrength
        ({source} : PLNBNCompilation.BNWorldModel.State (bn := bn))
        (Mettapedia.PLN.WorldModel.AtomQuery.link (atoms 0) (atoms 2))).toReal -
      plnDeductionStrength (condProb (observedJoint working (atomObservations atoms)) 1 0)
        (condProb (observedJoint working (atomObservations atoms)) 2 1)
        (marginalProb (observedJoint working (atomObservations atoms)) 1)
        (marginalProb (observedJoint working (atomObservations atoms)) 2)| ≤
      queryModelErrorBound (observedJoint source (atomObservations atoms))
        (observedJoint working (atomObservations atoms)) 0 +
      Real.sqrt (condMutualInfo (observedJoint working (atomObservations atoms)).prob
        (worldToAssignment 3 · 0) (worldToAssignment 3 · 1) (worldToAssignment 3 · 2) /
          (2 * mass (realWeight working) (atomObservations atoms 0))) := by
  rw [wm_link_eq_observed_conditional source atoms
    (atom_measure_ne_zero_of_pos source (atoms 0) sourcePossible)]
  have sourcePositive : 0 < marginalProb (observedJoint source (atomObservations atoms)) 0 := by
    simpa only [observed_marginal] using sourcePossible
  have workingPositive : 0 < marginalProb (observedJoint working (atomObservations atoms)) 0 := by
    simpa only [observed_marginal] using workingPossible
  have bound := model_and_information_error_le (observedJoint source (atomObservations atoms))
    (observedJoint working (atomObservations atoms)) 0 1 2 sourcePositive workingPositive
  simpa only [completeDeduction, observed_marginal] using bound

end WorldModel

end Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.InformationError
