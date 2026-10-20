import Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph
import Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

/-!
# Native finite factor graphs through polynomial module readouts

A chosen finite indexing supplies the reference table for the existing
factor-graph potential. The emitted tree evaluator computes every query mass
and the native partition function. Nonnegative potentials additionally give
an independently executed complete mass object, retaining its zero-total case.

Abstract finite indexing is noncomputable. The table compiler and its tree
evaluator are executable once a concrete finite table is supplied. These
results do not establish an efficient native optimizer or a runtime provider.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts
open Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation

variable {V K : Type*} [Fintype V] [DecidableEq V] [CommSemiring K]
  (graph : FactorGraph V K) [∀ v, Fintype (graph.stateSpace v)] [Fintype graph.factors]

local instance : Fintype graph.FullConfig := by
  unfold FactorGraph.FullConfig
  infer_instance

/-- Materialize the actual scoped potential lookup at the chosen finite indices. -/
noncomputable def table :
    Fin (Fintype.card graph.FullConfig) → Fin (Fintype.card graph.factors) → K :=
  fun world factor =>
    graph.potential ((Fintype.equivFin graph.factors).symm factor)
      (graph.restrictToScope ((Fintype.equivFin graph.factors).symm factor)
        ((Fintype.equivFin graph.FullConfig).symm world))

/-- A polynomial readout for all configurations selected by the query. -/
noncomputable def readout (query : graph.FullConfig → Bool) : Pattern :=
  compile (List.finRange (Fintype.card graph.FullConfig))
    (query ∘ (Fintype.equivFin graph.FullConfig).symm) (Fintype.card graph.factors)

/-- A row product recovers the native factor-graph joint potential. -/
theorem row_product (world : Fin (Fintype.card graph.FullConfig)) :
    (∏ factor, table graph world factor) =
      graph.unnormalizedJoint ((Fintype.equivFin graph.FullConfig).symm world) := by
  unfold table FactorGraph.unnormalizedJoint
  exact (Fintype.equivFin graph.factors).symm.prod_comp
    (fun factor => graph.potential factor (graph.restrictToScope factor
      ((Fintype.equivFin graph.FullConfig).symm world)))

/-- The actual reference evaluator recovers every native finite query mass. -/
theorem run_readout (query : graph.FullConfig → Bool) :
    (run (values (table graph)) (readout graph query)).value =
      ∑ world : graph.FullConfig, if query world then graph.unnormalizedJoint world else 0 := by
  rw [readout, complete_compile_value]
  simp only [row_product, Function.comp_def]
  exact (Fintype.equivFin graph.FullConfig).symm.sum_comp
    (fun world => if query world then graph.unnormalizedJoint world else 0)

/-- The true query computes the native partition function. -/
theorem run_partition :
    (run (values (table graph)) (readout graph (fun _ => true))).value = graph.partitionFunction := by
  rw [run_readout]
  simp only [↓reduceIte]
  unfold FactorGraph.partitionFunction
  rw [Fintype.piFinset_univ]
  rfl

end Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout

open scoped NNReal ENNReal
open Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts
open Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

variable {V Output : Type*} [Fintype V] [DecidableEq V]
  (graph : FactorGraph V ℝ≥0) [∀ v, Fintype (graph.stateSpace v)] [Fintype graph.factors]

local instance : Fintype graph.FullConfig := by
  unfold FactorGraph.FullConfig
  infer_instance

/-- Build the complete observed mass object from executed polynomial readouts. -/
noncomputable def compiledMass (observe : graph.FullConfig → Output) :
    MassSemantics (Output → Bool) where
  queryMass query := ((run (values (table graph)) (readout graph (query ∘ observe))).value : ℝ≥0∞)
  totalMass := ((run (values (table graph)) (readout graph (fun _ => true))).value : ℝ≥0∞)
  queryMass_le_total query := by
    rw [run_readout, run_readout]
    simp only [↓reduceIte]
    exact_mod_cast (Finset.sum_le_sum (s := Finset.univ) fun world _ =>
      show (if query (observe world) then graph.unnormalizedJoint world else 0) ≤
        graph.unnormalizedJoint world by split_ifs <;> simp)
  totalMass_ne_top := ENNReal.coe_ne_top

/-- Execution preserves all observed query masses and the total mass before normalization. -/
theorem compiled_mass_eq_observation (observe : graph.FullConfig → Output) :
    compiledMass graph observe = observationMass graph.unnormalizedJoint observe := by
  apply MassSemantics.ext
  · funext query
    change ((run (values (table graph)) (readout graph (query ∘ observe))).value : ℝ≥0∞) = _
    rw [run_readout]
    rfl
  · change ((run (values (table graph)) (readout graph (fun _ => true))).value : ℝ≥0∞) = _
    rw [run_readout]
    simp [observationMass]

end Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout
