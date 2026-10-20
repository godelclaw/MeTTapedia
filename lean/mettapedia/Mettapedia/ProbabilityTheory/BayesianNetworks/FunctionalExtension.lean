import Mettapedia.ProbabilityTheory.FiniteFunctionalExtension
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph

/-!
# A factor graph for a deterministic world extension

Two variables represent the source choice and the derived observation. One
factor carries the source weight; a second enforces the functional relation.
Their product is proved equal to the independently defined extended table.
The configuration equivalence then identifies the graph's complete query and
partition masses with the source observation semantics.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension

open scoped NNReal BigOperators
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

universe u
variable {Source Output : Type u} [Fintype Source] [Fintype Output] [DecidableEq Output]

/-- The two variable carriers: source choice and derived output. -/
abbrev stateSpace : Bool → Type u
  | false => Source
  | true => Output

noncomputable def graph (realize : Source → Output) (weight : Source → ℝ≥0) :
    FactorGraph Bool ℝ≥0 where
  stateSpace := stateSpace (Source := Source) (Output := Output)
  factors := Bool
  scope factor := if factor then Finset.univ else {false}
  potential
    | false, config => weight (config false (by simp))
    | true, config => if config true (by simp) = realize (config false (by simp)) then 1 else 0

instance factorFintype (realize : Source → Output) (weight : Source → ℝ≥0) :
    Fintype (graph realize weight).factors := inferInstanceAs (Fintype Bool)

instance stateFintype (realize : Source → Output) (weight : Source → ℝ≥0) (flag : Bool) :
    Fintype ((graph realize weight).stateSpace flag) := by
  cases flag <;> dsimp [graph, stateSpace] <;> infer_instance

/-- Every full graph configuration corresponds to exactly one source-output
pair. Both directions are supplied independently. -/
def configurationEquiv (realize : Source → Output) (weight : Source → ℝ≥0) :
    Source × Output ≃ (graph realize weight).FullConfig where
  toFun world
    | false => world.1
    | true => world.2
  invFun config := (config false, config true)
  left_inv _ := rfl
  right_inv config := by funext flag; cases flag <;> rfl

omit [Fintype Source] [Fintype Output] in
theorem graph_joint_eq_extension (realize : Source → Output) (weight : Source → ℝ≥0)
    (world : Source × Output) :
    (graph realize weight).unnormalizedJoint (configurationEquiv realize weight world) =
      extend realize weight world := by
  unfold FactorGraph.unnormalizedJoint
  change (∏ factor : Bool, (graph realize weight).potential factor
    ((graph realize weight).restrictToScope factor (configurationEquiv realize weight world))) = _
  rw [Fintype.prod_bool]
  change (if world.2 = realize world.1 then (1 : ℝ≥0) else 0) * weight world.1 = _
  rw [extend_as_factor, mul_comm]

/-- The existing factor-graph partition operation sums to the source mass. -/
theorem graph_partition_eq_source (realize : Source → Output) (weight : Source → ℝ≥0) :
    (graph realize weight).partitionFunction = ∑ world, weight world := by
  classical
  let : Fintype (graph realize weight).FullConfig := by
    unfold FactorGraph.FullConfig
    infer_instance
  unfold FactorGraph.partitionFunction
  rw [Fintype.piFinset_univ]
  change (∑ config : (graph realize weight).FullConfig,
    (graph realize weight).unnormalizedJoint config) = _
  rw [← (configurationEquiv realize weight).sum_comp]
  simp only [graph_joint_eq_extension]
  rw [Fintype.sum_prod_type]
  simp [extend]

/-- Observe the graph by summing over all its full configurations. -/
noncomputable def massSemantics (realize : Source → Output) (weight : Source → ℝ≥0) :
    MassSemantics (Output → Bool) := by
  classical
  letI : Fintype (graph realize weight).FullConfig := by
    unfold FactorGraph.FullConfig
    infer_instance
  exact observationMass (graph realize weight).unnormalizedJoint (fun config => config true)

/-- The graph realizes source observation semantics before normalization.
There is no extra probability mass from the auxiliary variable. -/
theorem graph_mass_eq_source (realize : Source → Output) (weight : Source → ℝ≥0) :
    massSemantics realize weight = observationMass weight realize := by
  classical
  let : Fintype (graph realize weight).FullConfig := by
    unfold FactorGraph.FullConfig
    infer_instance
  have reindex := observationMass_equiv (configurationEquiv realize weight)
    (graph realize weight).unnormalizedJoint (fun config => config true)
  have table : (graph realize weight).unnormalizedJoint ∘ configurationEquiv realize weight =
      extend realize weight := funext (graph_joint_eq_extension realize weight)
  rw [table] at reindex
  change observationMass (extend realize weight) Prod.snd = massSemantics realize weight at reindex
  rw [← reindex, extended_mass_eq]

end Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension
