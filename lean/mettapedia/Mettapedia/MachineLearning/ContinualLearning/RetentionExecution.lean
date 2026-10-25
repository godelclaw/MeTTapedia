import Mettapedia.MachineLearning.ContinualLearning.OrthogonalGradientRetention
import Mettapedia.GSLT.Dynamics.OrderedListFold

/-!
# Ordered execution and retention observations

The ordered-fold GSLT consumes every update occurrence. Its complete paths
realize additive accumulation, including the finalization transition. Additive
observations interpret the result; they need not distinguish the intermediate
states or histories. These are exact algebraic semantics, independent of a
numerical representation or a native training implementation.
-/

namespace Mettapedia.MachineLearning.ContinualLearning.RetentionExecution

open Mettapedia.GSLT.Dynamics

variable {Parameter Observation : Type} [AddMonoid Parameter] [AddMonoid Observation]

/-- Sequential additive evaluation agrees with the independent sum interpretation. -/
theorem fold_add (updates : List Parameter) (initial : Parameter) :
    updates.foldl (· + ·) initial = accumulatedParameter initial updates := by
  simpa only [accumulatedParameter, totalUpdate, List.sum_eq_foldl, add_zero] using
    (List.foldl_assoc (op := fun x y : Parameter => x + y)
      (l := updates) (a₁ := initial) (a₂ := 0))

/-- A concrete path consumes the supplied occurrences in order. -/
def runPath (updates : List Parameter) (initial : Parameter) :
    (OrderedListFold.theory (· + ·)).RewritePath (.active updates initial)
      (.done (accumulatedParameter initial updates)) :=
  (fold_add updates initial) ▸ OrderedListFold.runPath (· + ·) updates initial

/-- Every supplied complete execution has the declared result and step count. -/
theorem complete_path (updates : List Parameter) (initial result : Parameter)
    (path : (OrderedListFold.theory (· + ·)).RewritePath
      (.active updates initial) (.done result)) :
    result = accumulatedParameter initial updates ∧ path.length = updates.length + 1 := by
  simpa only [fold_add] using OrderedListFold.complete_path (· + ·) updates initial result path

/-- Observation commutes with execution while the path retains its ordered steps. -/
theorem complete_observation (observe : Parameter →+ Observation)
    (updates : List Parameter) (initial result : Parameter)
    (path : (OrderedListFold.theory (· + ·)).RewritePath
      (.active updates initial) (.done result)) :
    observe result = observe initial + (updates.map observe).sum := by
  rw [(complete_path updates initial result path).1, observe_accumulatedParameter]

/-- The sharper Jacobian-drift bound applies to any complete operational path. -/
theorem complete_readout_bound {Parameter : Type} [NormedAddCommGroup Parameter]
    [InnerProductSpace ℝ Parameter] (base : ℝ) (stored actual initial result : Parameter)
    (updates : List Parameter) (orthogonal : ∀ update ∈ updates, inner ℝ stored update = 0)
    (path : (OrderedListFold.theory (· + ·)).RewritePath
      (.active updates initial) (.done result)) :
    |linearizedReadout base actual initial result - base| ≤
      ‖actual - stored‖ * ‖totalUpdate updates‖ := by
  rw [(complete_path updates initial result path).1]
  exact linearizedReadout_forgetting_le_jacobianDrift_mul_totalUpdate _ _ _ _ _ orthogonal

/-- Equal final parameters conceal different intermediate observations. -/
theorem equal_endpoints_different_prefixes :
    accumulatedParameter (0 : ℤ) [1, -1] = accumulatedParameter 0 [-1, 1] ∧
      accumulatedParameter (0 : ℤ) [1] ≠ accumulatedParameter 0 [-1] := by decide

/-- Reordering state-dependent affine updates can change even the endpoint. -/
theorem stateDependent_updates_need_order :
    ([(2, 0), (1, 1)] : List (ℤ × ℤ)).foldl (fun x update => update.1 * x + update.2) 0 ≠
      ([(1, 1), (2, 0)] : List (ℤ × ℤ)).foldl (fun x update => update.1 * x + update.2) 0 := by
  decide

end Mettapedia.MachineLearning.ContinualLearning.RetentionExecution
