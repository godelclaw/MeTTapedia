import Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

/-!
# Composing deterministic extensions under a declared observation view

A second component may read both the retained source and the first auxiliary
output. The corresponding revision maps compose and preserve the complete
final query-mass object. Prefix observations on the first output alone need
not determine a continuation that reads the source.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.FunctionalExtensionComposition

open scoped NNReal ENNReal BigOperators
open Mettapedia.Logic.WorldModel
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

variable {Source Aux Output : Type*} [Fintype Source] [Fintype Aux] [DecidableEq Aux]
  [Fintype Output] [DecidableEq Output]

theorem staged_mass_eq (first : Source → Aux) (second : Source × Aux → Output)
    (weight : Source → ℝ≥0) :
    observationMass (extend second (extend first weight)) Prod.snd =
      observationMass weight (fun source => second (source, first source)) := by
  rw [extension_observation_mass second (extend first weight) Prod.snd,
    extension_observation_mass first weight second]

noncomputable def sequentialInterpretation (first : Source → Aux) (second : Source × Aux → Output) :
    @RevisionMap (Source → ℝ≥0) (Output → Bool) (Option ℝ≥0∞)
      ((Source × Aux) × Output → ℝ≥0) (Output → Bool) (Option ℝ≥0∞)
      (tableModel (fun source => second (source, first source))).toWorldModel
      (tableModel (Source := (Source × Aux) × Output) Prod.snd).toWorldModel := by
  letI := tableModel (fun source => second (source, first source))
  letI := tableModel second
  letI := tableModel (Source := (Source × Aux) × Output) Prod.snd
  exact (interpretationWithView first second).comp (interpretation second)

/-- Fusing the deterministic functions preserves all final-view masses;
it does not assert preservation of every intermediate observer or cost. -/
theorem fused_mass_eq (first : Source → Aux) (second : Source × Aux → Output)
    (weight : Source → ℝ≥0) :
    observationMass (extend second (extend first weight)) Prod.snd =
      observationMass (extend (fun source => second (source, first source)) weight) Prod.snd := by
  rw [staged_mass_eq, extended_mass_eq]

/-- Chronological native table mixtures transport through the composed map. -/
theorem sequential_chronology (first : Source → Aux) (second : Source × Aux → Output)
    (updates : List (Source → ℝ≥0)) (initial : Source → ℝ≥0) :
    extend second (extend first (updates.foldl (· + ·) initial)) =
      (updates.map (fun weight => extend second (extend first weight))).foldl (· + ·)
        (extend second (extend first initial)) := by
  let := tableModel (fun source => second (source, first source))
  let := tableModel (Source := (Source × Aux) × Output) Prod.snd
  exact (sequentialInterpretation first second).foldl_revise updates initial

namespace Controls

private def leftWeight : Bool → ℝ≥0 := fun source => if source then 1 else 0
private def rightWeight : Bool → ℝ≥0 := fun source => if source then 0 else 1
private def first (_ : Bool) : Bool := false
private def second (world : Bool × Bool) : Bool := world.1

theorem prefix_observations_identical :
    observationMass (extend first leftWeight) Prod.snd =
      observationMass (extend first rightWeight) Prod.snd := by
  rw [extended_mass_eq, extended_mass_eq]
  apply MassSemantics.ext
  · funext query
    simp [observationMass, first, leftWeight, rightWeight]
  · simp [observationMass, leftWeight, rightWeight]

theorem continuation_observations_differ :
    (observationMass (extend second (extend first leftWeight)) Prod.snd).query id = some 1 ∧
      (observationMass (extend second (extend first rightWeight)) Prod.snd).query id = some 0 := by
  rw [staged_mass_eq, staged_mass_eq]
  simp only [observationMass, Fintype.sum_bool, second, leftWeight, rightWeight,
    Bool.false_eq_true, if_true, if_false]
  norm_num [MassSemantics.query, MassSemantics.queryProb]

end Controls

end Mettapedia.ProbabilityTheory.FunctionalExtensionComposition
