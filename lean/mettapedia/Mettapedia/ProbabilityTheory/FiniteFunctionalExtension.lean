import Mettapedia.ProbabilityTheory.MassSemantics
import Mettapedia.Logic.WorldModel.Observation
import Mathlib.Data.Fintype.Prod

/-!
# Finite deterministic extensions preserve query mass

An auxiliary value is fixed by a function of the source world. Extending a
world-weight table puts its weight on exactly that auxiliary value. Query
masses and total mass are preserved, and projecting the extended table recovers
the original table. Unconstrained auxiliary choices can duplicate source mass.

These are mixture-update world models. Mixture of weight tables is distinct
from multiplying factors or unioning logic programs. Normalization remains an
optional observation, with no answer when the total mass is zero.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

open scoped NNReal ENNReal BigOperators
open Mettapedia.Logic.WorldModel

variable {Source Output : Type*} [Fintype Source] [Fintype Output] [DecidableEq Output]

/-- Observe a finite table through a deterministic world interpretation. -/
noncomputable def observationMass (weight : Source → ℝ≥0) (realize : Source → Output) :
    MassSemantics (Output → Bool) where
  queryMass query := ((∑ world, if query (realize world) then weight world else 0 : ℝ≥0) : ℝ≥0∞)
  totalMass := ((∑ world, weight world : ℝ≥0) : ℝ≥0∞)
  queryMass_le_total query := by
    exact_mod_cast (Finset.sum_le_sum (s := Finset.univ) fun world _ =>
      show (if query (realize world) then weight world else 0) ≤ weight world by
        split_ifs <;> simp)
  totalMass_ne_top := ENNReal.coe_ne_top

omit [DecidableEq Output] in
/-- Native table addition is mixture revision, including empty tables. -/
@[instance_reducible] noncomputable def tableModel (realize : Source → Output) :
    MonoidalWorldModel (Source → ℝ≥0) (Output → Bool) (Option ℝ≥0∞) where
  revise := (· + ·)
  empty := 0
  extract weight query := (observationMass weight realize).query query
  revise_assoc := add_assoc
  revise_empty_left := zero_add
  revise_empty_right := add_zero

omit [Fintype Output] [DecidableEq Output] in
/-- Reindexing a finite world table along an equivalence preserves its full
mass semantics, not only its normalized query values. -/
theorem observationMass_equiv {Other : Type*} [Fintype Other]
    (equiv : Source ≃ Other) (weight : Other → ℝ≥0) (realize : Other → Output) :
    observationMass (weight ∘ equiv) (realize ∘ equiv) = observationMass weight realize := by
  apply MassSemantics.ext
  · funext query
    apply congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞))
    exact equiv.sum_comp (fun world => if query (realize world) then weight world else 0)
  · apply congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞))
    exact equiv.sum_comp weight

/-- One permitted auxiliary extension for each source world. -/
def extend (realize : Source → Output) (weight : Source → ℝ≥0) : Source × Output → ℝ≥0 :=
  fun world => if world.2 = realize world.1 then weight world.1 else 0

omit [Fintype Source] [Fintype Output] in
theorem extend_as_factor (realize : Source → Output) (weight : Source → ℝ≥0)
    (world : Source × Output) :
    extend realize weight world = weight world.1 * if world.2 = realize world.1 then 1 else 0 := by
  by_cases same : world.2 = realize world.1 <;> simp [extend, same]

/-- Summing out the auxiliary coordinate. -/
noncomputable def marginalize (weight : Source × Output → ℝ≥0) : Source → ℝ≥0 :=
  fun world => ∑ auxiliary, weight (world, auxiliary)

omit [Fintype Source] in
theorem marginalize_extend (realize : Source → Output) (weight : Source → ℝ≥0) :
    marginalize (extend realize weight) = weight := by
  funext world
  simp [marginalize, extend]

/-- A deterministic extension preserves every query on a declared view of
both the source and auxiliary coordinates, before normalization. -/
theorem extension_observation_mass {View : Type*} (realize : Source → Output) (weight : Source → ℝ≥0)
    (observe : Source × Output → View) :
    observationMass (extend realize weight) observe =
      observationMass weight (fun source => observe (source, realize source)) := by
  apply MassSemantics.ext
  · funext query
    apply congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞))
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.sum_eq_single (realize source)]
    · simp [extend]
    · intro auxiliary _ different
      simp [extend, different]
    · intro missing
      exact (missing (Finset.mem_univ _)).elim
  · apply congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞))
    rw [Fintype.sum_prod_type]
    simp [extend]

/-- The auxiliary-output view is a specialization of the complete view law. -/
theorem extended_mass_eq (realize : Source → Output) (weight : Source → ℝ≥0) :
    observationMass (extend realize weight) Prod.snd = observationMass weight realize :=
  extension_observation_mass realize weight Prod.snd

/-- The view is part of the interpretation contract. A later component may
observe retained source data as well as the auxiliary output. -/
noncomputable def interpretationWithView {View : Type*} (realize : Source → Output) (observe : Source × Output → View) :
    @RevisionMap (Source → ℝ≥0) (View → Bool) (Option ℝ≥0∞)
      (Source × Output → ℝ≥0) (View → Bool) (Option ℝ≥0∞)
      (tableModel (fun source => observe (source, realize source))).toWorldModel
      (tableModel observe).toWorldModel := by
  letI := tableModel (fun source => observe (source, realize source))
  letI := tableModel observe
  exact {
    state := extend realize
    query := id
    value := id
    observe weight query := by
      change (observationMass (extend realize weight) observe).query query =
        (observationMass weight (fun source => observe (source, realize source))).query query
      rw [extension_observation_mass]
    empty := by
      funext world
      change extend realize (0 : Source → ℝ≥0) world = 0
      simp [extend]
    revise := by
      intro first second
      funext world
      change extend realize (first + second) world =
        extend realize first world + extend realize second world
      by_cases same : world.2 = realize world.1 <;> simp [extend, same] }

/-- Auxiliary-output interpretation with exact mixture revision. -/
noncomputable def interpretation (realize : Source → Output) :
    @RevisionMap (Source → ℝ≥0) (Output → Bool) (Option ℝ≥0∞)
      (Source × Output → ℝ≥0) (Output → Bool) (Option ℝ≥0∞)
      (tableModel realize).toWorldModel (tableModel (Source := Source × Output) Prod.snd).toWorldModel :=
  interpretationWithView realize Prod.snd

namespace Controls

noncomputable def asymmetric : Bool → ℝ≥0 := fun world => if world then 3/4 else 1/4

theorem nonconstant_extension_query :
    (observationMass (extend Bool.not asymmetric) Prod.snd).query id = some (1/4 : ℝ≥0∞) := by
  rw [extended_mass_eq]
  simp only [observationMass, Fintype.sum_bool, asymmetric, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false, if_true]
  norm_num [MassSemantics.query, MassSemantics.queryProb]

/-- An unconstrained Boolean auxiliary introduces an extra world and changes
the query answer. Keeping total mass prevents normalization from hiding it. -/
theorem unconstrained_auxiliary_changes_meaning :
    (observationMass (fun _ : Unit × Bool => (1 : ℝ≥0)) Prod.snd).totalMass = 2 ∧
      (observationMass (fun _ : Unit × Bool => (1 : ℝ≥0)) Prod.snd).query id = some (1/2 : ℝ≥0∞) ∧
      (observationMass (extend (fun _ : Unit => false) (fun _ => 1)) Prod.snd).query id =
        some (0 : ℝ≥0∞) := by
  rw [extended_mass_eq]
  simp only [observationMass, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
  norm_num [MassSemantics.query, MassSemantics.queryProb]

end Controls

end Mettapedia.ProbabilityTheory.FiniteFunctionalExtension
