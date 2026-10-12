import Mettapedia.GSLT.Causality.DoCalculus.BowBound
import Mettapedia.GSLT.Causality.DoCalculus.DoorMargin
import Mettapedia.GSLT.Causality.DoCalculus.ExchangeDelete
import Mettapedia.GSLT.Causality.DoCalculus.RuleControls
import Mettapedia.GSLT.Causality.DoCalculus.WeightReading
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.CoordinateCrossing

/-!
# When a crossing publication is sound

`crossingPolicy` gates on `identificationDischarged` and then pools the raw
observation. `front_door_admitted` states that gate. The count is wrong at the
front door: the checker returns true, the raw observational strength is `3/4`,
and the identified expression is `3/5`.

A crossing publication is a function of the observational table. It is sound
for a family of models when the count it publishes into the interventional
coordinate has the strength of the interventional query in every model with
that table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Logic.EvidenceStateInsufficiency

/-- An observational table together with the strength of one query. -/
structure CausalModel where
  table : Counts
  query : ℚ

/-- **Positive model.** The front-door table, with the identified strength. -/
def frontDoorModel : CausalModel where
  table := smokeObsCounts
  query := 3 / 5

/-- **Negative pair.** One bow table, two interventional strengths. -/
def bowHighModel : CausalModel where
  table := bowObsCounts
  query := bowModel1Counts.strength

/-- **Negative pair.** The same bow table, the other interventional strength. -/
def bowLowModel : CausalModel where
  table := bowObsCounts
  query := bowModel2Counts.strength

theorem bow_models_one_table :
    bowHighModel.table = bowLowModel.table ∧ bowHighModel.query ≠ bowLowModel.query := by
  refine ⟨rfl, ?_⟩
  rw [bowHighModel, bowLowModel, bow_model_strengths.1, bow_model_strengths.2]
  norm_num

/-- The count `publish` writes into the interventional coordinate, a function of
the observational table, has the query strength in every model of the family. -/
def SoundCrossing (models : List CausalModel) (publish : Counts → Counts) : Prop :=
  ∀ model ∈ models, (publish model.table).strength = model.query

/-- Publish one count that was simulated under an intervention. -/
def publishSimulated (simulated : Counts) : Counts → Counts :=
  fun _ => simulated

/-- Write that count into the interventional coordinate. The observational
coordinate stays the table the count was read from. -/
def installPublished (publish : Counts → Counts) (table : Counts) : QueryState where
  observational := table
  interventional := publish table

/-- **Positive.** The identified count, installed, has strength `3/5`. Pooling
one raw observation revises a coordinate and is not that installation:
`poolObservational` revises the table, and `poolInterventional` revises the
identified count. -/
theorem identified_install_is_not_a_raw_pool (experiment : Bool) :
    (installPublished (fun _ => frontDoorCounts) smokeObsCounts).interventional.strength =
        3 / 5 ∧
      (installPublished (fun _ => frontDoorCounts) smokeObsCounts).observational =
        smokeObsCounts ∧
      (poolObservational frontDoorState experiment).observational =
        smokeObsCounts.revise experiment ∧
      (poolObservational frontDoorState experiment).interventional =
        frontDoorState.interventional ∧
      (poolInterventional frontDoorState experiment).interventional =
        frontDoorCounts.revise experiment ∧
      frontDoorCounts.revise experiment ≠ frontDoorCounts := by
  refine ⟨front_door_count_strength, rfl,
    (pool_observational_keeps_interventional frontDoorState experiment).2.trans ?obs,
    (pool_observational_keeps_interventional frontDoorState experiment).1,
    (pool_interventional_keeps_observational frontDoorState experiment).2.trans ?inter,
    ?revised⟩
  · simp [frontDoorState]
  · simp [frontDoorState]
  · rw [frontDoorCounts_canonical]
    cases experiment <;> decide

/-- **Negative.** Installing the raw observational table publishes strength
`3/4`, which is not the identified strength. -/
theorem raw_install_misses_front_door :
    (installPublished (fun table => table) smokeObsCounts).interventional.strength = 3 / 4 ∧
      (installPublished (fun table => table) smokeObsCounts).interventional.strength ≠
        (installPublished (fun _ => frontDoorCounts) smokeObsCounts).interventional.strength := by
  refine ⟨smoke_obs_count_strength, ?_⟩
  unfold installPublished
  exact front_door_count_differs_from_observation.symm

/-- **Positive.** At the front door, publishing the count read off the identified
expression is sound. The do-mass is that strength, by
`front_door_weight_count_licence`, and `identify` returns the expression, by
`front_door_identify_count_licence`. -/
theorem front_door_identified_policy_sound (experiment : Bool) :
    SoundCrossing [frontDoorModel] (fun _ => frontDoorCounts) ∧
      frontDoorOf true true smokeProbJoint =
        ENNReal.ofReal (frontDoorCounts.strength : ℝ) ∧
      Factors (fun cpt : FrontPositive true => cpt.1.jointWeight)
        (fun cpt => doMass cpt.1 true true) := by
  refine ⟨?_, (front_door_weight_count_licence experiment).2.1,
    front_door_identified true true⟩
  intro model member
  obtain rfl := List.mem_singleton.mp member
  exact (front_door_identify_count_licence experiment).2.1

/-- **Positive.** At the back door, publishing the count read off the identified
expression is sound, from `back_door_identify_count_licence` and
`back_door_weight_count_licence`. -/
theorem back_door_identified_policy_sound (experiment : Bool) :
    SoundCrossing [⟨doorObsCounts, 1 / 2⟩] (fun _ => backDoorCounts) ∧
      backDoorFromMargin Door.x Door.y doorZ (doorAt false)
          (observedMargin (backDoorLatent Door.x Door.y doorZ) doorProbJoint) =
        ENNReal.ofReal (backDoorCounts.strength : ℝ) := by
  refine ⟨?_, (back_door_weight_count_licence experiment).2.1⟩
  intro model member
  obtain rfl := List.mem_singleton.mp member
  exact (back_door_identify_count_licence experiment).2.1

/-- **Negative.** `crossingPolicy` is not sound at the front door. The checker
returns true and the policy returns the raw observation, but the observational
strength is not the identified strength. -/
theorem crossingPolicy_front_not_sound (experiment : Bool) :
    identificationDischarged smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS
        (∅ : Finset Smoke) = true ∧
      (crossingPolicy smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke)
          .observational .interventional).returned
        ((pureObservation experiment).branchLocal emptyFlag) = [experiment] ∧
      ¬ SoundCrossing [frontDoorModel] (fun table => table) := by
  refine ⟨(front_door_admitted experiment).1, crossingPolicy_returns experiment, ?_⟩
  intro sound
  have published := sound frontDoorModel (List.mem_singleton.mpr rfl)
  exact front_door_count_differs_from_observation
    (published.trans (front_door_identify_count_licence experiment).2.1.symm).symm

/-- **Negative.** At the bow no publication is sound: the two models share a
table and `bow_observational_pool_misses_a_model` separates their do-masses. -/
theorem bow_no_policy_sound (publish : Counts → Counts) :
    ¬ SoundCrossing [bowHighModel, bowLowModel] publish := by
  intro sound
  have miss := bow_observational_pool_misses_a_model publish
  have high := sound bowHighModel (List.mem_cons.mpr (Or.inl rfl))
  have low := sound bowLowModel
    (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  have same : bowModel1Counts.strength = bowModel2Counts.strength := by
    have highStrength : (publish bowObsCounts).strength = bowModel1Counts.strength := by
      simpa [bowHighModel] using high
    have lowStrength : (publish bowObsCounts).strength = bowModel2Counts.strength := by
      simpa [bowLowModel] using low
    exact highStrength.symm.trans lowStrength
  have doSame : bowDoMass bowCPT1 true = bowDoMass bowCPT2 true := by
    rw [← miss.2.2.2.2.1, ← miss.2.2.2.2.2.1]
    exact congrArg (fun query : ℚ => ENNReal.ofReal (query : ℝ)) same
  rw [bow_do_model1, bow_do_model2] at doSame
  exact one_ne_inv_two doSame

/-- **Positive, no confounder.** On the copy graph `Z → Y`, `rule2_of_parents`
equates the interventional ratio with the observational ratio, and publishing
the raw table is sound: both strengths are `1`. -/
theorem copy_rule2_raw_pooling_sound :
    SoundCrossing [⟨⟨1, 0⟩, 1⟩] (fun table => table) ∧
      truncSlice copyGraph copyAcyclic copyCPT
          (doFinset ((∅ : Finset Node) ∪ {Node.z})
            (mergeAssign (∅ : Finset Node) (fun _ => true) (fun _ => true)))
          ((∅ : Finset Node) ∪ {Node.y} ∪ {Node.z} ∪ ∅) (fun _ => true) /
        truncSlice copyGraph copyAcyclic copyCPT
          (doFinset ((∅ : Finset Node) ∪ {Node.z})
            (mergeAssign (∅ : Finset Node) (fun _ => true) (fun _ => true)))
          ((∅ : Finset Node) ∪ {Node.z} ∪ ∅) (fun _ => true) =
        truncSlice copyGraph copyAcyclic copyCPT
          (doFinset (∅ : Finset Node) (fun _ => true))
          ((∅ : Finset Node) ∪ {Node.y} ∪ {Node.z} ∪ ∅) (fun _ => true) /
        truncSlice copyGraph copyAcyclic copyCPT
          (doFinset (∅ : Finset Node) (fun _ => true))
          ((∅ : Finset Node) ∪ {Node.z} ∪ ∅) (fun _ => true) := by
  refine ⟨?sound, ?rule⟩
  · intro model member
    obtain rfl := List.mem_singleton.mp member
    norm_num [Counts.strength, Counts.total]
  · have hdisj : Disjoint (∅ : Finset Node) ({Node.z} : Finset Node) :=
      Finset.disjoint_empty_left _
    have hparents :
        ∀ v ∈ ({Node.z} : Finset Node), ∀ u, copyGraph.edges u v →
          u ∈ ((∅ : Finset Node) ∪ {Node.z} ∪ ∅) := by
      intro v hv u hedge
      have hu : u ∈ ({Node.z} : Finset Node) :=
        copy_rule2_conditional_eq.1 v hv u hedge
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hu)))
    have hz :
        ∀ v ∈ ({Node.z} : Finset Node),
          (fun _ : Node => true) v = (fun _ : Node => true) v :=
      fun _ _ => rfl
    have hkeep : ∀ f : Node → Bool,
        agreesOn ({Node.z} : Finset Node) (fun _ => true) f = f Node.z := by
      intro f
      rw [agreesOn]
      cases hfz : f Node.z
      · rw [decide_eq_false_iff_not]
        intro hall
        exact Bool.false_ne_true (hfz ▸ hall Node.z (Finset.mem_singleton_self _))
      · rw [decide_eq_true_iff]
        intro v hv
        have hvz : v = Node.z := Finset.mem_singleton.mp hv
        subst hvz
        exact hfz
    have hpos :
        truncSlice copyGraph copyAcyclic copyCPT
          (doFinset (∅ : Finset Node) (fun _ => true))
          ({Node.z} : Finset Node) (fun _ => true) ≠ 0 := by
      have hmass :
          truncSlice copyGraph copyAcyclic copyCPT
              (doFinset (∅ : Finset Node) (fun _ => true))
              ({Node.z} : Finset Node) (fun _ => true) =
            nodeMass copyGraph copyAcyclic copyCPT
              (doFinset (∅ : Finset Node) (fun _ => true))
              (fun f => agreesOn ({Node.z} : Finset Node) (fun _ => true) f) :=
        rfl
      have hnode :
          nodeMass copyGraph copyAcyclic copyCPT
              (doFinset (∅ : Finset Node) (fun _ => true))
              (fun f => agreesOn ({Node.z} : Finset Node) (fun _ => true) f) =
            nodeMass copyGraph copyAcyclic copyCPT doNone (fun f => f Node.z) := by
        rw [doNone_eq]
        simp only [nodeMass, hkeep]
      rw [hmass, hnode, copy_obs_mass_z]
      exact half_ne_zero
    exact rule2_of_parents (graph := copyGraph) (hAcyclic := copyAcyclic)
      (X := (∅ : Finset Node)) (Y := {Node.y}) (Z := {Node.z}) (W := (∅ : Finset Node))
      hdisj hparents copyCPT (fun _ => true) (fun _ => true) (fun _ => true) hz hpos

/-- **Positive, the other direction.** On the copy graph the interventional
conditional and the observational conditional are both `1`, so publishing the
simulated count into the observational coordinate reads that strength. -/
theorem copy_simulated_into_observation_sound :
    SoundCrossing [⟨⟨1, 0⟩, 1⟩] (publishSimulated ⟨1, 0⟩) ∧
      nodeMass copyGraph copyAcyclic copyCPT
          (doFinset ({Node.z} : Finset Node) (fun _ => true)) (fun f => f Node.y) /
        nodeMass copyGraph copyAcyclic copyCPT
          (doFinset ({Node.z} : Finset Node) (fun _ => true)) (fun _ => true) = 1 ∧
      nodeMass copyGraph copyAcyclic copyCPT
          (doFinset (∅ : Finset Node) (fun _ => true)) (fun f => f Node.y && f Node.z) /
        nodeMass copyGraph copyAcyclic copyCPT
          (doFinset (∅ : Finset Node) (fun _ => true)) (fun f => f Node.z) = 1 := by
  refine ⟨?sound, ?interventional, ?observational⟩
  · intro model member
    obtain rfl := List.mem_singleton.mp member
    simp [publishSimulated, Counts.strength, Counts.total]
  · rw [← doZTrue_eq, copy_doZ_mass_y, copy_doZ_mass_all, div_by_one]
  · have hinterventional :
        nodeMass copyGraph copyAcyclic copyCPT
            (doFinset ({Node.z} : Finset Node) (fun _ => true)) (fun f => f Node.y) /
          nodeMass copyGraph copyAcyclic copyCPT
            (doFinset ({Node.z} : Finset Node) (fun _ => true)) (fun _ => true) = 1 := by
      rw [← doZTrue_eq, copy_doZ_mass_y, copy_doZ_mass_all, div_by_one]
    exact (copy_rule2_conditional_eq).2.symm.trans hinterventional

/-- **Negative, the other direction.** Publishing the front-door interventional
count into the observational coordinate does not have the observational
strength. -/
theorem front_simulated_into_observation_unsound :
    ¬ SoundCrossing [⟨smokeObsCounts, smokeObsCounts.strength⟩]
        (publishSimulated frontDoorCounts) := by
  intro sound
  have published := sound ⟨smokeObsCounts, smokeObsCounts.strength⟩
    (List.mem_singleton.mpr rfl)
  exact front_door_count_differs_from_observation
    (by simpa [publishSimulated] using published)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
