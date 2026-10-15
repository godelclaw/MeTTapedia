import Mettapedia.OSLF.NativeTypes.Generation.Schemas
import Mettapedia.OSLF.NativeTypes.Generation.Checking
import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierComparison
import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierControls

open Mettapedia.OSLF.Framework

/-!
# Reflective COMM in an unrestricted-context companion

The generator takes the actual scoped companion of the authored rho language.
Its selected operational profile retains original COMM, reflective substitution
and typed contextual descent at every constructor and binder position, with
literal repeated-channel matching. This is an operational extension of rho's
parallel-only reduction contexts. Equation closure is not silently added to
that profile. Both arbitrary sorted input terms and concrete communications
use the same generated plan and native frontier. The separate authored-context
consumer compiles the parallel permissions from rho's congruence declarations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)

def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {operational := GeneralRho.permissions}

def chosen := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot GeneralRho.snapshot fragment

theorem chosen_snapshot : chosen = GeneralRho.snapshot := by
  change ({GeneralRho.snapshot with language :=
    Mettapedia.OSLF.NativeTypes.Generation.selectedLanguage GeneralRho.language ⟨none, GeneralRho.permissions⟩} : Snapshot) = _
  rw [Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]
  rfl

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated := Mettapedia.OSLF.NativeTypes.Generation.generate GeneralRho.snapshot fragment
  Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem actual_plan : generated.plan = GeneralRho.plan := by
  change compile chosen GeneralRho.permissions = GeneralRho.plan
  rw [chosen_snapshot]
  rfl

theorem actual_request (bound : List TypeExpr) (pattern : Pattern) :
    generated.request bound (.base "Proc") pattern = GeneralRho.frontierRequest bound pattern := by
  change GeneralOccurrenceFrontier.Request.fromSnapshot chosen _ _ _ _ = _
  rw [chosen_snapshot]
  rfl

theorem actual_execution (bound : List TypeExpr) (pattern : Pattern) (budget : Nat) :
    HEq (generated.execute bound (.base "Proc") pattern budget)
      (GeneralOccurrenceFrontier.run (GeneralRho.frontierRequest bound pattern) budget
        (GeneralOccurrenceFrontier.start (GeneralRho.frontierRequest bound pattern))) := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.execute
  change GeneralOccurrenceFrontier.run
    (.fromSnapshot chosen GeneralRho.permissions bound (.base "Proc") pattern) budget
    (GeneralOccurrenceFrontier.start
      (.fromSnapshot chosen GeneralRho.permissions bound (.base "Proc") pattern)) ≍ _
  rw [chosen_snapshot]
  rfl

/-- For every sorted scoped source, the generated execution has an actual
finite completed run whose independently checked coverage certificate holds. -/
theorem every_sorted_source_has_certified_execution {bound : List TypeExpr} {pattern : Pattern}
    (typed : OpenPatternWellSorted GeneralRho.language GeneralRho.snapshot.free
      bound (.base "Proc") pattern) :
    ∃ budget, GeneralOccurrenceFrontier.checkCertificate
      (generated.request bound (.base "Proc") pattern)
      (generated.execute bound (.base "Proc") pattern budget) = true := by
  obtain ⟨budget, actual⟩ := GeneralOccurrenceFrontier.finish_actual_run
    (GeneralRho.frontierRequest bound pattern) (GeneralRho.source_frontier_admitted typed)
  refine ⟨budget, ?_⟩
  have certified := GeneralRho.source_frontier_certificate typed
  rw [← actual] at certified
  change GeneralOccurrenceFrontier.checkCertificate
    (.fromSnapshot chosen GeneralRho.permissions bound (.base "Proc") pattern)
    (GeneralOccurrenceFrontier.run
      (.fromSnapshot chosen GeneralRho.permissions bound (.base "Proc") pattern) budget
      (GeneralOccurrenceFrontier.start
        (.fromSnapshot chosen GeneralRho.permissions bound (.base "Proc") pattern))) = true
  rw [chosen_snapshot]
  exact certified

/-- Every generated position is licensed by independent typing descent. -/
theorem generated_schemas_are_licensed {schema : Schema generated.plan}
    (member : schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas generated.plan) :
    schema.bound = [] ∧
      schema.programCarrier ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates generated.plan.snapshot.language
        schema.declaration.rule ∧
      ∃ site, Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Licensed
        generated.plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree schema.declaration.rule)
        .all [] schema.programCarrier schema.declaration.rule.left site ∧
        schema.position = site.address ∧ schema.focusBound = site.focusBound ∧
        schema.focusCarrier = site.focusType :=
  Mettapedia.OSLF.NativeTypes.Generation.schemas_sound member

def rootExecution := generated.execute [] (.base "Proc") GeneralRho.FrontierControls.rootSource 40

theorem communication_readout :
    GeneralRho.FrontierControls.readouts
      (generated.request [] (.base "Proc") GeneralRho.FrontierControls.rootSource) 40 =
        [⟨0, [], [], GeneralRho.commTrace, some GeneralRho.FrontierControls.receivedBody,
          GeneralRho.FrontierControls.rootTarget⟩] := by
  rw [actual_request]
  exact GeneralRho.FrontierControls.actual_received_drop

theorem communication_emits_one_native_receipt : rootExecution.answers.length = 1 := by
  have count := congrArg List.length communication_readout
  simpa only [GeneralRho.FrontierControls.readouts, List.length_map, List.length_singleton,
    rootExecution, Mettapedia.OSLF.NativeTypes.Generation.Generated.execute] using count

theorem communication_under_input_binder :
    GeneralRho.FrontierControls.readouts
      (generated.request [] (.base "Proc") GeneralRho.FrontierControls.inputSource) 60 =
        [⟨0, [1, 0], [.base "Name"], GeneralRho.commTrace,
          some GeneralRho.FrontierControls.outerBody, GeneralRho.FrontierControls.inputTarget⟩] := by
  rw [actual_request]
  exact GeneralRho.FrontierControls.actual_input_context_and_outer_name

theorem equal_targets_retain_two_origins :
    GeneralRho.FrontierControls.readouts
      (generated.request [] (.base "Proc") GeneralRho.FrontierControls.duplicates) 75 =
        [⟨0, [], [], GeneralRho.firstInputTrace, some GeneralRho.FrontierControls.receivedBody,
            GeneralRho.FrontierControls.duplicateTarget⟩,
         ⟨0, [], [], GeneralRho.secondInputTrace, some GeneralRho.FrontierControls.receivedBody,
            GeneralRho.FrontierControls.duplicateTarget⟩] := by
  rw [actual_request]
  exact GeneralRho.FrontierControls.actual_duplicate_bag_origins

end Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl
