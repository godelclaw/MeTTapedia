import Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Profile
import Mettapedia.OSLF.NativeTypes.Runtime.Search
import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Meaning

/-!
# Authored conditional equations in a normalized native backend

The language, conditional equation and both declaration origins are the
existing authored completion control. The normalizer collapses exactly the
enabled equation; no declared equation is discarded by the runtime adapter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized.AuthoredControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling
open GeneralCompletedFrontierControls

def plan : Plan := (request true).plan

def Source (source : Pattern) : Prop :=
  OpenPatternWellSorted plan.snapshot.language
    (snapshot true).free [] term source

theorem source_cases_of_typed (actual : LanguageDef) (grammar : actual.terms = language.terms)
    {source : Pattern} (typed : HasType actual
      (snapshot true).free [] source term) (object : isObjectPattern source = true) :
    source = one ∨ source = two ∨ source = done := by
  generalize expectedEq : term = expected at typed
  cases typed with
  | bvar selected => simp at selected
  | fvar selected => simp [snapshot, Snapshot.free] at selected
  | @constructor _ rule arguments member _ argumentsTyped =>
    rw [grammar] at member
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same <;> subst rule <;>
      cases argumentsTyped <;> simp [one, two, done]
  | subst _ _ => simp [isObjectPattern] at object
  | lambda => cases expectedEq
  | multiLambda => cases expectedEq
  | collection => cases expectedEq
  | @collectionConstructor _ rule _ _ _ _ _ member shape _ =>
    rw [grammar] at member
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same <;> subst rule <;> cases shape

theorem source_cases {source : Pattern} (typed : Source source) :
    source = one ∨ source = two ∨ source = done :=
  source_cases_of_typed _ rfl typed.1 typed.2.2.1

theorem literal_source (source : Pattern)
    (chosen : source = one ∨ source = two ∨ source = done) : Source source := by
  apply checkOpenPatternWellSorted_sound
  rcases chosen with rfl | rfl | rfl <;>
    change checkOpenPatternWellSorted (snapshot true).language _ _ _ _ = true
  all_goals cbv

theorem licensed_root {source : Pattern} {site : SiteData}
    (licensed : Licensed (GeneralPlanEnvironment.environment plan).language
      (snapshot true).free permissions.sites [] term source site) :
    site = SiteData.here [] term source := by
  have generated := GeneralTypedSites.generate_complete licensed
  have actual : GeneralTypedSites.generate (GeneralPlanEnvironment.environment plan).language
      (snapshot true).free permissions.sites [] term source = [SiteData.here [] term source] := by
    rcases source_cases_of_typed (GeneralPlanEnvironment.environment plan).language rfl licensed.source_typed licensed.source_object with rfl | rfl | rfl <;>
      change GeneralTypedSites.generate (GeneralPlanEnvironment.environment
        (compile (snapshot true) permissions)).language _ _ _ _ _ = _
    all_goals rw [runtime_plan_actual]; cbv
  rw [actual] at generated
  exact List.mem_singleton.mp generated

theorem equation_edge_shape {source target : Pattern}
    (edge : GeneralOccurrenceSemantics.Equation plan [] term source target) :
    (source = one ∧ target = two) ∨ (source = two ∧ target = one) := by
  obtain ⟨receipt, valid, endpoint⟩ := edge
  have site := licensed_root valid.job.2
  have member := List.fst_mem_of_mem_zipIdx valid.job.1
  change receipt.job.equation ∈ (compile (snapshot true) permissions).equations at member
  rw [runtime_plan_actual] at member
  change receipt.job.equation ∈ [oriented .forward, oriented .reverse] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have found := valid.matched.matching.complete
  have reduced := valid.reduct
  have result := valid.endpoint
  rw [site] at found reduced result
  rcases member with direction | direction
  · rw [direction] at found reduced
    have reduct : receipt.rawReduct = two := by
      have computed : ScopedRuleMatching.reduct? (oriented .forward).rule
          (oriented .forward).binding.spec 0 receipt.completed = some two := by cbv
      exact (Option.some.inj (computed.symm.trans reduced)).symm
    have targetIs : target = two := by
      rw [← endpoint, result, reduct]
      cbv
    rcases source_cases_of_typed (GeneralPlanEnvironment.environment plan).language rfl valid.sourceTyped.1 valid.sourceTyped.2.2.1 with same | same | same
    · exact .inl ⟨same, targetIs⟩
    · rw [same] at found
      have empty : ScopedRuleMatching.matchAt (oriented .forward).rule
          (oriented .forward).binding.spec 0 .left [] 0 []
          (oriented .forward).rule.left two.eraseBinderMetadata = [] := by cbv
      simp only [SiteData.here, List.length_nil] at found
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)
    · rw [same] at found
      have empty : ScopedRuleMatching.matchAt (oriented .forward).rule
          (oriented .forward).binding.spec 0 .left [] 0 []
          (oriented .forward).rule.left done.eraseBinderMetadata = [] := by cbv
      simp only [SiteData.here, List.length_nil] at found
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)
  · rw [direction] at found reduced
    have reduct : receipt.rawReduct = one := by
      have computed : ScopedRuleMatching.reduct? (oriented .reverse).rule
          (oriented .reverse).binding.spec 0 receipt.completed = some one := by cbv
      exact (Option.some.inj (computed.symm.trans reduced)).symm
    have targetIs : target = one := by
      rw [← endpoint, result, reduct]
      cbv
    rcases source_cases_of_typed (GeneralPlanEnvironment.environment plan).language rfl valid.sourceTyped.1 valid.sourceTyped.2.2.1 with same | same | same
    · rw [same] at found
      have empty : ScopedRuleMatching.matchAt (oriented .reverse).rule
          (oriented .reverse).binding.spec 0 .left [] 0 []
          (oriented .reverse).rule.left one.eraseBinderMetadata = [] := by cbv
      simp only [SiteData.here, List.length_nil] at found
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)
    · exact .inr ⟨same, targetIs⟩
    · rw [same] at found
      have empty : ScopedRuleMatching.matchAt (oriented .reverse).rule
          (oriented .reverse).binding.spec 0 .left [] 0 []
          (oriented .reverse).rule.left done.eraseBinderMetadata = [] := by cbv
      simp only [SiteData.here, List.length_nil] at found
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)

def normal (source : Pattern) : Pattern := if source = one then two else source

theorem normalizer : Complete.Coherence.Normalizer
    (GeneralOccurrenceSemantics.Equation plan [] term) normal where
  sound source := by
    by_cases same : source = one
    · subst source
      exact .rel _ _ ⟨conversionReceipt .forward ⟨0, by decide⟩,
        conversion_receipt_valid .forward ⟨0, by decide⟩, rfl⟩
    · simpa only [normal, same, if_false] using
        Relation.EqvGen.refl (r := GeneralOccurrenceSemantics.Equation plan [] term) source
  canonical source target edge := by
    rcases equation_edge_shape edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [normal, one, two]

theorem normal_source {source : Pattern} (typed : Source source) : Source (normal source) := by
  by_cases same : source = one
  · simpa [normal, same] using literal_source two (.inr (.inl rfl))
  · simpa only [normal, same, if_false] using typed

theorem normal_source_iff (source : Pattern) : Source (normal source) ↔ Source source := by
  constructor
  · intro typed
    by_cases same : source = one
    · simpa only [same] using literal_source one (.inl rfl)
    · simpa only [normal, same, if_false] using typed
  · exact normal_source

theorem primitive_shape {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : GeneralOccurrenceSemantics.Primitive plan [] term source receipt) :
    source = two ∧ receipt.target = done := by
  have site := licensed_root valid.1.2
  have member := List.fst_mem_of_mem_zipIdx valid.1.1
  change receipt.job.declaration ∈ (compile (snapshot true) permissions).rules at member
  rw [runtime_plan_actual] at member
  change receipt.job.declaration ∈ [declaration 0, declaration 1] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have lhs : receipt.job.declaration.rule.left = two := by
    rcases member with same | same <;> rw [same] <;> rfl
  have computed : ScopedRuleMatching.reductWith?
      (ScopedReflectiveExecution.binderOperation (GeneralPlanEnvironment.environment plan).reflection
        receipt.job.declaration.rule) receipt.job.declaration.rule receipt.job.declaration.binding.spec
      (SiteData.here [] term source).focusBound.length receipt.completed = some done := by
    rcases member with same | same <;> rw [same] <;> cbv
  have reduced := (GeneralRuleJobs.receipt_root_readout valid).2.2.2.1
  rw [site] at reduced
  have localTarget : receipt.localTarget = done :=
    (Option.some.inj (computed.symm.trans reduced)).symm
  have targetIs : receipt.target = done := by
    rw [valid.2.2.2.1, site, localTarget]
    rfl
  refine ⟨?_, targetIs⟩
  have firing := valid.2.1
  have selected := GeneralRuleJobs.Job.selected_rule valid.1
  rw [site] at firing
  cases firing with
  | @fire bound type source target index matchingSchema matchingSpec trace captured completed history
      declared specification admitted sourceTyped matching capturedTyped premises reduced targetTyped =>
    have schemaSame : matchingSchema = receipt.job.declaration.rule :=
      Option.some.inj (declared.symm.trans selected)
    subst matchingSchema
    have found := matching.matching.complete
    rw [lhs] at found
    rcases source_cases_of_typed (GeneralPlanEnvironment.environment plan).language rfl
        sourceTyped.1 sourceTyped.2.2.1 with same | same | same
    · rw [same] at found
      have empty : ScopedRuleMatching.matchAt receipt.job.declaration.rule matchingSpec
          0 .left [] 0 [] two one = [] := by cbv
      simp only [SiteData.here, List.length_nil] at found
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)
    · exact same
    · rw [same] at found
      have empty : ScopedRuleMatching.matchAt receipt.job.declaration.rule matchingSpec
          0 .left [] 0 [] two done = [] := by cbv
      simp only [SiteData.here, List.length_nil] at found
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)

def raw : Mettapedia.GSLT.GSLT := GSLTTypeSynthesis.equalityGSLT Pattern
  (fun source target => ∃ receipt,
    GeneralOccurrenceSemantics.Primitive plan [] term source receipt ∧ receipt.target = target)

theorem raw_step_iff (source target : Pattern) :
    raw.Step source target ↔ source = two ∧ target = done := by
  constructor
  · rintro ⟨receipt, valid, rfl⟩
    exact primitive_shape valid
  · rintro ⟨rfl, rfl⟩
    exact ⟨reductionReceipt ⟨0, by decide⟩, reduction_receipt_valid ⟨0, by decide⟩, rfl⟩

theorem certificate : Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate raw
    (GeneralOccurrenceSemantics.Equation plan [] term) normal where
  normalizer := normalizer
  raw_equations := by
    intro first second same
    change first = second at same
    subst second
    exact .refl _
  normalize_step := by
    intro source target step
    obtain ⟨rfl, rfl⟩ := (raw_step_iff source target).mp step
    refine ⟨done, ?_, .refl _⟩
    apply (raw_step_iff _ _).mpr
    simp [normal, two, one]

def receipts (source : Pattern) : List GeneralRuleJobs.Receipt :=
  if source = two then [reductionReceipt ⟨0, by decide⟩, reductionReceipt ⟨1, by decide⟩] else []

theorem receipts_valid (source : Pattern) (receipt : GeneralRuleJobs.Receipt)
    (member : receipt ∈ receipts source) :
    GeneralOccurrenceSemantics.Primitive plan [] term source receipt := by
  unfold receipts at member
  split at member
  next same =>
    subst source
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact reduction_receipt_valid ⟨0, by decide⟩
    · exact reduction_receipt_valid ⟨1, by decide⟩
  next => simp only [List.not_mem_nil] at member

theorem receipts_sound (source : Pattern) (receipt : GeneralRuleJobs.Receipt)
    (member : receipt ∈ receipts source) : raw.Step source receipt.target :=
  ⟨receipt, receipts_valid source receipt member, rfl⟩

theorem receipts_cover (source target : Pattern) (step : raw.Step source target) :
    ∃ receipt, receipt ∈ receipts source ∧ raw.Equiv target receipt.target := by
  obtain ⟨rfl, rfl⟩ := (raw_step_iff source target).mp step
  exact ⟨reductionReceipt ⟨0, by decide⟩, by simp [receipts], rfl⟩

def frontier (budget : Nat) (source : Pattern) : List GeneralRuleJobs.Receipt :=
  if budget = 0 then [] else receipts source

def rawBackend : Backend raw Source where
  Receipt _ := GeneralRuleJobs.Receipt
  target _ receipt := receipt.target
  frontier := frontier
  closed budget _ := budget != 0
  sound budget source receipt member := by
    have nonzero : budget ≠ 0 := by
      intro same
      simp only [frontier, same, if_pos, List.not_mem_nil] at member
    exact receipts_sound source receipt (by simpa only [frontier, nonzero, if_false] using member)
  coverage budget source finished target step := by
    have nonzero : budget ≠ 0 := by simpa using finished
    obtain ⟨receipt, listed, equal⟩ := receipts_cover source target step
    exact ⟨receipt, by simpa only [frontier, nonzero, if_false] using listed, equal⟩
  target_admitted budget source _ receipt member := by
    have nonzero : budget ≠ 0 := by
      intro same
      simp only [frontier, same, if_pos, List.not_mem_nil] at member
    have step := receipts_sound source receipt
      (by simpa only [frontier, nonzero, if_false] using member)
    rw [(raw_step_iff source receipt.target).mp step |>.2]
    exact literal_source done (.inr (.inr rfl))
  completionBudget _ := 1
  complete_at _ _ := rfl
  frontier_stable source budget enough := by
    have nonzero : budget ≠ 0 := by omega
    simp [frontier, nonzero]
  closed_stable _ budget enough := by
    have nonzero : budget ≠ 0 := by omega
    simp [nonzero]

def rawCursor : Mettapedia.OSLF.NativeTypes.Decision.Machine.CursorBackend raw Source where
  Receipt _ := GeneralRuleJobs.Receipt
  target _ receipt := receipt.target
  tasks source := .pause fun _ => Stream.ofList (receipts source)
  sound source receipt member :=
    receipts_sound source receipt (by simpa only [Stream.flatten, Stream.flatten_ofList] using member)
  coverage source _ target step := by
    obtain ⟨receipt, listed, equal⟩ := receipts_cover source target step
    exact ⟨receipt, by simpa only [Stream.flatten, Stream.flatten_ofList] using listed, equal⟩
  target_admitted source _ receipt member := by
    have step := receipts_sound source receipt
      (by simpa only [Stream.flatten, Stream.flatten_ofList] using member)
    rw [(raw_step_iff source receipt.target).mp step |>.2]
    exact literal_source done (.inr (.inr rfl))

def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {operational := permissions}

def chosen : Snapshot := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot (snapshot true) fragment

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated : Mettapedia.OSLF.NativeTypes.Generation.Generated :=
  Mettapedia.OSLF.NativeTypes.Generation.generate (snapshot true) fragment
    Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem generated_snapshot : generated.snapshot = snapshot true := by
  change Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot (snapshot true) fragment = _
  simp only [Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot, fragment,
    Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]

theorem generated_plan : generated.plan = plan := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.plan
  rw [generated_snapshot]
  rfl

def generatedBackend : Backend (Mettapedia.OSLF.NativeTypes.Instances.Normalized.raw generated [] term)
    (Mettapedia.OSLF.NativeTypes.Instances.Normalized.Source generated [] term) where
  Receipt _ := GeneralRuleJobs.Receipt
  target _ receipt := receipt.target
  frontier := frontier
  closed budget _ := budget != 0
  sound budget source receipt member := by
    change ∃ witness, GeneralOccurrenceSemantics.Primitive generated.plan [] term source witness ∧ _
    rw [generated_plan]
    exact rawBackend.sound budget source receipt member
  coverage budget source finished target step := by
    change ∃ witness, GeneralOccurrenceSemantics.Primitive generated.plan [] term source witness ∧ _ at step
    rw [generated_plan] at step
    exact rawBackend.coverage budget source finished target step
  target_admitted budget source _ receipt member := by
    change OpenPatternWellSorted generated.snapshot.language generated.snapshot.free [] term receipt.target
    rw [generated_snapshot]
    have step := rawBackend.sound budget source receipt member
    rw [(raw_step_iff source receipt.target).mp step |>.2]
    exact literal_source done (.inr (.inr rfl))
  completionBudget _ := 1
  complete_at _ _ := rfl
  frontier_stable := rawBackend.frontier_stable
  closed_stable := rawBackend.closed_stable

def generatedCursor : Mettapedia.OSLF.NativeTypes.Decision.Machine.CursorBackend
    (Mettapedia.OSLF.NativeTypes.Instances.Normalized.raw generated [] term)
    (Mettapedia.OSLF.NativeTypes.Instances.Normalized.Source generated [] term) where
  Receipt _ := GeneralRuleJobs.Receipt
  target _ receipt := receipt.target
  tasks source := .pause fun _ => Stream.ofList (receipts source)
  sound source receipt member := by
    change ∃ witness, GeneralOccurrenceSemantics.Primitive generated.plan [] term source witness ∧ _
    rw [generated_plan]
    exact rawCursor.sound source receipt member
  coverage source _ target step := by
    change ∃ witness, GeneralOccurrenceSemantics.Primitive generated.plan [] term source witness ∧ _ at step
    rw [generated_plan] at step
    exact receipts_cover source target step |>.imp fun receipt valid =>
      ⟨by simpa only [Stream.flatten, Stream.flatten_ofList] using valid.1, valid.2⟩
  target_admitted source _ receipt member := by
    change OpenPatternWellSorted generated.snapshot.language generated.snapshot.free [] term receipt.target
    rw [generated_snapshot]
    have step := rawCursor.sound source receipt member
    rw [(raw_step_iff source receipt.target).mp step |>.2]
    exact literal_source done (.inr (.inr rfl))

def profile : Profile generated [] term where
  nf := normal
  certificate := by
    change Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate
      (Mettapedia.OSLF.NativeTypes.Instances.Normalized.raw generated [] term)
      (GeneralOccurrenceSemantics.Equation generated.plan [] term) normal
    unfold Mettapedia.OSLF.NativeTypes.Instances.Normalized.raw
    rw [generated_plan]
    exact certificate
  foundation := by
    rw [generated_plan]
    change (compile (snapshot true) permissions).complete = true
    rw [runtime_plan_actual]
    cbv
  normal_admitted source typed := by
    unfold Mettapedia.OSLF.NativeTypes.Instances.Normalized.Source
    rw [generated_snapshot]
    exact (normal_source_iff source).mpr typed
  base := generatedBackend
  cursor := generatedCursor
  provenance := {
    finiteOrigin _ receipt := receipt
    finite_valid := by
      intro budget source receipt member
      change GeneralRuleJobs.Receipt at receipt
      rw [generated_plan]
      change receipt ∈ frontier budget source at member
      have nonzero : budget ≠ 0 := by
        intro same
        simp only [frontier, same, if_pos, List.not_mem_nil] at member
      exact receipts_valid source receipt
        (by simpa only [frontier, nonzero, if_false] using member)
    finite_target _ _ := rfl
    cursorOrigin _ receipt := receipt
    cursor_valid := by
      intro source receipt member
      change GeneralRuleJobs.Receipt at receipt
      rw [generated_plan]
      change receipt ∈ (Stream.pause (fun _ => Stream.ofList (receipts source))).flatten at member
      exact receipts_valid source receipt
        (by simpa only [Stream.flatten, Stream.flatten_ofList] using member)
    cursor_target _ _ := rfl }
  profileChoice := .displayed
    (Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.allStar generated.snapshot.language) [] rfl
  observations := [⟨"Done", ⟨2, by decide⟩, fun source => source == done⟩]

def doneFormula : profile.driver.Formula := .atom ⟨0, by decide⟩

def decision (formula : profile.driver.Formula) (source : Pattern) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Runtime.search profile.driver profile.engine formula source budget

#guard generated.plan.equations.length == 2
#guard generated.equationAdmission == none
#guard profile.profileChoice.status == some true
#guard (decision (.possibility doneFormula) one 0).readout == .judgment .unknown
#guard (decision (.possibility doneFormula) one 40).readout == .judgment (.decided true)
#guard (decision (.possibility doneFormula) two 40).readout == .judgment (.decided true)
#guard (decision (.possibility doneFormula) done 40).readout == .judgment (.decided false)
#guard (decision (.outgoingUniversal doneFormula) one 40).readout == .judgment (.decided true)
#guard (decision (.outgoingUniversal .bottom) one 40).readout == .judgment (.decided false)
#guard (decision (.possibility doneFormula) (.apply "Undeclared" []) 40).readout ==
  .sourceRefused .illScopedOrSorted
#guard (profile.engine.cursor.tasks one).flatten.map (fun receipt => receipt.job.declaration.declarationIndex) == [0, 1]
#guard (decision (.outgoingUniversal doneFormula) one 40).observations.map
    (fun observed => observed.receipt.job.declaration.declarationIndex) == [0, 1]
#guard (Mettapedia.OSLF.NativeTypes.Runtime.resume 33
    (decision (.possibility doneFormula) one 7)).readout ==
  (decision (.possibility doneFormula) one 40).readout
#guard (Mettapedia.OSLF.NativeTypes.Runtime.resume 33
    (decision (.possibility doneFormula) one 7)).spent ==
  (decision (.possibility doneFormula) one 40).spent

theorem normalized_source_has_real_authored_step :
    (GeneralOccurrenceSemantics.gslt generated.plan [] term).Step one done := by
  rw [generated_plan]
  exact equation_exposes_done

theorem normalized_runtime_compares_actual_source (source target : Pattern) :
    profile.system.Step source target ↔
      (GeneralOccurrenceSemantics.gslt generated.plan [] term).Step source target :=
  profile.step_iff_source source target

theorem source_equation_is_nontrivial :
    (GeneralOccurrenceSemantics.gslt generated.plan [] term).Equiv one two ∧ one ≠ two := by
  constructor
  · rw [generated_plan]
    change Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan [] term) one two
    simpa only [request_root, plan] using equation_exposes_two
  · decide

def executableRequest : Mettapedia.OSLF.NativeTypes.Executable.Request :=
  .normalized (snapshot true) fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
    vertex [] term profile

def legacyRequest : Mettapedia.OSLF.NativeTypes.Executable.Request :=
  .authored (snapshot true) fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
    vertex [] term (fun _ _ _ _ => true)

def publicObserve (query : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Query)
    (source : Pattern) (budget : Nat) :=
  (Mettapedia.OSLF.NativeTypes.Executable.generate executableRequest).map fun installed =>
    (Mettapedia.OSLF.NativeTypes.Executable.ask installed query source budget).readout

#guard (Mettapedia.OSLF.NativeTypes.Executable.generate executableRequest).map (fun _ => ()) == .ok ()
#guard (Mettapedia.OSLF.NativeTypes.Executable.generate legacyRequest).map (fun _ => ()) ==
  .error (.authoredLocal .equationCoverageRequired)
#guard publicObserve (.possibility (.constructor "Done")) one 0 ==
  .ok (.checked (.judgment .unknown))
#guard publicObserve (.possibility (.constructor "Done")) one 40 ==
  .ok (.checked (.judgment (.decided true)))
#guard publicObserve (.possibility (.constructor "Done")) done 40 ==
  .ok (.checked (.judgment (.decided false)))
#guard publicObserve (.outgoingUniversal (.constructor "Done")) one 40 ==
  .ok (.checked (.judgment (.decided true)))
#guard publicObserve (.outgoingUniversal .bottom) one 40 ==
  .ok (.checked (.judgment (.decided false)))
#guard publicObserve (.constructor "Unregistered") one 40 ==
  .ok (.unknownConstructor "Unregistered")
#guard publicObserve (.possibility (.constructor "Done")) (.apply "Undeclared" []) 40 ==
  .ok (.checked (.sourceRefused .illScopedOrSorted))

theorem public_generation_retains_inputs
    {installed : Mettapedia.OSLF.NativeTypes.Runtime.Installed}
    (accepted : Mettapedia.OSLF.NativeTypes.Executable.generate executableRequest = .ok installed) :
    installed.native.generated.snapshot = (snapshot true) ∧
      installed.native.generated.languageFragment = fragment := by
  have retained := Mettapedia.OSLF.NativeTypes.Executable.generate_success_inputs accepted
  refine ⟨?_, retained.2.1⟩
  exact retained.1.trans generated_snapshot

theorem done_native_leaf_exact (source : Pattern) :
    (profile.sourceTests ⟨0, by decide⟩).predicate source ↔ source = done := by
  change ((normal source) == done) = true ↔ source = done
  by_cases same : source = one
  · simp [normal, same, one, two, done]
  · simp [normal, same]

theorem actual_source_native_membership :
    (GSLTTypeSynthesis.gsltOSLF (GeneralOccurrenceSemantics.gslt generated.plan [] term)).satisfies
      one (profile.sourceNativeType (.possibility doneFormula)).pred := by
  apply (GSLTTypeSynthesis.gsltDiamond_spec
    (GeneralOccurrenceSemantics.gslt generated.plan [] term)
    (profile.sourceTests ⟨0, by decide⟩).predicate one).mpr
  exact ⟨done, normalized_source_has_real_authored_step, (done_native_leaf_exact done).mpr rfl⟩

theorem actual_source_native_nonmembership :
    ¬ (GSLTTypeSynthesis.gsltOSLF (GeneralOccurrenceSemantics.gslt generated.plan [] term)).satisfies
      done (profile.sourceNativeType (.possibility doneFormula)).pred := by
  intro member
  obtain ⟨target, step, _⟩ := (GSLTTypeSynthesis.gsltDiamond_spec
    (GeneralOccurrenceSemantics.gslt generated.plan [] term)
    (profile.sourceTests ⟨0, by decide⟩).predicate done).mp member
  rw [generated_plan] at step
  obtain ⟨representative, receipt, before, fired, _⟩ := step
  obtain ⟨sourceTwo, _⟩ := primitive_shape fired
  have impossible := normalizer.eqvGen_eq before
  rw [sourceTwo] at impossible
  have different : normal done ≠ normal two := by decide
  exact different impossible

theorem absent_provider_rejects_normalization :
    ¬ Complete.Coherence.Normalizer
      (GeneralOccurrenceSemantics.Equation (request false).plan [] term) normal := by
  intro assumed
  have collapse : ∀ {first second : Pattern}, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation (request false).plan [] term) first second → first = second := by
    intro first second related
    induction related with
    | rel _ _ edge => exact False.elim (no_rows_equation_impossible edge)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  have different : one ≠ normal one := by decide
  exact different (collapse (assumed.sound one))

end Mettapedia.OSLF.NativeTypes.Instances.Normalized.AuthoredControls
