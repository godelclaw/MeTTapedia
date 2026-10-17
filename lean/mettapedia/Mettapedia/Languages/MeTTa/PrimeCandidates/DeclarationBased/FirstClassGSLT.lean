import Mettapedia.GSLT.LanguageDef.ScopedBindingCaptureSupport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RelationalEvidence
import Mettapedia.GSLT.LanguageDef.RelationPresentationRoutes
import Mettapedia.GSLT.LanguageDef.GSLTILNativeKernel
import Mettapedia.GSLT.LanguageDef.SemanticService
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity

/-!
# First-class GSLT presentations and typed routes in cumulative-tower candidate

A validated language presentation is an ordinary typed native value and uses
the single staged quotation former.  An authored GSLT-IL route is separately a
proof-relevant cumulative-tower candidate relation on its selected endpoint fibres.  A route may be
executed relationally without a compilation license; representability is the
additional evidence that exposes a direct map.

`LanguageWorkspace` associates a presentation value with an inventory of
authored routes.  The association is data, not an unstated adequacy theorem:
semantic agreement between a presentation's dynamics and a route program must
be supplied by a separate checked bridge.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace FirstClassGSLT

open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.RelationPresentation

/-! ## Presentation values -/

abbrev PresentationValue :=
  Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef

/-- A presentation is quoted by the same operation as every other native
term. -/
def quotePresentation (level : Nat) (presentation : PresentationValue) :
    StagedReflectiveTm level 0 :=
  nativeQuotedLanguage level presentation

/-- Every first-class presentation value has the ordinary native quotation
type. -/
theorem quotePresentation_hasType (level : Nat)
    (presentation : PresentationValue) :
    NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil
      (quotePresentation level presentation)
      (nativeQuoteNext level
        (StagedReflectiveTm.u0 : StagedReflectiveTm (level + 1) 0)) :=
  nativeQuotedLanguage_has_type level presentation

/-- Quotation retains the complete validated presentation value. -/
@[simp] theorem quotePresentation_roundtrip (level : Nat)
    (presentation : PresentationValue) :
    (quotePresentation level presentation).quotedLanguage? =
      some presentation :=
  quotedLanguage?_nativeQuotedLanguage level presentation

/-! ## Typed authored routes as relational values -/

/-- A first-class authored route, including declaration membership and its
selected native endpoint fibres. -/
structure TypedRouteValue where
  program : Program
  route : RouteDecl
  declared : route ∈ program.routes
  profile : TypedRouteProfile program route

namespace TypedRouteValue

/-- The primary meaning of a typed route is its proof-relevant relation. -/
def relation (value : TypedRouteValue) :
    Mettapedia.GSLT.RelationPresentation.Rel
      value.profile.Source value.profile.Target :=
  AuthoredRoute.internalizeTyped value.profile

/-- A compilation license is exactly representability of the primary
relation; it is not part of route authoring. -/
abbrev License (value : TypedRouteValue) := value.profile.License

/-- Any authored route witness executes in the relational semantics, whether
or not a direct map has been licensed. -/
def execute (value : TypedRouteValue)
    {source : value.profile.Source} {target : value.profile.Target}
    (witness : value.profile.related source target) :
    (value.relation).evidence source target :=
  AuthoredRoute.executeWithoutLicense value.profile witness

/-- A license exposes one direct map on the selected typed fibre. -/
def compile (value : TypedRouteValue) (license : value.License) :
    value.profile.Source → value.profile.Target :=
  value.profile.compile license

/-- Licensed execution agrees fibrewise with the graph of the compiled map. -/
def representedAsGraph (value : TypedRouteValue) (license : value.License)
    (source : value.profile.Source) (target : value.profile.Target) :
    value.relation.evidence source target ≃
      (Mettapedia.GSLT.RelationPresentation.Rel.graph
        (value.compile license)).evidence source target :=
  AuthoredRoute.representedAsGraph license source target

/-- The map exposed through cumulative-tower candidate is the map selected by the GSLT-IL route
license; no second compilation decision is made. -/
@[simp] theorem represented_map_agrees (value : TypedRouteValue)
    (license : value.License) :
    ((AuthoredRoute.licenseEquiv value.profile) license).map =
      value.compile license :=
  AuthoredRoute.represented_map_agrees license

end TypedRouteValue

/-- A first-class language workspace.  Route-to-presentation adequacy is not
assumed by this container. -/
structure LanguageWorkspace where
  presentation : PresentationValue
  routes : List TypedRouteValue

namespace LanguageWorkspace

def quoted (workspace : LanguageWorkspace) (level : Nat) :
    StagedReflectiveTm level 0 :=
  quotePresentation level workspace.presentation

theorem quoted_hasType (workspace : LanguageWorkspace) (level : Nat) :
    NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil
      (workspace.quoted level)
      (nativeQuoteNext level
        (StagedReflectiveTm.u0 : StagedReflectiveTm (level + 1) 0)) :=
  quotePresentation_hasType level workspace.presentation

@[simp] theorem quoted_roundtrip (workspace : LanguageWorkspace)
    (level : Nat) :
    (workspace.quoted level).quotedLanguage? =
      some workspace.presentation :=
  quotePresentation_roundtrip level workspace.presentation

end LanguageWorkspace

/-! ## Positive admitted route -/

def atom (name : String) : Pattern := .apply name []

def unitRoute : RouteDecl where
  occurrence := atom "unit-route-occurrence"
  name := "unit-route"
  sourceSpace := atom "unit-source-space"
  targetSpace := atom "unit-target-space"

def unitRouteRule : RouteRule where
  occurrence := atom "unit-rule-occurrence"
  name := "unit-route"
  source := atom "unit-input"
  target := atom "unit-output"

def unitRouteProgram : Program where
  spaceRules := []
  routes := [unitRoute]
  routeRules := [unitRouteRule]

def unitRouteProfile : TypedRouteProfile unitRouteProgram unitRoute where
  Source := Unit
  Target := Unit
  sourcePattern _ := atom "unit-input"
  targetPattern _ := atom "unit-output"

def unitRouteValue : TypedRouteValue where
  program := unitRouteProgram
  route := unitRoute
  declared := by simp [unitRouteProgram]
  profile := unitRouteProfile

def unitRouteWitness : unitRouteProfile.related () () where
  routeMember := by simp [unitRouteProgram]
  rule := unitRouteRule
  ruleMember := by simp [unitRouteProgram]
  nameEq := rfl
  sourceEq := rfl
  targetEq := rfl

instance unitRouteWitness_subsingleton :
    Subsingleton (unitRouteProfile.related () ()) where
  allEq first second := by
    rcases first with
      ⟨_firstRouteMember, firstRule, firstRuleMember,
        _firstName, _firstSource, _firstTarget⟩
    rcases second with
      ⟨_secondRouteMember, secondRule, secondRuleMember,
        _secondName, _secondSource, _secondTarget⟩
    have firstRuleEq : firstRule = unitRouteRule := by
      simpa [unitRouteProgram] using firstRuleMember
    have secondRuleEq : secondRule = unitRouteRule := by
      simpa [unitRouteProgram] using secondRuleMember
    subst firstRule
    subst secondRule
    rfl

/-- The singleton typed route earns a direct identity map. -/
def unitRouteLicense : unitRouteValue.License where
  map := _root_.id
  exact source target := by
    cases source
    cases target
    exact
      { toFun := fun _ => ⟨⟨rfl⟩⟩
        invFun := fun _ => unitRouteWitness
        left_inv := by
          intro witness
          change unitRouteWitness = witness
          exact unitRouteWitness_subsingleton.allEq _ _
        right_inv := by
          rintro ⟨⟨proof⟩⟩
          rfl }

theorem unitRoute_executes :
    Nonempty (unitRouteValue.relation.evidence () ()) :=
  ⟨unitRouteValue.execute unitRouteWitness⟩

@[simp] theorem unitRoute_compiles_to_identity :
    unitRouteValue.compile unitRouteLicense = _root_.id :=
  rfl

/-! ## Negative unlicensed route with duplicate occurrences -/

def duplicateFirstRule : RouteRule :=
  { unitRouteRule with occurrence := atom "duplicate-first-occurrence" }

def duplicateSecondRule : RouteRule :=
  { unitRouteRule with occurrence := atom "duplicate-second-occurrence" }

def duplicateRouteProgram : Program where
  spaceRules := []
  routes := [unitRoute]
  routeRules := [duplicateFirstRule, duplicateSecondRule]

def duplicateRouteProfile :
    TypedRouteProfile duplicateRouteProgram unitRoute where
  Source := Unit
  Target := Unit
  sourcePattern _ := atom "unit-input"
  targetPattern _ := atom "unit-output"

def duplicateRouteValue : TypedRouteValue where
  program := duplicateRouteProgram
  route := unitRoute
  declared := by simp [duplicateRouteProgram]
  profile := duplicateRouteProfile

def duplicateFirstWitness : duplicateRouteProfile.related () () where
  routeMember := by simp [duplicateRouteProgram]
  rule := duplicateFirstRule
  ruleMember := by simp [duplicateRouteProgram]
  nameEq := rfl
  sourceEq := rfl
  targetEq := rfl

def duplicateSecondWitness : duplicateRouteProfile.related () () where
  routeMember := by simp [duplicateRouteProgram]
  rule := duplicateSecondRule
  ruleMember := by simp [duplicateRouteProgram]
  nameEq := rfl
  sourceEq := rfl
  targetEq := rfl

theorem duplicateWitnesses_distinct :
    duplicateFirstWitness ≠ duplicateSecondWitness := by
  intro equal
  have rulesEqual := congrArg RouteWitness.rule equal
  have occurrencesEqual := congrArg RouteRule.occurrence rulesEqual
  change atom "duplicate-first-occurrence" =
    atom "duplicate-second-occurrence" at occurrencesEqual
  simp [atom] at occurrencesEqual

theorem duplicateRoute_executes_twice :
    Nonempty (duplicateRouteValue.relation.evidence () ()) ∧
      Nonempty (duplicateRouteValue.relation.evidence () ()) :=
  ⟨⟨duplicateRouteValue.execute duplicateFirstWitness⟩,
    ⟨duplicateRouteValue.execute duplicateSecondWitness⟩⟩

/-- Visible single-valuedness does not license compilation when two authored
occurrences inhabit the same proof-relevant fibre. -/
theorem duplicateRoute_not_licensed :
    ¬ Nonempty duplicateRouteValue.License := by
  rintro ⟨license⟩
  have pairEqual := (license.deterministic ()).allEq
    (⟨(), duplicateFirstWitness⟩ :
      Sigma fun target => duplicateRouteProfile.related () target)
    ⟨(), duplicateSecondWitness⟩
  exact duplicateWitnesses_distinct
    (eq_of_heq (Sigma.mk.inj pairEqual).2)

/-! ## Declaration-backed cumulative values for the finite command service

This consumer is distinct from the staged quotation interface above. Source
operations are executed by the admitted command service; their returned native
terms earn actual cumulative formation under a generated finite installation.
A native proof-family compiler, unrestricted ambient conversion reflection and
an implementation-level evaluator comparison are separate obligations.
-/

namespace FiniteCatalogInterpretation

open Mettapedia.GSLT.LanguageDef.GSLTIL.NativeCommand

open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature

/-- Complete raw payload inventory, including occurrence identities. -/
def programPatterns (program : Program) : List Pattern :=
  program.spaceRules.flatMap (fun row => [row.occurrence, row.space, row.source, row.target]) ++
    program.routes.flatMap (fun row => [row.occurrence, row.sourceSpace, row.targetSpace]) ++
    program.routeRules.flatMap (fun row => [row.occurrence, row.source, row.target])

theorem programPatterns_scoped (workspace : Workspace) {pattern : Pattern}
    (present : pattern ∈ programPatterns workspace.program) :
    pattern.isWellScopedAt workspace.scope = true := by
  rcases workspace.formed with ⟨spaces, declarations, routes⟩
  simp only [programPatterns, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at present
  rcases present with (spaceCase | route) | row
  · obtain ⟨selected, member, cases⟩ := spaceCase
    rcases spaces selected member with ⟨occurrence, space, source, target⟩
    rcases cases with rfl | rfl | rfl | rfl <;> assumption
  · obtain ⟨selected, member, cases⟩ := route
    rcases declarations selected member with ⟨occurrence, source, target⟩
    rcases cases with rfl | rfl | rfl <;> assumption
  · obtain ⟨selected, member, cases⟩ := row
    rcases routes selected member with ⟨occurrence, source, target⟩
    rcases cases with rfl | rfl | rfl <;> assumption

/-- Extract actual finite constructor support by the checked raw refiner. -/
def constructors (scope : Nat) (patterns : List Pattern) : List (PatOp .pat) :=
  patterns.flatMap fun pattern =>
    (Mettapedia.OSLF.MeTTaIL.ScopedSyntax.fromPattern? scope pattern).toList.flatMap
      (fun term => usedOperators (toTerm term))

def sourceTerm (scope : Nat) (pattern : Pattern)
    (formed : pattern.isWellScopedAt scope = true) :
    Mettapedia.OSLF.Binding.Term patSig (ctxOf scope) .pat :=
  toTerm (Mettapedia.OSLF.MeTTaIL.ScopedSyntax.refine scope pattern formed)

def nativeValue (scope : Nat) (pattern : Pattern)
    (formed : pattern.isWellScopedAt scope = true) : Tower.Tm (ctxOf scope).length :=
  BindingSignatureEmbedding.encode names (sourceTerm scope pattern formed)

theorem sourceTerm_readout (scope : Nat) (pattern : Pattern)
    (formed : pattern.isWellScopedAt scope = true) :
    erase (sourceTerm scope pattern formed) = pattern := by
  rw [sourceTerm, erase_toTerm]
  exact Mettapedia.OSLF.MeTTaIL.ScopedSyntax.refine_readout scope pattern formed

theorem constructors_cover (scope : Nat) {patterns : List Pattern} {pattern : Pattern}
    (present : pattern ∈ patterns) (formed : pattern.isWellScopedAt scope = true)
    {operator : PatOp .pat} (used : operator ∈ usedOperators (sourceTerm scope pattern formed)) :
    operator ∈ constructors scope patterns := by
  have parsed : Mettapedia.OSLF.MeTTaIL.ScopedSyntax.fromPattern? scope pattern =
      some (Mettapedia.OSLF.MeTTaIL.ScopedSyntax.refine scope pattern formed) := by
    have roundtrip := Mettapedia.OSLF.MeTTaIL.ScopedSyntax.fromPattern?_toPattern
      (Mettapedia.OSLF.MeTTaIL.ScopedSyntax.refine scope pattern formed)
    simpa only [Mettapedia.OSLF.MeTTaIL.ScopedSyntax.refine_readout] using roundtrip
  apply List.mem_flatMap.mpr
  refine ⟨pattern, present, ?_⟩
  simp only [parsed, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact used

/-- The installation covers the actual program fields, request and complete
computed answer list. No all-operator lookup callback is assumed. -/
def installationPatterns (workspace : Workspace) (source : Pattern) : List Pattern :=
  programPatterns workspace.program ++ source :: (successors workspace.program source).map Prod.snd

def installation (workspace : Workspace) (source : Pattern) : List (PatOp .pat) :=
  constructors workspace.scope (installationPatterns workspace source)

theorem installation_formed (workspace : Workspace) (source : Pattern) :
    (signature (installation workspace source)).WellFormed Tower.rules :=
  wellFormed (installation workspace source)

theorem value_judgment (workspace : Workspace) (source : Pattern)
    {pattern : Pattern} (present : pattern ∈ installationPatterns workspace source)
    (formed : pattern.isWellScopedAt workspace.scope = true) :
    FormationSensitive.Judgment (rules (installation workspace source))
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
      (nativeValue workspace.scope pattern formed)
      (BindingSignatureEmbedding.sortType names .pat) :=
  supported_judgment (installation workspace source)
    (sourceTerm workspace.scope pattern formed)
    (fun _ used => constructors_cover workspace.scope present formed used)

theorem program_field_judgment (workspace : Workspace) (source : Pattern)
    {pattern : Pattern} (present : pattern ∈ programPatterns workspace.program) :
    FormationSensitive.Judgment (rules (installation workspace source))
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
      (nativeValue workspace.scope pattern (programPatterns_scoped workspace present))
      (BindingSignatureEmbedding.sortType names .pat) :=
  value_judgment workspace source (List.mem_append_left _ present) _

theorem source_judgment (workspace : Workspace) (source : Pattern)
    (formed : source.isWellScopedAt workspace.scope = true) :
    FormationSensitive.Judgment (rules (installation workspace source))
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
      (nativeValue workspace.scope source formed)
      (BindingSignatureEmbedding.sortType names .pat) :=
  value_judgment workspace source (List.mem_append_right _ List.mem_cons_self) formed

/-- Computed native answers retain authored instruction positions. The
original raw answer is used only by the checked source-to-native construction. -/
def answers (workspace : Workspace) (source : Pattern) :
    List (Instruction × Tower.Tm (ctxOf workspace.scope).length) :=
  (successors workspace.program source).attach.map fun entry =>
    (entry.val.1, nativeValue workspace.scope entry.val.2
      (((mem_successors_iff workspace.program source entry.val.2 entry.val.1).mp
        entry.property).target_wellScoped workspace.formed))

theorem answers_exact (workspace : Workspace) (source : Pattern)
    (instruction : Instruction) (native : Tower.Tm (ctxOf workspace.scope).length) :
    (instruction, native) ∈ answers workspace source ↔
      ∃ (output : Pattern) (formed : output.isWellScopedAt workspace.scope = true),
        Instruction.Judges workspace.program instruction source output ∧
          native = nativeValue workspace.scope output formed := by
  constructor
  · intro member
    unfold answers at member
    obtain ⟨⟨⟨selected, output⟩, present⟩, _attached, same⟩ := List.mem_map.mp member
    obtain ⟨rfl, nativeSame⟩ := Prod.mk.inj same
    have judged := (mem_successors_iff workspace.program source output selected).mp present
    exact ⟨output, judged.target_wellScoped workspace.formed, judged, nativeSame.symm⟩
  · rintro ⟨output, formed, judged, rfl⟩
    have present := (mem_successors_iff workspace.program source output instruction).mpr judged
    unfold answers
    apply List.mem_map.mpr
    refine ⟨⟨(instruction, output), present⟩, List.mem_attach _ _, ?_⟩
    rfl

theorem answer_judgment (workspace : Workspace) (source : Pattern)
    {instruction : Instruction} {native : Tower.Tm (ctxOf workspace.scope).length}
    (member : (instruction, native) ∈ answers workspace source) :
    FormationSensitive.Judgment (rules (installation workspace source))
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) native
      (BindingSignatureEmbedding.sortType names .pat) := by
  obtain ⟨output, formed, judged, rfl⟩ := (answers_exact workspace source instruction native).mp member
  have present := (mem_successors_iff workspace.program source output instruction).mpr judged
  apply value_judgment workspace source
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, present, rfl⟩))

/-- Native emitted answers never invent a source operation. This is a
service-image theorem, not reflection of arbitrary ambient conversion. -/
theorem answer_reflects_step (workspace : Workspace) (source : Pattern)
    {instruction : Instruction} {native : Tower.Tm (ctxOf workspace.scope).length}
    (member : (instruction, native) ∈ answers workspace source) :
    ∃ output, Step workspace.program source output ∧
      ∃ formed, native = nativeValue workspace.scope output formed := by
  obtain ⟨output, formed, judged, same⟩ := (answers_exact workspace source instruction native).mp member
  exact ⟨output, Instruction.stepOfJudges judged, formed, same⟩

/-- Every independently specified immediate source step has an emitted native
answer, under the very installation used for every other answer. -/
theorem source_step_covered (workspace : Workspace) {source output : Pattern}
    (step : Step workspace.program source output) :
    ∃ (instruction : Instruction) (formed : output.isWellScopedAt workspace.scope = true),
      (instruction, nativeValue workspace.scope output formed) ∈ answers workspace source := by
  obtain ⟨instruction, judged⟩ := (Instruction.exists_judges_iff_step workspace.program source output).mpr step
  refine ⟨instruction, judged.target_wellScoped workspace.formed, ?_⟩
  exact (answers_exact workspace source instruction _).mpr ⟨output, _, judged, rfl⟩

theorem answers_length (workspace : Workspace) (source : Pattern) :
    (answers workspace source).length = (successors workspace.program source).length := by
  simp only [answers, List.length_map, List.length_attach]

/-- The native service returns one literal finite installation and native
answer values. Its proof of formation is constructed by the implementation. -/
structure Result (workspace : Workspace) where
  source : Pattern
  operators : List (PatOp .pat)
  outputs : List (Instruction × Tower.Tm (ctxOf workspace.scope).length)

/-- Meaning uses original command judgments and actual cumulative typing.
Neither coverage nor formation is defined by successful execution. -/
def target (workspace : Workspace) :
    Mettapedia.GSLT.LanguageDef.SemanticEvidence.AdmissionObject where
  Carrier := Result workspace
  Meaning result :=
    result.source.isWellScopedAt workspace.scope = true ∧
      (signature result.operators).WellFormed Tower.rules ∧
      (∀ pattern ∈ programPatterns workspace.program,
        ∃ formed : pattern.isWellScopedAt workspace.scope = true,
          FormationSensitive.Judgment (rules result.operators)
            (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
            (nativeValue workspace.scope pattern formed)
            (BindingSignatureEmbedding.sortType names .pat)) ∧
      (∀ instruction native, (instruction, native) ∈ result.outputs ↔
        ∃ (output : Pattern) (formed : output.isWellScopedAt workspace.scope = true),
          Instruction.Judges workspace.program instruction result.source output ∧
            native = nativeValue workspace.scope output formed) ∧
      (∀ instruction native, (instruction, native) ∈ result.outputs →
        FormationSensitive.Judgment (rules result.operators)
          (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) native
          (BindingSignatureEmbedding.sortType names .pat))

/-- A concrete operation through the current native-service boundary. It
executes admitted source commands and constructs formed cumulative values;
it does not install an ambient conversion rule for every source step. -/
def operation (workspace : Workspace) : operationSource workspace ⟶ target workspace where
  run source := ⟨source, installation workspace source, answers workspace source⟩
  preserves source formed := by
    refine ⟨formed, installation_formed workspace source, ?_,
      answers_exact workspace source, ?_⟩
    · intro pattern present
      exact ⟨programPatterns_scoped workspace present,
        program_field_judgment workspace source present⟩
    · intro instruction native present
      exact answer_judgment workspace source present

def service (workspace : Workspace) :
    Mettapedia.GSLT.LanguageDef.SemanticService.Service (target workspace) :=
  .nativeOperation (operationSource workspace) (operation workspace)

/-- A refused source instruction cannot acquire an answer by being lowered
to the cumulative native value interface. -/
theorem refused_instruction_no_native_answer (workspace : Workspace) (source : Pattern)
    (instruction : Instruction)
    (refused : Instruction.execute workspace.program instruction source = none) :
    ∀ native, (instruction, native) ∉ answers workspace source := by
  intro native member
  obtain ⟨output, _formed, judged, _same⟩ := (answers_exact workspace source instruction native).mp member
  have accepted := (Instruction.execute_iff_judges workspace.program instruction source output).mpr judged
  rw [refused] at accepted
  cases accepted

theorem canary_native_occurrences :
    (answers Canary.workspace Canary.request).length = 3 := by
  rw [answers_length]
  change (successors Canary.authored Canary.request).length = 3
  rw [Canary.duplicate_answers_retained]
  rfl

theorem canary_extra_behavior_not_authorized :
    ∀ native, (.transport 0 2, native) ∉ answers Canary.workspace Canary.request :=
  refused_instruction_no_native_answer Canary.workspace Canary.request (.transport 0 2)
    Canary.added_behavior_separated.2.1

/-! ## Native proof programs for the literal finite command calculus

The generated declarations contain one occurrence-indexed primitive proof
for each actual selected command template, together with reflexivity and
composition. All types and declarations are formed in the cumulative
calculus. Every independently judged source script compiles to a typed
native proof, and literal proof readback retains its instruction occurrences.

The certificate interface below reflects this compiler image. It does not
classify arbitrary ambient native inhabitants or conversion, and the source
Program remains the literal-row command calculus rather than arbitrary
authored schema matching. No executed time bound is asserted here.
-/

namespace Proof

open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
open Declaration FormationSensitive TelescopeAbstraction

structure Primitive where
  instruction : Instruction
  source : Pattern
  target : Pattern
  deriving DecidableEq

def primitives (program : Program) : List Primitive :=
  (instructionInventory program).filterMap fun instruction =>
    (Instruction.template program instruction).map fun ends => ⟨instruction, ends.1, ends.2⟩

theorem primitives_exact (program : Program) (primitive : Primitive) :
    primitive ∈ primitives program ↔
      Instruction.Judges program primitive.instruction primitive.source primitive.target := by
  constructor
  · intro member
    obtain ⟨instruction, _inInventory, selected⟩ := List.mem_filterMap.mp member
    obtain ⟨ends, known, same⟩ := Option.map_eq_some_iff.mp selected
    cases same
    exact (Instruction.template_iff_judges program instruction ends.1 ends.2).mp known
  · intro judged
    apply List.mem_filterMap.mpr
    refine ⟨primitive.instruction, instructionInventory_complete judged, ?_⟩
    rw [(Instruction.template_iff_judges program _ _ _).mpr judged]
    rfl

def patterns (workspace : Workspace) (claim : Claim) : List Pattern :=
  programPatterns workspace.program ++ [claim.source, claim.target] ++
    (primitives workspace.program).flatMap (fun primitive => [primitive.source, primitive.target])

def operators (workspace : Workspace) (claim : Claim) : List (PatOp .pat) :=
  constructors workspace.scope (patterns workspace claim)

def objectRules (workspace : Workspace) (claim : Claim) : Rules Tower.Head :=
  rules (operators workspace claim)

def reachName : DeclName := `GSLT.Command.Reach

def reflName : DeclName := `GSLT.Command.Reflexivity

def transName : DeclName := `GSLT.Command.Composition

def reach {n : Nat} (source target : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const reachName) source) target

@[simp] theorem reach_rename {n m : Nat} (action : Ren n m) (source target : Tower.Tm n) :
    rename action (reach source target) = reach (rename action source) (rename action target) := rfl

@[simp] theorem reach_subst {n m : Nat} (action : Sub Tower.Head n m) (source target : Tower.Tm n) :
    subst action (reach source target) = reach (subst action source) (subst action target) := rfl

def reachType : Tower.Tm 0 :=
  .pi (.const dataName) (.pi (.const dataName) (.head (.sort Tower.zero)))

def reflType : Tower.Tm 0 := .pi (.const dataName) (reach (.var 0) (.var 0))

def transType : Tower.Tm 0 :=
  .pi (.const dataName) (.pi (.const dataName) (.pi (.const dataName)
    (.pi (reach (.var 2) (.var 1))
      (.pi (reach (.var 2) (.var 1)) (reach (.var 4) (.var 2))))))

def primitiveName (index : Nat) : DeclName := .num `GSLT.Command.Primitive index

theorem primitiveName_injective : Function.Injective primitiveName := by
  intro first second same
  exact (Lean.Name.num.inj same).2


private theorem fresh_reach (inventory : List (PatOp .pat)) :
    (rules inventory).constantType reachName = none := by
  change (signature inventory).typeOf? reachName = none
  unfold Signature.typeOf?
  cases selected : (signature inventory).entries reachName with
  | none => rfl
  | some entry =>
      have member := Signature.entries_ofList_mem (declarationList inventory) selected
      rcases List.mem_cons.mp member with same | member
      · have impossible := congrArg Prod.fst same
        cases impossible
      · obtain ⟨operator, _, same⟩ := List.mem_map.mp member
        have impossible := congrArg Prod.fst same
        cases operator with
        | fvarOp name => simp [operatorName, reachName] at impossible
        | applyOp label arity => simp [operatorName, reachName] at impossible
        | lamOp name => cases name <;> simp [operatorName, reachName] at impossible
        | multiLamOp arity names => simp [operatorName, reachName] at impossible
        | substOp => simp [operatorName, reachName] at impossible
        | collOp kind arity rest => cases kind <;> simp [operatorName, reachName] at impossible

def primitiveType (workspace : Workspace)
    (primitive : {p // p ∈ primitives workspace.program}) : Tower.Tm 0 :=
  closeType (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
    (reach
      (nativeValue workspace.scope primitive.val.source
        (Instruction.template_source_scoped workspace.formed
          ((Instruction.template_iff_judges _ _ _ _).mpr
            ((primitives_exact workspace.program primitive.val).mp primitive.property))))
      (nativeValue workspace.scope primitive.val.target
        (((primitives_exact workspace.program primitive.val).mp primitive.property).target_wellScoped
          workspace.formed)))

def primitiveAt (workspace : Workspace) (index : Fin (primitives workspace.program).length) :
    {p // p ∈ primitives workspace.program} :=
  ⟨(primitives workspace.program).get index, List.get_mem _ _⟩

def entries (workspace : Workspace) : List (DeclName × Entry Tower.Head) :=
  [(reachName, ⟨reachType, none⟩), (reflName, ⟨reflType, none⟩),
    (transName, ⟨transType, none⟩)] ++
    List.ofFn (fun index : Fin (primitives workspace.program).length =>
      (primitiveName index.val, ⟨primitiveType workspace (primitiveAt workspace index), none⟩))

def declarations (workspace : Workspace) : Signature Tower.Head :=
  Signature.ofList (entries workspace)

def proofRules (workspace : Workspace) (claim : Claim) : Rules Tower.Head :=
  extendRules (objectRules workspace claim) (declarations workspace)

private theorem include_object {workspace : Workspace} {claim : Claim} {n : Nat}
    {gamma : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing (objectRules workspace claim) gamma term type) :
    Typing (proofRules workspace claim) gamma term type :=
  typed.includeSignature (declarations workspace)

private theorem data_formed (workspace : Workspace) (claim : Claim)
    {n : Nat} (gamma : Tower.Ctx n) :
    Typing (proofRules workspace claim) gamma (.const dataName) (.head (.sort Tower.zero)) :=
  include_object ((sortRealization (operators workspace claim)).sortType_formed gamma .pat)

private theorem pi_zero {workspace : Workspace} {claim : Claim} {n : Nat}
    {gamma : Tower.Ctx n} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (domainFormed : Typing (proofRules workspace claim) gamma domain (.head (.sort Tower.zero)))
    (codomainFormed : Typing (proofRules workspace claim) (.snoc gamma domain) codomain
      (.head (.sort Tower.zero))) :
    Typing (proofRules workspace claim) gamma (.pi domain codomain) (.head (.sort Tower.zero)) := by
  apply Typing.cumul (.piForm domainFormed (.sort _) codomainFormed (.sort _) (.sorts _ _))
  intro valuation
  simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval]

private theorem reachType_formed (workspace : Workspace) (claim : Claim) :
    Typing (proofRules workspace claim) .nil reachType (.head (.sort (.succ Tower.zero))) := by
  have inner := Typing.piForm (data_formed workspace claim (.snoc .nil (.const dataName)))
    (LevelTower.IsUniverse.sort Tower.zero)
    (Typing.headType (R := proofRules workspace claim)
      (LevelTower.HeadTyping.sort (L := Nat) Tower.zero))
    (LevelTower.IsUniverse.sort (.succ Tower.zero))
    (LevelTower.Join.sorts Tower.zero (.succ Tower.zero))
  have outer := Typing.piForm (data_formed workspace claim .nil)
    (LevelTower.IsUniverse.sort Tower.zero) inner
    (LevelTower.IsUniverse.sort (.max Tower.zero (.succ Tower.zero)))
    (LevelTower.Join.sorts Tower.zero (.max Tower.zero (.succ Tower.zero)))
  apply Typing.cumul outer
  intro valuation
  simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero]

private theorem reach_lookup (workspace : Workspace) (claim : Claim) :
    (proofRules workspace claim).constantType reachName = some reachType := by
  apply combinedType_of_signature (objectRules workspace claim) (declarations workspace)
    (fresh_reach (operators workspace claim))
  simp [declarations, entries, Signature.ofList, Signature.insert, Signature.typeOf?]

private theorem reach_formed {workspace : Workspace} {claim : Claim} {n : Nat}
    {gamma : Tower.Ctx n} {source target : Tower.Tm n}
    (sourceTyped : Typing (proofRules workspace claim) gamma source (.const dataName))
    (targetTyped : Typing (proofRules workspace claim) gamma target (.const dataName)) :
    Typing (proofRules workspace claim) gamma (reach source target) (.head (.sort Tower.zero)) := by
  have constant := Typing.const (Γ := gamma) (reach_lookup workspace claim)
    (reachType_formed workspace claim) (LevelTower.IsUniverse.sort (.succ Tower.zero))
  have first := Typing.appElim constant sourceTyped
  have second := Typing.appElim first targetTyped
  simpa only [reachType, reach, liftClosed, rename, inst0, subst, subst0] using second

private theorem reflType_formed (workspace : Workspace) (claim : Claim) :
    Typing (proofRules workspace claim) .nil reflType (.head (.sort Tower.zero)) := by
  apply pi_zero (data_formed workspace claim .nil)
  exact reach_formed (Typing.var 0) (Typing.var 0)

private theorem transType_formed (workspace : Workspace) (claim : Claim) :
    Typing (proofRules workspace claim) .nil transType (.head (.sort Tower.zero)) := by
  let gamma1 : Tower.Ctx 1 := .snoc .nil (.const dataName)
  let gamma2 : Tower.Ctx 2 := .snoc gamma1 (.const dataName)
  let gamma3 : Tower.Ctx 3 := .snoc gamma2 (.const dataName)
  let gamma4 : Tower.Ctx 4 := .snoc gamma3 (reach (.var 2) (.var 1))
  let gamma5 : Tower.Ctx 5 := .snoc gamma4 (reach (.var 2) (.var 1))
  have first : Typing (proofRules workspace claim) gamma3
      (reach (.var 2) (.var 1)) (.head (.sort Tower.zero)) :=
    reach_formed (Typing.var 2) (Typing.var 1)
  have second : Typing (proofRules workspace claim) gamma4
      (reach (.var 2) (.var 1)) (.head (.sort Tower.zero)) :=
    reach_formed (Typing.var 2) (Typing.var 1)
  have result : Typing (proofRules workspace claim) gamma5
      (reach (.var 4) (.var 2)) (.head (.sort Tower.zero)) :=
    reach_formed (Typing.var 4) (Typing.var 2)
  exact pi_zero (data_formed workspace claim .nil)
    (pi_zero (data_formed workspace claim gamma1)
      (pi_zero (data_formed workspace claim gamma2)
        (pi_zero first (pi_zero second result))))

private theorem joins (workspace : Workspace) (claim : Claim)
    {u v : Tower.Head} (isU : (proofRules workspace claim).isUniverse u)
    (isV : (proofRules workspace claim).isUniverse v) :
    ∃ w, (proofRules workspace claim).isUniverse w ∧
      (proofRules workspace claim).join u v w := by
  cases isU with
  | sort left =>
      cases isV with
      | sort right => exact ⟨.sort (.max left right), .sort _, .sorts _ _⟩

private theorem object_value (workspace : Workspace) (claim : Claim)
    {pattern : Pattern} (member : pattern ∈ patterns workspace claim)
    (formed : pattern.isWellScopedAt workspace.scope = true) :
    Typing (objectRules workspace claim)
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
      (nativeValue workspace.scope pattern formed) (.const dataName) :=
  (supported_judgment (operators workspace claim) (sourceTerm workspace.scope pattern formed)
    (fun _ used => constructors_cover workspace.scope member formed used)).typing

private theorem primitiveType_formed (workspace : Workspace) (claim : Claim)
    (primitive : {p // p ∈ primitives workspace.program}) :
    ∃ level, (proofRules workspace claim).isUniverse level ∧
      Typing (proofRules workspace claim) .nil (primitiveType workspace primitive) (.head level) := by
  have judged := (primitives_exact workspace.program primitive.val).mp primitive.property
  have sourceFormed := Instruction.template_source_scoped workspace.formed
    ((Instruction.template_iff_judges _ _ _ _).mpr judged)
  have targetFormed := judged.target_wellScoped workspace.formed
  have sourceMember : primitive.val.source ∈ patterns workspace claim := by
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨primitive.val, primitive.property, by simp⟩
  have targetMember : primitive.val.target ∈ patterns workspace claim := by
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨primitive.val, primitive.property, by simp⟩
  have sourceTyped := include_object (object_value workspace claim sourceMember sourceFormed)
  have targetTyped := include_object (object_value workspace claim targetMember targetFormed)
  have relation := reach_formed sourceTyped targetTyped
  have context := ((sortRealization (operators workspace claim)).context_formed
    (ctxOf workspace.scope)).includeSignature (declarations workspace)
  exact FormationCheckedTelescopePrograms.close_formed (joins workspace claim) context relation (.sort _)

private theorem fresh_name (inventory : List (PatOp .pat)) (name : DeclName)
    (differentData : name ≠ dataName)
    (differentConstructor : ∀ operator, operatorName operator ≠ name) :
    (rules inventory).constantType name = none := by
  change (signature inventory).typeOf? name = none
  unfold Signature.typeOf?
  cases selected : (signature inventory).entries name with
  | none => rfl
  | some entry =>
      have member := Signature.entries_ofList_mem (declarationList inventory) selected
      rcases List.mem_cons.mp member with same | member
      · exact (differentData (congrArg Prod.fst same)).elim
      · obtain ⟨operator, _, same⟩ := List.mem_map.mp member
        exact (differentConstructor operator (congrArg Prod.fst same)).elim

private theorem fresh_refl (inventory : List (PatOp .pat)) :
    (rules inventory).constantType reflName = none := by
  apply fresh_name inventory reflName (by decide)
  intro operator
  cases operator with
  | fvarOp name => simp [operatorName, reflName]
  | applyOp label arity => simp [operatorName, reflName]
  | lamOp name => cases name <;> simp [operatorName, reflName]
  | multiLamOp arity names => simp [operatorName, reflName]
  | substOp => simp [operatorName, reflName]
  | collOp kind arity rest => cases kind <;> simp [operatorName, reflName]

private theorem fresh_trans (inventory : List (PatOp .pat)) :
    (rules inventory).constantType transName = none := by
  apply fresh_name inventory transName (by decide)
  intro operator
  cases operator with
  | fvarOp name => simp [operatorName, transName]
  | applyOp label arity => simp [operatorName, transName]
  | lamOp name => cases name <;> simp [operatorName, transName]
  | multiLamOp arity names => simp [operatorName, transName]
  | substOp => simp [operatorName, transName]
  | collOp kind arity rest => cases kind <;> simp [operatorName, transName]

private theorem fresh_primitive (inventory : List (PatOp .pat)) (index : Nat) :
    (rules inventory).constantType (primitiveName index) = none := by
  apply fresh_name inventory (primitiveName index) (by intro impossible; cases impossible)
  intro operator
  cases operator with
  | fvarOp name => intro impossible; cases impossible
  | applyOp label arity => intro impossible; cases impossible
  | lamOp name => cases name <;> intro impossible <;> cases impossible
  | multiLamOp arity names => intro impossible; cases impossible
  | substOp => intro impossible; cases impossible
  | collOp kind arity rest => cases kind <;> intro impossible <;> cases impossible

private theorem refl_lookup (workspace : Workspace) (claim : Claim) :
    (proofRules workspace claim).constantType reflName = some reflType := by
  apply combinedType_of_signature (objectRules workspace claim) (declarations workspace)
    (fresh_refl (operators workspace claim))
  simp [declarations, entries, Signature.ofList, Signature.insert, Signature.typeOf?, reflName, reachName]

private theorem trans_lookup (workspace : Workspace) (claim : Claim) :
    (proofRules workspace claim).constantType transName = some transType := by
  apply combinedType_of_signature (objectRules workspace claim) (declarations workspace)
    (fresh_trans (operators workspace claim))
  simp [declarations, entries, Signature.ofList, Signature.insert, Signature.typeOf?,
    transName, reflName, reachName]

private theorem primitive_lookup (workspace : Workspace) (claim : Claim)
    (index : Fin (primitives workspace.program).length) :
    (proofRules workspace claim).constantType (primitiveName index.val) =
      some (primitiveType workspace (primitiveAt workspace index)) := by
  apply combinedType_of_signature (objectRules workspace claim) (declarations workspace)
    (fresh_primitive (operators workspace claim) index.val)
  have known := Signature.entries_ofFn (fun i : Fin (primitives workspace.program).length => primitiveName i.val)
    (fun i => ⟨primitiveType workspace (primitiveAt workspace i), none⟩)
    (fun first second same => Fin.ext (primitiveName_injective same)) index
  simpa [declarations, entries, Signature.ofList, Signature.insert, Signature.typeOf?,
    primitiveName, reachName, reflName, transName] using congrArg (Option.map Entry.type) known

private theorem entries_typed (workspace : Workspace) (claim : Claim)
    {name : DeclName} {entry : Entry Tower.Head}
    (member : (name, entry) ∈ entries workspace) :
    ∃ level, (proofRules workspace claim).isUniverse level ∧
      Typing (proofRules workspace claim) .nil entry.type (.head level) := by
  rcases List.mem_append.mp member with first | primitive
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at first
    rcases first with same | same | same
    · cases same
      exact ⟨.sort (.succ Tower.zero), .sort _, reachType_formed workspace claim⟩
    · cases same
      exact ⟨.sort Tower.zero, .sort _, reflType_formed workspace claim⟩
    · cases same
      exact ⟨.sort Tower.zero, .sort _, transType_formed workspace claim⟩
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp primitive
    cases same
    exact primitiveType_formed workspace claim (primitiveAt workspace index)

private theorem entries_fresh (workspace : Workspace) (claim : Claim)
    {name : DeclName} {entry : Entry Tower.Head}
    (member : (name, entry) ∈ entries workspace) :
    (objectRules workspace claim).constantType name = none := by
  rcases List.mem_append.mp member with first | primitive
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at first
    rcases first with same | same | same
    · cases same; exact fresh_reach (operators workspace claim)
    · cases same; exact fresh_refl (operators workspace claim)
    · cases same; exact fresh_trans (operators workspace claim)
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp primitive
    cases same
    exact fresh_primitive (operators workspace claim) index.val

private theorem entries_opaque (workspace : Workspace)
    {name : DeclName} {entry : Entry Tower.Head}
    (member : (name, entry) ∈ entries workspace) : entry.value? = none := by
  rcases List.mem_append.mp member with first | primitive
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at first
    rcases first with same | same | same <;> cases same <;> rfl
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp primitive
    cases same
    rfl

private theorem valueOf_none (workspace : Workspace) (name : DeclName) :
    (declarations workspace).valueOf? name = none := by
  cases selected : (declarations workspace).entries name with
  | none => simp [Signature.valueOf?, selected]
  | some entry =>
      have member := Signature.entries_ofList_mem (entries workspace) selected
      simp [Signature.valueOf?, selected, entries_opaque workspace member]

theorem wellFormed (workspace : Workspace) (claim : Claim) :
    (declarations workspace).WellFormed (objectRules workspace claim) where
  fresh := fun selected => entries_fresh workspace claim
    (Signature.entries_ofList_mem (entries workspace) selected)
  types := by
    intro name type known
    unfold Signature.typeOf? at known
    cases selected : (declarations workspace).entries name with
    | none => simp [selected] at known
    | some entry =>
        have same : entry.type = type := by simpa [selected] using known
        obtain ⟨level, isUniverse, typed⟩ := entries_typed workspace claim
          (Signature.entries_ofList_mem (entries workspace) selected)
        exact ⟨level, isUniverse, same ▸ typed.toRaw⟩
  values := by
    intro name type value _known impossible
    rw [valueOf_none] at impossible
    cases impossible
  noSelfDelta := by
    intro name value impossible
    rw [valueOf_none] at impossible
    cases impossible
  declaredPreserves := by
    intro n gamma left right type impossible _typed
    rw [declarations, Signature.computation_ofList] at impossible
    exact impossible.elim

def reflexivity {n : Nat} (source : Tower.Tm n) : Tower.Tm n :=
  .app (.const reflName) source

def composition {n : Nat} (source middle target first second : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app (.const transName) source) middle) target) first) second

private theorem reflexivity_typed {workspace : Workspace} {claim : Claim} {n : Nat}
    {gamma : Tower.Ctx n} {source : Tower.Tm n}
    (typed : Typing (proofRules workspace claim) gamma source (.const dataName)) :
    Typing (proofRules workspace claim) gamma (reflexivity source) (reach source source) := by
  have constant := Typing.const (Γ := gamma) (refl_lookup workspace claim)
    (reflType_formed workspace claim) (LevelTower.IsUniverse.sort Tower.zero)
  have applied := Typing.appElim constant typed
  simpa only [reflexivity, reflType, reach, liftClosed, rename, inst0, subst, subst0,
    liftRen, Fin.cases_zero] using applied

private theorem composition_typed {workspace : Workspace} {claim : Claim} {n : Nat}
    {gamma : Tower.Ctx n} {source middle target first second : Tower.Tm n}
    (sourceTyped : Typing (proofRules workspace claim) gamma source (.const dataName))
    (middleTyped : Typing (proofRules workspace claim) gamma middle (.const dataName))
    (targetTyped : Typing (proofRules workspace claim) gamma target (.const dataName))
    (firstTyped : Typing (proofRules workspace claim) gamma first (reach source middle))
    (secondTyped : Typing (proofRules workspace claim) gamma second (reach middle target)) :
    Typing (proofRules workspace claim) gamma
      (composition source middle target first second) (reach source target) := by
  have constant := Typing.const (Γ := gamma) (trans_lookup workspace claim)
    (transType_formed workspace claim) (LevelTower.IsUniverse.sort Tower.zero)
  let objectContext : Tower.Ctx 3 :=
    .snoc (.snoc (.snoc .nil (.const dataName)) (.const dataName)) (.const dataName)
  let body : Tower.Tm 3 :=
    .pi (reach (.var 2) (.var 1))
      (.pi (reach (.var 2) (.var 1)) (reach (.var 4) (.var 2)))
  change Typing _ _ _ (liftClosed (closeType objectContext body)) at constant
  have empty : FormationSensitive.CtxMor (proofRules workspace claim)
      (.nil : Tower.Ctx 0) gamma (Fin.elim0 : Sub Tower.Head 0 n) :=
    fun position => Fin.elim0 position
  have firstObject := empty.extend (type := .const dataName) sourceTyped
  have secondObject := firstObject.extend (type := .const dataName) middleTyped
  have thirdObject := secondObject.extend (type := .const dataName) targetTyped
  have instantiated := FormationCheckedTelescopePrograms.apply_typed thirdObject constant
  have normalized :
      subst (consSub target (consSub middle (consSub source Fin.elim0))) body =
        .pi (reach source middle)
          (.pi (rename wk (reach middle target))
            (rename wk (rename wk (reach source target)))) := by rfl
  rw [normalized] at instantiated
  have one := Typing.appElim instantiated firstTyped
  have cancel :
      inst0 first (.pi (rename wk (reach middle target))
        (rename wk (rename wk (reach source target)))) =
      .pi (reach middle target) (rename wk (reach source target)) := by
    simp only [inst0, subst, subst_liftSub_wk]
    change Tm.pi (inst0 first (rename wk (reach middle target)))
      (rename wk (inst0 first (rename wk (reach source target)))) =
      Tm.pi (reach middle target) (rename wk (reach source target))
    rw [inst0_rename_wk, inst0_rename_wk]
  rw [cancel] at one
  have two := Typing.appElim one secondTyped
  rw [inst0_rename_wk] at two
  simpa only [composition, applyClosed, objectContext, consSub_zero, consSub_succ] using two

def applyPrimitive (workspace : Workspace)
    (index : Fin (primitives workspace.program).length) :
    Tower.Tm (ctxOf workspace.scope).length :=
  applyClosed (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) ids
    (.const (primitiveName index.val))

private theorem applyPrimitive_typed (workspace : Workspace) (claim : Claim)
    (index : Fin (primitives workspace.program).length) :
    Typing (proofRules workspace claim)
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
      (applyPrimitive workspace index)
      (reach
        (nativeValue workspace.scope (primitiveAt workspace index).val.source
          (Instruction.template_source_scoped workspace.formed
            ((Instruction.template_iff_judges _ _ _ _).mpr
              ((primitives_exact _ _).mp (primitiveAt workspace index).property))))
        (nativeValue workspace.scope (primitiveAt workspace index).val.target
          (((primitives_exact _ _).mp (primitiveAt workspace index).property).target_wellScoped
            workspace.formed))) := by
  obtain ⟨level, isUniverse, formed⟩ :=
    primitiveType_formed workspace claim (primitiveAt workspace index)
  have constant := Typing.const (Γ := BindingSignatureEmbedding.context names (ctxOf workspace.scope))
    (primitive_lookup workspace claim index) formed isUniverse
  have identity : FormationSensitive.CtxMor (proofRules workspace claim)
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) ids := by
    intro position
    simpa only [ids, subst_ids] using
      (Typing.var (R := proofRules workspace claim)
        (Γ := BindingSignatureEmbedding.context names (ctxOf workspace.scope)) position)
  have applied := FormationCheckedTelescopePrograms.apply_typed identity constant
  simpa only [primitiveType, applyPrimitive, subst_ids] using applied

def findPrimitive (program : Program) (primitive : Primitive) :
    Option (Fin (primitives program).length) :=
  (primitives program).findFinIdx? (fun candidate => decide (candidate = primitive))

theorem findPrimitive_sound {program : Program} {primitive : Primitive}
    {index : Fin (primitives program).length}
    (found : findPrimitive program primitive = some index) :
    (primitives program).get index = primitive :=
  of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp found).1

theorem findPrimitive_complete {program : Program} {primitive : Primitive}
    (judged : Instruction.Judges program primitive.instruction primitive.source primitive.target) :
    ∃ index, findPrimitive program primitive = some index := by
  have member := (primitives_exact program primitive).mpr judged
  have present : (findPrimitive program primitive).isSome = true := by
    rw [findPrimitive, List.isSome_findFinIdx?, List.any_eq_true]
    exact ⟨primitive, member, by simp⟩
  exact Option.isSome_iff_exists.mp present

private theorem source_member (workspace : Workspace) (claim : Claim) :
    claim.source ∈ patterns workspace claim :=
  List.mem_append_left _ (List.mem_append_right _ (by simp))

private theorem target_member (workspace : Workspace) (claim : Claim) :
    claim.target ∈ patterns workspace claim :=
  List.mem_append_left _ (List.mem_append_right _ (by simp))

private theorem primitive_target_member (workspace : Workspace) (claim : Claim)
    {primitive : Primitive}
    (judged : Instruction.Judges workspace.program primitive.instruction primitive.source primitive.target) :
    primitive.target ∈ patterns workspace claim :=
  List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨primitive, (primitives_exact _ _).mpr judged, by simp⟩)

/-- Compile a checked finite script by the actual selected commands and finite
primitive-declaration lookup. Scope proofs are generated by source admission
and the selected commands, not supplied inside the raw script. -/
def compileFrom (workspace : Workspace) (claim : Claim) :
    List Instruction → (source : Pattern) →
      source.isWellScopedAt workspace.scope = true →
      claim.target.isWellScopedAt workspace.scope = true →
      Option (Tower.Tm (ctxOf workspace.scope).length)
  | [], source, sourceFormed, _targetFormed =>
      if source = claim.target then some (reflexivity (nativeValue workspace.scope source sourceFormed))
      else none
  | instruction :: rest, source, sourceFormed, targetFormed =>
      match executed : Instruction.execute workspace.program instruction source with
      | none => none
      | some middle =>
          match findPrimitive workspace.program ⟨instruction, source, middle⟩ with
          | none => none
          | some index =>
              let middleFormed :=
                ((Instruction.execute_iff_judges workspace.program instruction source middle).mp executed).target_wellScoped
                  workspace.formed
              (compileFrom workspace claim rest middle middleFormed targetFormed).map fun later =>
                composition (nativeValue workspace.scope source sourceFormed)
                  (nativeValue workspace.scope middle middleFormed)
                  (nativeValue workspace.scope claim.target targetFormed)
                  (applyPrimitive workspace index) later

/-- The raw boundary performs both endpoint scope checks before compilation. -/
def compile (workspace : Workspace) (claim : Claim) (script : List Instruction) :
    Option (Tower.Tm (ctxOf workspace.scope).length) :=
  if formed : claim.source.isWellScopedAt workspace.scope = true ∧
      claim.target.isWellScopedAt workspace.scope = true then
    compileFrom workspace claim script claim.source formed.1 formed.2
  else none

theorem compileFrom_sound (workspace : Workspace) (claim : Claim) :
    ∀ (script : List Instruction) (source : Pattern)
      (sourceFormed : source.isWellScopedAt workspace.scope = true)
      (targetFormed : claim.target.isWellScopedAt workspace.scope = true)
      (_member : source ∈ patterns workspace claim)
      (native : Tower.Tm (ctxOf workspace.scope).length),
      compileFrom workspace claim script source sourceFormed targetFormed = some native →
      ScriptJudges workspace.program script source claim.target ∧
        Typing (proofRules workspace claim)
          (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) native
          (reach (nativeValue workspace.scope source sourceFormed)
            (nativeValue workspace.scope claim.target targetFormed)) := by
  intro script
  induction script with
  | nil =>
      intro source sourceFormed targetFormed member native accepted
      simp only [compileFrom] at accepted
      split at accepted
      · next same =>
          have nativeSame := Option.some.inj accepted
          subst native
          subst source
          exact ⟨.nil _, reflexivity_typed (include_object
            (object_value workspace claim member sourceFormed))⟩
      · cases accepted
  | cons instruction rest inductionHypothesis =>
      intro source sourceFormed targetFormed member native accepted
      simp only [compileFrom] at accepted
      split at accepted
      · cases accepted
      · next middle executed =>
          split at accepted
          · cases accepted
          · next index found =>
              obtain ⟨later, tailCompiled, sameNative⟩ := Option.map_eq_some_iff.mp accepted
              have head := (Instruction.execute_iff_judges workspace.program instruction source middle).mp executed
              have middleFormed := head.target_wellScoped workspace.formed
              have middleMember := primitive_target_member workspace claim (primitive := ⟨instruction, source, middle⟩) head
              obtain ⟨tailJudged, tailTyped⟩ := inductionHypothesis middle middleFormed targetFormed
                middleMember later tailCompiled
              have primitiveTyped := applyPrimitive_typed workspace claim index
              have primitiveSame := findPrimitive_sound found
              change (primitiveAt workspace index).val = _ at primitiveSame
              have headTyped : Typing (proofRules workspace claim)
                  (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
                  (applyPrimitive workspace index)
                  (reach (nativeValue workspace.scope source sourceFormed)
                    (nativeValue workspace.scope middle middleFormed)) := by
                simpa only [primitiveSame] using primitiveTyped
              have typed := composition_typed
                (include_object (object_value workspace claim member sourceFormed))
                (include_object (object_value workspace claim middleMember middleFormed))
                (include_object (object_value workspace claim (target_member workspace claim) targetFormed))
                headTyped tailTyped
              exact ⟨.cons head tailJudged, sameNative ▸ typed⟩

theorem compileFrom_complete (workspace : Workspace) (claim : Claim) :
    ∀ (script : List Instruction) (source : Pattern)
      (sourceFormed : source.isWellScopedAt workspace.scope = true)
      (targetFormed : claim.target.isWellScopedAt workspace.scope = true),
      ScriptJudges workspace.program script source claim.target →
      ∃ native, compileFrom workspace claim script source sourceFormed targetFormed = some native := by
  intro script
  induction script with
  | nil =>
      intro source sourceFormed targetFormed judged
      cases judged
      exact ⟨reflexivity (nativeValue workspace.scope claim.target sourceFormed),
        by simp only [compileFrom, ite_true]⟩
  | cons instruction rest inductionHypothesis =>
      intro source sourceFormed targetFormed judged
      cases judged with
      | cons head tail =>
          rename_i middle
          have executed := (Instruction.execute_iff_judges workspace.program instruction _ _).mpr head
          obtain ⟨index, found⟩ := findPrimitive_complete (primitive := ⟨instruction, _, _⟩) head
          obtain ⟨later, compiled⟩ := inductionHypothesis _ (head.target_wellScoped workspace.formed)
            targetFormed tail
          refine ⟨composition (nativeValue workspace.scope source sourceFormed)
            (nativeValue workspace.scope middle (head.target_wellScoped workspace.formed))
            (nativeValue workspace.scope claim.target targetFormed)
            (applyPrimitive workspace index) later, ?_⟩
          rw [compileFrom]
          split
          · next refused => rw [executed] at refused; cases refused
          · next nextValue observed =>
              have same : nextValue = middle := Option.some.inj (observed.symm.trans executed)
              subst nextValue
              simp only [found, compiled, Option.map_some]

theorem compile_sound (workspace : Workspace) (claim : Claim)
    (script : List Instruction) (native : Tower.Tm (ctxOf workspace.scope).length)
    (accepted : compile workspace claim script = some native) :
    ∃ (sourceFormed : claim.source.isWellScopedAt workspace.scope = true)
      (targetFormed : claim.target.isWellScopedAt workspace.scope = true),
      ScriptJudges workspace.program script claim.source claim.target ∧
        Judgment (proofRules workspace claim)
          (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) native
          (reach (nativeValue workspace.scope claim.source sourceFormed)
            (nativeValue workspace.scope claim.target targetFormed)) := by
  unfold compile at accepted
  split at accepted
  · next formed =>
      obtain ⟨judged, typed⟩ := compileFrom_sound workspace claim script claim.source
        formed.1 formed.2 (source_member workspace claim) native accepted
      exact ⟨formed.1, formed.2, judged,
        ⟨((sortRealization (operators workspace claim)).context_formed (ctxOf workspace.scope)).includeSignature
          (declarations workspace), typed⟩⟩
  · cases accepted

theorem compile_complete (workspace : Workspace) (claim : Claim)
    (script : List Instruction) (admitted : (proofSystem workspace).Judges script claim) :
    ∃ native, compile workspace claim script = some native := by
  rcases admitted with ⟨sourceFormed, targetFormed, judged⟩
  obtain ⟨native, accepted⟩ := compileFrom_complete workspace claim script claim.source
    sourceFormed targetFormed judged
  refine ⟨native, ?_⟩
  simp only [compile, sourceFormed, targetFormed, and_self, dite_true, accepted]

theorem compile_exists_iff (workspace : Workspace) (claim : Claim) (script : List Instruction) :
    (∃ native, compile workspace claim script = some native) ↔
      (proofSystem workspace).Judges script claim := by
  constructor
  · rintro ⟨native, compiled⟩
    obtain ⟨sourceFormed, targetFormed, judged, _typed⟩ := compile_sound workspace claim script native compiled
    exact ⟨sourceFormed, targetFormed, judged⟩
  · exact compile_complete workspace claim script

/-- The packet contains raw source instruction data and an actual native term,
not a producer-supplied typing proof or semantic oracle. -/
structure Certificate (workspace : Workspace) where
  script : List Instruction
  native : Tower.Tm (ctxOf workspace.scope).length

def check (workspace : Workspace) (claim : Claim) (certificate : Certificate workspace) : Bool :=
  decide (compile workspace claim certificate.script = some certificate.native)

/-- This checks the compiler image. Its source authority is the original
independent script judgment; arbitrary ambient native proof terms are not
claimed to be accepted by this interface. -/
def imageProofSystem (workspace : Workspace) :
    Mettapedia.GSLT.LanguageDef.SemanticEvidence.NativeProofSystem Claim where
  ProofObject := Certificate workspace
  Judges certificate claim :=
    (proofSystem workspace).Judges certificate.script claim ∧
      compile workspace claim certificate.script = some certificate.native

def imageKernel (workspace : Workspace) :
    Mettapedia.GSLT.LanguageDef.SemanticEvidence.NativeProofKernel (imageProofSystem workspace) where
  decide claim certificate := check workspace claim certificate
  correct claim certificate := by
    change decide (_ = _) = true ↔ _ ∧ _
    rw [decide_eq_true_eq]
    constructor
    · intro compiled
      exact ⟨(compile_exists_iff workspace claim certificate.script).mp ⟨certificate.native, compiled⟩,
        compiled⟩
    · exact And.right

theorem image_meaning_exact (workspace : Workspace) (claim : Claim) :
    (Mettapedia.GSLT.LanguageDef.GSLTIL.NativeCommand.target workspace).Meaning claim ↔
      Nonempty ((imageProofSystem workspace).ProofFibre claim) := by
  constructor
  · intro meaning
    obtain ⟨⟨script, admitted⟩⟩ := (meaning_exact workspace claim).mp meaning
    obtain ⟨native, compiled⟩ := compile_complete workspace claim script admitted
    exact ⟨⟨⟨script, native⟩, admitted, compiled⟩⟩
  · rintro ⟨⟨certificate, admitted, _compiled⟩⟩
    exact (meaning_exact workspace claim).mpr ⟨⟨certificate.script, admitted⟩⟩

def proofService (workspace : Workspace) :
    Mettapedia.GSLT.LanguageDef.SemanticService.Service (Mettapedia.GSLT.LanguageDef.GSLTIL.NativeCommand.target workspace) :=
  .nativeProof (imageProofSystem workspace) (imageKernel workspace) (image_meaning_exact workspace)

theorem accepted_iff_source_runs (workspace : Workspace) (claim : Claim) :
    (∃ certificate, check workspace claim certificate = true) ↔
      (Mettapedia.GSLT.LanguageDef.GSLTIL.NativeCommand.target workspace).Meaning claim := by
  constructor
  · rintro ⟨certificate, accepted⟩
    have compiled : compile workspace claim certificate.script = some certificate.native :=
      of_decide_eq_true accepted
    obtain ⟨sourceFormed, targetFormed, judged, _typing⟩ :=
      compile_sound workspace claim certificate.script certificate.native compiled
    exact ⟨sourceFormed, targetFormed,
      (script_exists_iff_runs workspace.program _ _).mp ⟨certificate.script, judged⟩⟩
  · intro meaning
    obtain ⟨⟨⟨script, native⟩, _admitted, compiled⟩⟩ := (image_meaning_exact workspace claim).mp meaning
    exact ⟨⟨script, native⟩, decide_eq_true compiled⟩

/-- Native substitution acts on the emitted proof itself at its indexed
proof family. The context morphism is the existing actual typing judgment. -/
theorem accepted_native_substitution (workspace : Workspace) (claim : Claim)
    (certificate : Certificate workspace) (accepted : check workspace claim certificate = true)
    {n : Nat} {gamma : Tower.Ctx n}
    (contextFormed : ContextFormation (proofRules workspace claim) gamma)
    (action : Sub Tower.Head (ctxOf workspace.scope).length n)
    (typed : FormationSensitive.CtxMor (proofRules workspace claim)
      (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) gamma action) :
    ∃ (sourceFormed : claim.source.isWellScopedAt workspace.scope = true)
      (targetFormed : claim.target.isWellScopedAt workspace.scope = true),
      Judgment (proofRules workspace claim) gamma (subst action certificate.native)
        (reach (subst action (nativeValue workspace.scope claim.source sourceFormed))
          (subst action (nativeValue workspace.scope claim.target targetFormed))) := by
  obtain ⟨sourceFormed, targetFormed, _judged, admitted⟩ := compile_sound workspace claim
    certificate.script certificate.native (of_decide_eq_true accepted)
  exact ⟨sourceFormed, targetFormed, contextFormed, admitted.typing.substitute typed⟩

/-- A scope-correct source assignment retains the same instruction script.
The new declaration package and native proof are actually recompiled; this
does not identify the two ambient native theories or their raw proof terms. -/
theorem accepted_source_reindex (workspace : Workspace) (destination : Nat)
    (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (images : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.WellScopedAssignment
      workspace.scope destination assignment)
    (claim : Claim) (certificate : Certificate workspace)
    (accepted : check workspace claim certificate = true) :
    ∃ native, compile (reindex workspace destination assignment images)
      (claim.reindex assignment) certificate.script = some native := by
  have admitted := (compile_exists_iff workspace claim certificate.script).mp
    ⟨certificate.native, of_decide_eq_true accepted⟩
  have oldAccepted := (kernel workspace).correct claim certificate.script |>.mpr admitted
  have nextAccepted := kernel_reindex_preserves workspace destination assignment images
    claim certificate.script oldAccepted
  exact compile_complete _ _ certificate.script
    ((kernel _).correct _ _ |>.mp nextAccepted)

/-- Read the declaration head of an application spine. Arguments are retained
in the proof term and checked by compilation; this projection is only a
receipt observer on that term. -/
def headConstant {n : Nat} : Tower.Tm n → Option DeclName
  | .const name => some name
  | .app function _ => headConstant function
  | _ => none

private theorem headConstant_applyClosed {n m : Nat} (context : Tower.Ctx n)
    (action : Sub Tower.Head n m) (function : Tower.Tm m) :
    headConstant (applyClosed context action function) = headConstant function := by
  induction context with
  | nil => rfl
  | snoc prior domain inductionHypothesis =>
      exact inductionHypothesis (fun index => action index.succ)

def readInstruction (workspace : Workspace) {n : Nat} (native : Tower.Tm n) : Option Instruction :=
  (headConstant native).bind fun name =>
    match name with
    | .num base index =>
        if base = `GSLT.Command.Primitive then
          ((primitives workspace.program)[index]?).map Primitive.instruction
        else none
    | _ => none

@[simp] theorem readInstruction_applyPrimitive (workspace : Workspace)
    (index : Fin (primitives workspace.program).length) :
    readInstruction workspace (applyPrimitive workspace index) =
      some (primitiveAt workspace index).val.instruction := by
  simp [readInstruction, applyPrimitive, headConstant_applyClosed, headConstant,
    primitiveName, primitiveAt]

/-- Decode the original instruction occurrences from the concrete native
composition grammar. This projection does not admit arbitrary native terms. -/
def readInstructions (workspace : Workspace) {n : Nat} (native : Tower.Tm n) : Option (List Instruction) :=
  match native with
  | .app (.const name) _ => if name = reflName then some [] else none
  | .app (.app (.app (.app (.app (.const name) _) _) _) first) later =>
      if name = transName then
        (readInstruction workspace first).bind fun instruction =>
          (readInstructions workspace later).map (instruction :: ·)
      else none
  | _ => none
termination_by structural native

@[simp] theorem readInstructions_reflexivity (workspace : Workspace) {n : Nat} (source : Tower.Tm n) :
    readInstructions workspace (reflexivity source) = some [] := by
  simp [readInstructions, reflexivity]

@[simp] theorem readInstructions_composition (workspace : Workspace) {n : Nat}
    (source middle target first later : Tower.Tm n) :
    readInstructions workspace (composition source middle target first later) =
      (readInstruction workspace first).bind fun instruction =>
        (readInstructions workspace later).map (instruction :: ·) := by
  simp [readInstructions, composition]

theorem compileFrom_readback (workspace : Workspace) (claim : Claim) :
    ∀ (script : List Instruction) (source : Pattern)
      (sourceFormed : source.isWellScopedAt workspace.scope = true)
      (targetFormed : claim.target.isWellScopedAt workspace.scope = true)
      (native : Tower.Tm (ctxOf workspace.scope).length),
      compileFrom workspace claim script source sourceFormed targetFormed = some native →
      readInstructions workspace native = some script := by
  intro script
  induction script with
  | nil =>
      intro source sourceFormed targetFormed native compiled
      simp only [compileFrom] at compiled
      split at compiled
      · have same := Option.some.inj compiled
        subst native
        exact readInstructions_reflexivity workspace _
      · cases compiled
  | cons instruction rest inductionHypothesis =>
      intro source sourceFormed targetFormed native compiled
      simp only [compileFrom] at compiled
      split at compiled
      · cases compiled
      · next middle _executed =>
          split at compiled
          · cases compiled
          · next index found =>
              obtain ⟨later, tailCompiled, same⟩ := Option.map_eq_some_iff.mp compiled
              subst native
              have readLater := inductionHypothesis middle _ targetFormed later tailCompiled
              have row := findPrimitive_sound found
              have readFirst := readInstruction_applyPrimitive workspace index
              change readInstruction workspace (applyPrimitive workspace index) =
                some ((primitives workspace.program).get index).instruction at readFirst
              rw [row] at readFirst
              simp only [readInstructions_composition, readFirst, Option.bind_some,
                readLater, Option.map_some]

/-- Literal compiled proofs retain the entire submitted occurrence script,
including repetitions. Value sharing cannot erase a source occurrence. -/
theorem compile_readback (workspace : Workspace) (claim : Claim) (script : List Instruction)
    (native : Tower.Tm (ctxOf workspace.scope).length)
    (compiled : compile workspace claim script = some native) :
    readInstructions workspace native = some script := by
  unfold compile at compiled
  split at compiled
  · exact compileFrom_readback workspace claim script claim.source _ _ native compiled
  · cases compiled

theorem literal_proof_preserves_script (workspace : Workspace) (claim : Claim)
    (first second : List Instruction) (native : Tower.Tm (ctxOf workspace.scope).length)
    (firstCompiled : compile workspace claim first = some native)
    (secondCompiled : compile workspace claim second = some native) : first = second := by
  exact Option.some.inj ((compile_readback workspace claim first native firstCompiled).symm.trans
    (compile_readback workspace claim second native secondCompiled))

/-- Closing the actual ambient object context gives a single closed native
proof program at the corresponding closed dependent type. -/
theorem accepted_closed_proof (workspace : Workspace) (claim : Claim)
    (certificate : Certificate workspace) (accepted : check workspace claim certificate = true) :
    ∃ (sourceFormed : claim.source.isWellScopedAt workspace.scope = true)
      (targetFormed : claim.target.isWellScopedAt workspace.scope = true),
      Judgment (proofRules workspace claim) .nil
        (closeTerm (BindingSignatureEmbedding.context names (ctxOf workspace.scope)) certificate.native)
        (closeType (BindingSignatureEmbedding.context names (ctxOf workspace.scope))
          (reach (nativeValue workspace.scope claim.source sourceFormed)
            (nativeValue workspace.scope claim.target targetFormed))) := by
  obtain ⟨sourceFormed, targetFormed, _judged, admitted⟩ := compile_sound workspace claim
    certificate.script certificate.native (of_decide_eq_true accepted)
  have universes : UniverseRegularity (proofRules workspace claim) :=
    (towerUniverseRegularity.includeSignature (signature (operators workspace claim))).includeSignature
      (declarations workspace)
  exact ⟨sourceFormed, targetFormed, .nil,
    FormationCheckedTelescopePrograms.close_typed universes (joins workspace claim)
      admitted.context admitted.typing⟩

end Proof

end FiniteCatalogInterpretation

#print axioms quotePresentation_hasType
#print axioms quotePresentation_roundtrip
#print axioms TypedRouteValue.representedAsGraph
#print axioms unitRoute_executes
#print axioms unitRoute_compiles_to_identity
#print axioms duplicateRoute_not_licensed

end FirstClassGSLT

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation BindingSignatureEmbedding
open AuthoredTypeExpressions
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- The native function type follows the original newest-first binding
context, using actual arrow types of the declared source sort. -/
def functionSort : List (DeclaredSort language) → DeclaredSort language → DeclaredSort language
  | [], result => result
  | domain :: rest, result => functionSort rest (DeclaredSort.arrow domain result)

theorem functionSort_native (dependencies : List (DeclaredSort language)) (result : DeclaredSort language) :
    nativeType (functionSort dependencies result) =
      ClosedOperators.spineType (S := sourceSignature language) nativeType dependencies (nativeType result) := by
  induction dependencies generalizing result with
  | nil => rfl
  | cons domain rest ih =>
      simpa only [functionSort, ClosedOperators.spineType, nativeType_arrow] using ih (DeclaredSort.arrow domain result)

def nativeParameterSorts (metadata : Metadata language rule spec)
    (ambient : List (DeclaredSort language)) : List (DeclaredSort language) :=
  metadata.entries.map fun entry => functionSort (language := language) (List.append entry.1 ambient) entry.2

def nativeParameterIndex (metadata : Metadata language rule spec)
    (ambient : List (DeclaredSort language)) (index : Fin metadata.entries.length) :
    Fin (nativeParameterSorts metadata ambient).length :=
  ⟨index.val, by simpa only [nativeParameterSorts, List.length_map] using index.isLt⟩

def nativeParameterContext (metadata : Metadata language rule spec)
    (ambient : List (DeclaredSort language)) :=
  ClosedOperators.typeContext (S := sourceSignature language) nativeType (nativeParameterSorts metadata ambient)

theorem nativeParameterLookup (metadata : Metadata language rule spec)
    (ambient : List (DeclaredSort language)) (index : Fin metadata.entries.length) :
    Presentation.Ctx.lookup (nativeParameterContext metadata ambient) (nativeParameterIndex metadata ambient index) =
      Presentation.liftClosed (ClosedOperators.spineType (S := sourceSignature language) nativeType
        ((metadata.entries.get index).1 ++ ambient) (nativeType (metadata.entries.get index).2)) := by
  have known := ClosedOperators.Formation.typeContext_lookup
    (S := sourceSignature language) (Head := Tower.Head) nativeType
    (varOfIdx (S := sourceSignature language) (nativeParameterSorts metadata ambient) (nativeParameterIndex metadata ambient index))
  rw [varIdx_varOfIdx (S := sourceSignature language) (nativeParameterSorts metadata ambient)
    (nativeParameterIndex metadata ambient index)] at known
  have selected : (nativeParameterSorts metadata ambient).get (nativeParameterIndex metadata ambient index) =
      functionSort (language := language) (List.append (metadata.entries.get index).1 ambient) (metadata.entries.get index).2 :=
    List.getElem_map (fun (entry : MetaArity (sourceSignature language)) =>
      functionSort (language := language) (List.append entry.1 ambient) entry.2) (l := metadata.entries) (i := index.val)
  apply known.trans
  apply (congrArg (fun sort : DeclaredSort language => Presentation.liftClosed (nativeType sort)) selected).trans
  exact congrArg Presentation.liftClosed (functionSort_native _ _)

theorem nativeParameterContextFormed (metadata : Metadata language rule spec)
    (installed : FullHeaders.Installation language) (ambient : List (DeclaredSort language)) :
    FormationSensitive.ContextFormation installed.rules (nativeParameterContext metadata ambient) :=
  (FullHeaders.Operational.realization installed).toFormation.typeContext_formed _

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored
open Mettapedia.OSLF
open Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Declaration BindingSignatureEmbedding TelescopeAbstraction FormationSensitive
open AuthoredTypeExpressions
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata
namespace NativeTemplate
open Declarations.BindingSignaturePackage
open SchemaTemplates
variable {language : LanguageDef} {M : List (MetaArity (sourceSignature language))}
variable {source : List (DeclaredSort language)} {sort : DeclaredSort language}

def names (scope : DeclName) (language : LanguageDef) : Names (sourceSignature language) where
  sort := fun selected => BindingSyntax.Wire.sortName scope selected.val
  operator := fun operator => BindingSyntax.Wire.operatorName scope language operator.original

theorem names_injective (scope : DeclName) (language : LanguageDef) :
    Function.Injective (declarationName (names scope language)) := by
  intro first second same
  cases first with
  | inl firstSort =>
      cases second with
      | inl secondSort =>
          exact congrArg Sum.inl (Subtype.ext (BindingSyntax.Wire.sortName_injective scope same))
      | inr secondOperator =>
          exact False.elim (BindingSyntax.Wire.sortName_ne_operatorName scope language firstSort.val secondOperator.2.original same)
  | inr firstOperator =>
      cases second with
      | inl secondSort =>
          exact False.elim (BindingSyntax.Wire.sortName_ne_operatorName scope language secondSort.val firstOperator.2.original same.symm)
      | inr secondOperator =>
          rcases firstOperator with ⟨firstSort, firstOperator⟩
          rcases secondOperator with ⟨secondSort, secondOperator⟩
          have decoded := congrArg (BindingSyntax.Wire.readOperatorName scope language) same
          simp only [declarationName, names, BindingSyntax.Wire.readOperatorName_operatorName] at decoded
          have resultSame : firstSort.val = secondSort.val := congrArg Sigma.fst (Option.some.inj decoded)
          have sortSame : firstSort = secondSort := Subtype.ext resultSame
          subst secondSort
          have originalSame : firstOperator.original = secondOperator.original :=
            eq_of_heq (Sigma.mk.inj (Option.some.inj decoded)).2
          exact congrArg (fun operator => Sum.inr (Sigma.mk firstSort operator))
            (ReindexedOperator.original_injective Subtype.val_injective originalSame)

def parameterNamespace (scope : DeclName) : DeclName := .str scope "metavariable"

theorem names_unselected (scope : DeclName) (language : LanguageDef)
    (symbol : Symbol (sourceSignature language)) :
    FiniteParameters.indexedPositions (parameterNamespace scope) M.length
      (declarationName (names scope language) symbol) = none := by
  cases symbol <;> rfl

def parameterSorts (term : Term (withMetas (sourceSignature language) M) source sort) :
    List (DeclaredSort language) :=
  (selected term).map fun index => functionSort (language := language) (M.get index).1 (M.get index).2

def callerSorts (term : Term (withMetas (sourceSignature language) M) source sort) :
    List (DeclaredSort language) := source ++ parameterSorts term

def caller (term : Term (withMetas (sourceSignature language) M) source sort) :=
  ClosedOperators.typeContext (S := sourceSignature language) nativeType (callerSorts term)

def parameterIndex (term : Term (withMetas (sourceSignature language) M) source sort)
    (position : Fin (selected term).length) : Fin (parameterSorts term).length :=
  ⟨position.val, by simpa only [parameterSorts, List.length_map] using position.isLt⟩

def parameterVar (term : Term (withMetas (sourceSignature language) M) source sort)
    (position : Fin (selected term).length) :
    Var (Srt := DeclaredSort language) (callerSorts term) ((parameterSorts term).get (parameterIndex term position)) :=
  weakenVar (S := sourceSignature language) source (varOfIdx (S := sourceSignature language) (parameterSorts term) (parameterIndex term position))

def functions (term : Term (withMetas (sourceSignature language) M) source sort)
    (position : Fin (selected term).length) : Tower.Tm (callerSorts term).length :=
  .var (varIdx (S := sourceSignature language) (parameterVar term position))

theorem functions_typed (installed : FullHeaders.Installation language)
    (term : Term (withMetas (sourceSignature language) M) source sort)
    (position : Fin (selected term).length) :
    Typing installed.rules (caller term) (functions term position)
      (liftClosed (ClosedOperators.bindingType (S := sourceSignature language) nativeType
        (M.get (sourceIndex term position)).1 (M.get (sourceIndex term position)).2)) := by
  have lookup := ClosedOperators.Formation.typeContext_lookup
    (S := sourceSignature language) (Head := Tower.Head) nativeType (parameterVar term position)
  have selectedSort : (parameterSorts term).get (parameterIndex term position) =
      functionSort (language := language) (M.get (sourceIndex term position)).1 (M.get (sourceIndex term position)).2 :=
    List.getElem_map _ (l := selected term) (i := position.val)
  have varTyped : Typing installed.rules (caller term) (functions term position)
      (Presentation.Ctx.lookup (caller term) (varIdx (S := sourceSignature language) (parameterVar term position))) := Typing.var (R := installed.rules) (Γ := caller term) (varIdx (S := sourceSignature language) (parameterVar term position))
  erw [lookup, selectedSort, functionSort_native] at varTyped
  exact varTyped

def variableSub (term : Term (withMetas (sourceSignature language) M) source sort) :
    Presentation.Sub Tower.Head source.length (callerSorts term).length :=
  fun index => .var (varIdx (S := sourceSignature language) (injPrefix (S := sourceSignature language) (Γ := parameterSorts term) source
    (varOfIdx (S := sourceSignature language) source index)))


def values (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) :
    ConstantSubstitution.Values Tower.Head (callerSorts term).length :=
  nativeValues (names scope language) (parameterNamespace scope) term nativeType
    (FullHeaders.Operational.images installed) (functions term)

theorem variableSub_typed (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) :
    ConstantSubstitution.TypedVariables installed.rules (context (names scope language) source)
      (caller term) (values installed scope term) (variableSub term) := by
  intro index
  let position : Var (Srt := DeclaredSort language) source (source.get index) :=
    varOfIdx (S := sourceSignature language) source index
  have sourceLookup := SortRealization.context_lookup (Head := Tower.Head) (names := names scope language) position
  have originalIndex : varIdx (S := sourceSignature language) position = index := varIdx_varOfIdx _ _
  rw [originalIndex] at sourceLookup
  have targetLookup := ClosedOperators.Formation.typeContext_lookup
    (S := sourceSignature language) (Head := Tower.Head) nativeType
    (injPrefix (S := sourceSignature language) (Γ := parameterSorts term) source position)
  change Typing _ (caller term) (variableSub term index)
    (ConstantSubstitution.interpret (values installed scope term) (variableSub term)
      (Presentation.Ctx.lookup (context (names scope language) source) index))
  erw [sourceLookup]
  change Typing _ (caller term) (variableSub term index)
    (nativeValues (names scope language) (parameterNamespace scope) term nativeType
      (FullHeaders.Operational.images installed) (functions term) ((names scope language).sort (source.get index)))
  erw [nativeValues_sort (names scope language) (names_injective scope language) (parameterNamespace scope)
    term nativeType (FullHeaders.Operational.images installed) (functions term) (source.get index)
    (context_sort_present term (source.get index) (List.get_mem source index))]
  have varTyped := Typing.var (R := installed.rules) (Γ := caller term)
    (varIdx (S := sourceSignature language)
      (injPrefix (S := sourceSignature language) (Γ := parameterSorts term) source position))
  erw [targetLookup] at varTyped
  exact varTyped

/-- One source template is interpreted into the installed full-TypeExpr
programs. Only its actually used functions occur in the native caller. -/
def program (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) : Tower.Tm (callerSorts term).length :=
  ConstantSubstitution.interpret (values installed scope term) (variableSub term)
    (Schema.fixedTemplate (names scope language) (programs (parameterNamespace scope)) term)

theorem program_typing (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) :
    Typing installed.rules (caller term) (program installed scope term) (liftClosed (nativeType sort)) :=
  interpretedTemplate_typing (names scope language) (names_injective scope language) (parameterNamespace scope)
    term (names_unselected scope language) installed.signature nativeType (FullHeaders.Operational.images installed)
    (FullHeaders.Operational.realization installed) rfl (caller term) (functions term)
    (functions_typed installed term) (variableSub term) (variableSub_typed installed scope term)

theorem program_judgment (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) :
    Judgment installed.rules (caller term) (program installed scope term) (liftClosed (nativeType sort)) :=
  ⟨(FullHeaders.Operational.realization installed).toFormation.typeContext_formed _, program_typing installed scope term⟩

def closedProgram (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) : Tower.Tm 0 :=
  closeTerm (caller term) (program installed scope term)

theorem closedProgram_typing (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) :
    Typing installed.rules .nil (closedProgram installed scope term)
      (closeType (caller term) (liftClosed (nativeType sort))) :=
  (FullHeaders.Operational.realization installed).toFormation.closeTerm_typing
    ((FullHeaders.Operational.realization installed).typeFormed sort)
    (program installed scope term) (program_typing installed scope term)

theorem sourceDeclarations_formed (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort) :
    (SchemaTemplates.signature (names scope language) (parameterNamespace scope) term).WellFormed Tower.rules :=
  SchemaTemplates.wellFormed (names scope language) (names_injective scope language) (parameterNamespace scope)
    term (names_unselected scope language)


/-- Supplying the actual used functions and source arguments through a
formed native context morphism earns the native call judgment. -/
theorem application_judgment (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort)
    {n : Nat} {destination : Presentation.Ctx Tower.Head n}
    (formed : ContextFormation installed.rules destination)
    (arguments : Presentation.Sub Tower.Head (callerSorts term).length n)
    (typed : FormationSensitive.CtxMor installed.rules (caller term) destination arguments) :
    Judgment installed.rules destination
      (applyClosed (caller term) arguments (liftClosed (closedProgram installed scope term)))
      (liftClosed (nativeType sort)) := by
  have closed := FormationCheckedTelescopePrograms.liftClosed_typing (closedProgram_typing installed scope term) destination
  have applied := FormationCheckedTelescopePrograms.apply_typed typed closed
  erw [subst_liftClosed] at applied
  exact ⟨formed, applied⟩

def applicationCode (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort)
    {n : Nat} (arguments : Presentation.Sub Tower.Head (callerSorts term).length n) :=
  FormationCheckedTelescopePrograms.applicationCode (caller term) arguments (program installed scope term)

theorem applicationCode_checked (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort)
    {n : Nat} (arguments : Presentation.Sub Tower.Head (callerSorts term).length n) :
    (applicationCode installed scope term arguments).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (applyClosed (caller term) arguments (liftClosed (closedProgram installed scope term)))
      (Presentation.subst arguments (program installed scope term)) = true :=
  FormationCheckedTelescopePrograms.applicationCode_checked (caller term) arguments (program installed scope term)

/-- The selected administrative beta count charges exactly source variables
and genuinely used function parameters; it is not an execution-time bound. -/
theorem applicationCode_stepCount (installed : FullHeaders.Installation language) (scope : DeclName)
    (term : Term (withMetas (sourceSignature language) M) source sort)
    {n : Nat} (arguments : Presentation.Sub Tower.Head (callerSorts term).length n) :
    (applicationCode installed scope term arguments).stepCount = source.length + (selected term).length := by
  erw [applicationCode, FormationCheckedTelescopePrograms.applicationCode_stepCount]
  exact (List.length_append (as := source) (bs := parameterSorts term)).trans
    (congrArg (Nat.add source.length) (List.length_map (f := fun index => functionSort (language := language) (M.get index).1 (M.get index).2)))

end NativeTemplate
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored.Controls
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding
open AuthoredTypeExpressions
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata

private def baseLanguage : LanguageDef where
  name := "full-rule-interface"
  types := [⟨"A", .ast⟩, ⟨"B", .ast⟩]
  terms := []
  equations := []
  rewrites := []

private def a : TypeExpr := .base "A"
private def b : TypeExpr := .base "B"
private def bagFunctions : TypeExpr := .collection .hashBag (.arrow a b)
private def sequenceSets : TypeExpr := .multiBinder (.collection .hashSet a)
private def arrowVector : TypeExpr := .arrow (.multiBinder b) (.collection .vec a)
private def rule : RewriteRule where
  name := "retained-full-context"
  typeContext := [("x", bagFunctions), ("sequence", sequenceSets), ("consumer", arrowVector), ("unused", bagFunctions)]
  premises := []
  left := .lambda none (.lambda none (.fvar "x"))
  right := .lambda none (.lambda none (.fvar "x"))

private def spec : RuleBindingSpec where
  dependencies := [("x", [a,a]), ("sequence", [.arrow a b]), ("consumer", []), ("unused", [a,a])]
  occurrences := [⟨"x", .left, [0,0], [.bvar 1,.bvar 0]⟩, ⟨"x", .right, [0,0], [.bvar 1,.bvar 0]⟩]

private def language : LanguageDef := {baseLanguage with rewrites := [{rule with bindings := some spec}]}
private def metadata : Metadata language rule spec := (metadata? language rule spec).get (by decide +kernel)
private def A : DeclaredSort language := ⟨a, .base ⟨0, by decide⟩⟩
private def B : DeclaredSort language := ⟨b, .base ⟨1, by decide⟩⟩
private def X : DeclaredSort language := DeclaredSort.collection .hashBag (DeclaredSort.arrow A B)
private def index : Fin metadata.entries.length := ⟨0, by decide +kernel⟩
private abbrev S := sourceSignature language
private def call : Term (withMetas S metadata.entries) [A,A] X :=
  .op (.inr (@MetaOp.mk S metadata.entries index)) (by
    change Args (withMetas S metadata.entries) [([], A), ([], A)] [A,A]
    exact .cons (.var (.succ .zero)) (.cons (.var .zero) .nil))
private def swapped : Term (withMetas S metadata.entries) [A,A] X :=
  .op (.inr (@MetaOp.mk S metadata.entries index)) (by
    change Args (withMetas S metadata.entries) [([], A), ([], A)] [A,A]
    exact .cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
private def observationNames : Names (withMetas S metadata.entries) where
  sort := fun _ => `SourceSort
  operator := fun operator => match operator with
    | .inl _ => `SourceConstructor
    | .inr (.mk position) => .num `SourceMeta position.val
private def observe {context : Ctx S} {sort : S.Srt}
    (source : Term (withMetas S metadata.entries) context sort) : Tower.Tm context.length := encode observationNames source
private def installed : FullHeaders.Installation language := (FullHeaders.install? language).get (by decide +kernel)

example : metadata.readSchema? (metadata.sourceSchema call) = some call := metadata.readSchema?_roundtrip call
example : metadata.sourceSchema call ≠ metadata.sourceSchema swapped := by
  intro same
  have equal := metadata.sourceSchema_injective same
  exact (by decide +kernel : observe call ≠ observe swapped) (congrArg observe equal)
example : FormationSensitive.ContextFormation installed.rules (nativeParameterContext metadata [A]) :=
  nativeParameterContextFormed metadata installed [A]
example : metadata.entries.length = rule.typeContext.length := metadata.source_length
example : MetadataDeclared language rule spec := metadata?_exact.mp ⟨metadata, Option.some_get _ |>.symm⟩

private def unknownRule : RewriteRule := {rule with typeContext := [("bad", .collection .hashSet (.multiBinder (.base "missing")))]}
private def unknownSpec : RuleBindingSpec := {dependencies := [("bad", [])]}
private def dependencySpec : RuleBindingSpec := {spec with dependencies := [("x", [.collection .vec (.base "missing")]), ("sequence", []), ("consumer", []), ("unused", [])]}

def checks : List (String × Bool) := [
  ("full-type-rule-metadata-decodes", (metadata? language rule spec).isSome),
  ("all-original-rows-retained", metadata.entries.length == 4),
  ("original-row-order", (metadata.entries.map fun entry => (entry.1.map Subtype.val, entry.2.val)) ==
    Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.metaArities (language := language) rule spec),
  ("full-dependency-types-retained", ((metadata.entries.get ⟨1, by decide +kernel⟩).1.map Subtype.val) == [.arrow a b]),
  ("unused-row-retained", (metadata.entries.get ⟨3, by decide +kernel⟩).2.val == bagFunctions),
  ("equal-typed-rows-have-distinct-positions", (metadata.sourceIndex index).val !=
    (metadata.sourceIndex ⟨3, by decide +kernel⟩).val),
  ("collection-result-not-reduced-to-base", (metadata.entries.get index).2.val == bagFunctions),
  ("multiBinder-result-retained", (metadata.entries.get ⟨1, by decide +kernel⟩).2.val == sequenceSets),
  ("unknown-result-base-refuses", (metadata? language unknownRule unknownSpec).isNone),
  ("unknown-dependency-base-refuses", (metadata? language rule dependencySpec).isNone),
  ("native-parameter-lookup", Presentation.Ctx.lookup (nativeParameterContext metadata [A]) (nativeParameterIndex metadata [A] index) ==
    liftClosed (ClosedOperators.spineType (S := S) nativeType [A,A,A] (nativeType X))),
  ("literal-call-schema-roundtrip", (metadata.readSchema? (metadata.sourceSchema call)).map observe == some (observe call)),
  ("literal-swapped-schema-roundtrip", (metadata.readSchema? (metadata.sourceSchema swapped)).map observe == some (observe swapped)),
  ("dependency-occurrence-order-visible", observe call != observe swapped),
  ("unknown-constructor-reader-refuses", (operatorReader language).read (sort := X) (.subst (.base "missing") bagFunctions) |>.isNone),
  ("full-source-installation-runs", (FullHeaders.install? language).isSome)
]

theorem checks_pass : checks.all Prod.snd = true := by decide +kernel

def main : IO Unit := do
  for check in checks do
    if !check.2 then throw (IO.userError check.1)
  IO.println s!"{checks.length} full authored rule-interface controls passed"

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored.Controls



set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored.NativeTemplate.Controls
open Mettapedia.OSLF
open Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Declaration BindingSignatureEmbedding TelescopeAbstraction FormationSensitive
open AuthoredTypeExpressions
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata
open Declarations.BindingSignaturePackage
open SchemaTemplates

private def language : LanguageDef where
  name := "used-native-function-parameters"
  types := [⟨"A", .ast⟩, ⟨"Empty", .ast⟩]
  terms := []
  equations := []
  rewrites := []

private abbrev S := sourceSignature language
private def A : DeclaredSort language := ⟨.base "A", .base ⟨0, by decide⟩⟩
private def E : DeclaredSort language := ⟨.base "Empty", .base ⟨1, by decide⟩⟩
private def AA := DeclaredSort.arrow A A
private def metas : List (MetaArity S) := [([], E), ([A], A)]
private def usedIndex : Fin metas.length := ⟨1, by decide⟩
private def unusedIndex : Fin metas.length := ⟨0, by decide⟩
private def callHere : Term (withMetas S metas) [A] A :=
  .op (.inr (@MetaOp.mk S metas usedIndex)) (.cons (.var .zero) .nil)
private def callOuter : Term (withMetas S metas) [A,A] A :=
  .op (.inr (@MetaOp.mk S metas usedIndex)) (.cons (.var (.succ .zero)) .nil)
private def closedSchema : Term (withMetas S metas) [] AA :=
  .op (.inl (StructuralPrograms.lambdaOperator A A)) (.cons callHere .nil)
private def openSchema : Term (withMetas S metas) [A] AA :=
  .op (.inl (StructuralPrograms.lambdaOperator A A)) (.cons callOuter .nil)
private def duplicateSchema : Term (withMetas S metas) [A] A :=
  .op (.inl (StructuralPrograms.substitutionOperator A A)) (.cons callOuter (.cons callHere .nil))
private def installed : FullHeaders.Installation language := (FullHeaders.install? language).get (by decide +kernel)
private def scope : DeclName := `FullNativeSchemaFixture
private def supplied : List (Fin metas.length × Nat) := [(usedIndex, 42)]
private def expectedClosed : Tower.Tm 0 :=
  .lam (.app (.lam (.var 0)) (.lam (.app (.var 1) (.var 0))))
private def expectedOpen : Tower.Tm 0 :=
  .lam (.lam (.app (.lam (.var 0)) (.lam (.app (.var 2) (.var 1)))))
private def capturedWrongly : Tower.Tm 0 :=
  .lam (.lam (.app (.lam (.var 0)) (.lam (.app (.var 2) (.var 0)))))
private def identityArguments : Presentation.Sub Tower.Head (callerSorts closedSchema).length 0 :=
  fun index => Fin.cases ClosedOperators.Derived.identity (fun impossible => Fin.elim0 impossible) index
private def instantiated : Tower.Tm 0 :=
  Presentation.subst identityArguments (program installed scope closedSchema)
private def call : Tower.Tm 0 :=
  applyClosed (caller closedSchema) identityArguments (liftClosed (closedProgram installed scope closedSchema))

example : Judgment installed.rules (caller closedSchema) (program installed scope closedSchema) (liftClosed (nativeType AA)) :=
  program_judgment installed scope closedSchema
example : Typing installed.rules .nil (closedProgram installed scope closedSchema)
    (closeType (caller closedSchema) (liftClosed (nativeType AA))) :=
  closedProgram_typing installed scope closedSchema
example : Typing installed.rules .nil (closedProgram installed scope openSchema)
    (closeType (caller openSchema) (liftClosed (nativeType AA))) :=
  closedProgram_typing installed scope openSchema
example : Typing installed.rules .nil (closedProgram installed scope duplicateSchema)
    (closeType (caller duplicateSchema) (liftClosed (nativeType A))) :=
  closedProgram_typing installed scope duplicateSchema
example : (SchemaTemplates.signature (names scope language) (parameterNamespace scope) closedSchema).WellFormed Tower.rules :=
  sourceDeclarations_formed scope closedSchema
example : ConstantSubstitution.RootFree
    (SchemaTemplates.rules (names scope language) (parameterNamespace scope) closedSchema).computation :=
  SchemaTemplates.rootFree _ _ _
example : ∀ original ∈ usedMetavariables closedSchema, ∃ value, supplied.lookup original = some value :=
  (readFunctions?_exact closedSchema supplied).mp ⟨[42], by decide +kernel⟩

private def mixedMetas : List (MetaArity S) := [([], E), ([E,A], A)]
private def mixedSchema : Term (withMetas S mixedMetas) [E,A] A :=
  .op (.inr (@MetaOp.mk S mixedMetas ⟨1, by decide⟩))
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
private def expectedMixed : Tower.Tm 0 :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0))))
private def mixedWrongly : Tower.Tm 0 :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1))))
example : Typing installed.rules .nil (closedProgram installed scope mixedSchema)
    (closeType (caller mixedSchema) (liftClosed (nativeType A))) :=
  closedProgram_typing installed scope mixedSchema

private def emptyName : DeclName := (names scope language).sort E
private def unusedName : DeclName := FiniteParameters.indexedName (parameterNamespace scope) unusedIndex
private def usedName : DeclName := FiniteParameters.indexedName (parameterNamespace scope) usedIndex

def checks : List (String × Bool) := [
  ("full-header-installation", (FullHeaders.install? language).isSome),
  ("unused-sort-has-no-authored-constructors", language.terms.isEmpty),
  ("unused-metadata-sort-declared", ((SchemaTemplates.signature (names scope language) (parameterNamespace scope) closedSchema).entries emptyName).isSome),
  ("unused-function-not-installed", ((SchemaTemplates.signature (names scope language) (parameterNamespace scope) closedSchema).entries unusedName).isNone),
  ("used-function-is-installed", ((SchemaTemplates.signature (names scope language) (parameterNamespace scope) closedSchema).entries usedName).isSome),
  ("original-used-ordinal-is-one", (selected closedSchema).map Fin.val == [1]),
  ("used-telescope-has-one-parameter", (parameterSorts closedSchema).length == 1),
  ("unused-empty-row-needs-no-value", readFunctions? closedSchema supplied == some [42]),
  ("missing-actually-used-parameter-refuses", (readFunctions? closedSchema ([] : List (Fin metas.length × Nat))).isNone),
  ("wrong-original-ordinal-refuses", (readFunctions? closedSchema [(unusedIndex,42)]).isNone),
  ("extra-unused-value-not-required", readFunctions? closedSchema [(unusedIndex,11),(usedIndex,42)] == some [42]),
  ("source-occurrences-retained", (usedMetavariables duplicateSchema).map Fin.val == [1,1]),
  ("duplicate-occurrence-uses-one-function-parameter", (selected duplicateSchema).map Fin.val == [1]),
  ("one-value-serves-both-original-occurrences", readFunctions? duplicateSchema supplied == some [42]),
  ("actual-native-closed-program", closedProgram installed scope closedSchema == expectedClosed),
  ("actual-native-open-caller-program", closedProgram installed scope openSchema == expectedOpen),
  ("binder-capture-is-distinguished", closedProgram installed scope openSchema != capturedWrongly),
  ("actual-native-function-application", instantiated == (.app (.lam (.var 0)) (.lam (.app (.lam (.var 0)) (.var 0))) : Tower.Tm 0)),
  ("actual-beta-certificate-replays", (applicationCode installed scope closedSchema identityArguments).check
    (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot call instantiated),
  ("wrong-claimed-endpoint-refuses", !(applicationCode installed scope closedSchema identityArguments).check
    (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot call (.lam (.var 0))),
  ("distinct-source-dependency-types-keep-telescope-order", closedProgram installed scope mixedSchema == expectedMixed),
  ("distinct-source-dependency-swap-is-distinguished", closedProgram installed scope mixedSchema != mixedWrongly),
  ("administrative-beta-count-is-one", (applicationCode installed scope closedSchema identityArguments).stepCount == 1)
]

def main : IO Unit := do
  for check in checks do
    if !check.2 then throw (IO.userError check.1)
  IO.println s!"{checks.length} full native schema template controls passed"

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored.NativeTemplate.Controls

#guard Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored.NativeTemplate.Controls.checks.all Prod.snd


set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open ScopedElaboration SchemaElaboration NamedBodies
open Mettapedia.GSLT.LanguageDef.WellSorted


end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT.Authored


set_option autoImplicit false

