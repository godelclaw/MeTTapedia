import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.OSLF.Framework.GeneralCanonicalQueryOccurrences
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation
import Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion

/-!
# Ordered module declarations admitted to first-order root execution

The source is an assembled declaration fragment, an explicit order, the complete
language core and an immutable provider snapshot. The checker binds the core's
rewrite list to that order and constructs the existing typed query profile and
first-order rule program. Its evidence consists of local syntax, typing,
provider and compilation checks; no execution correspondence is an input.

The physical module exporter supplies `ModuleRewriteRulesV1` with ordered
`ModuleRuleOccurrenceV1` rows whose origins are `SyntaxOriginV1(source, site)`.
This interface uses those portable strings, not runtime handles. Reading source
bytes, assembling native module values and decoding their full language core
remain separate front-end boundaries. In particular a finite set supplies no
implicit execution order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OrderedFirstOrderAdmission

open Mettapedia.OSLF.MeTTaIL
open Syntax
open Mettapedia.OSLF.Framework
open GeneralCanonicalAgreement

deriving instance DecidableEq for RewriteRule

/-- The two strings in the physical `SyntaxOriginV1` value. -/
abbrev PortableOrigin := String × String

abbrev RuleEntry := Entry PortableOrigin String RewriteRule
abbrev RuleFragment := Finset RuleEntry

/-- The complete submitted package is retained even when admission refuses it. -/
structure Source where
  revision : String
  contract : NativeAuthoring.ImportContract
  fragment : RuleFragment
  order : List RuleEntry
  core : LanguageDef

def Source.ruleRows (source : Source) : List RewriteRule := source.order.map Entry.body

/-- A rule index denotes a portable declaration origin in the supplied order. -/
def Source.originAt? (source : Source) (index : Nat) : Option PortableOrigin :=
  (source.order[index]?).map Entry.origin

def originTerm (origin : PortableOrigin) : CettaWire.Term :=
  .application "SyntaxOriginV1" [.string origin.1, .string origin.2]

def decodeOrigin? : CettaWire.Term → Option PortableOrigin
  | .application "SyntaxOriginV1" [.string source, .string site] => some (source, site)
  | _ => none

@[simp] theorem decodeOrigin_originTerm (origin : PortableOrigin) :
    decodeOrigin? (originTerm origin) = some origin := by cases origin; rfl

theorem originTerm_injective : Function.Injective originTerm := by
  intro first second same
  have recovered := congrArg decodeOrigin? same
  simpa only [decodeOrigin_originTerm, Option.some.injEq] using recovered

/-- Adapt the native five-field row to the existing complete authored codec.
The native representation has no slot for explicit binding annotations. -/
def decodeNativeRule? : CettaWire.Term → Option RewriteRule
  | .application "RewriteRule" [name, context, premises, left, right] =>
    InferenceCettaWire.AuthoredRule.decodeRewrite? (.application "ScopedRewriteRuleV1"
      [name, context, premises, left, right, .symbol "RuleBindingNone"])
  | _ => none

def nativeRuleTerm? (rule : RewriteRule) : Option CettaWire.Term :=
  if rule.bindings.isNone then
    some (.application "RewriteRule" [.string rule.name,
      InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext,
      InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises,
      InferenceCettaWire.encodePattern rule.left, InferenceCettaWire.encodePattern rule.right])
  else none

theorem decodeNativeRule_nativeRuleTerm (rule : RewriteRule) (unannotated : rule.bindings = none) :
    (nativeRuleTerm? rule).bind decodeNativeRule? = some rule := by
  cases rule
  dsimp only at unannotated
  subst unannotated
  simp [nativeRuleTerm?, decodeNativeRule?, InferenceCettaWire.AuthoredRule.decodeRewrite?,
    InferenceCettaWire.AuthoredRule.decodeOptionalBinding?, InferenceCettaWire.decodeList_encodeList]

def nativeOccurrenceTerm? (entry : RuleEntry) : Option CettaWire.Term := do
  let rule ← nativeRuleTerm? entry.body
  pure (.application "ModuleRuleOccurrenceV1" [originTerm entry.origin, rule])

def decodeNativeOccurrence? : CettaWire.Term → Option RuleEntry
  | .application "ModuleRuleOccurrenceV1" [origin, rule] => do
    let origin ← decodeOrigin? origin
    let body ← decodeNativeRule? rule
    pure ⟨origin, body.name, body⟩
  | _ => none

theorem nativeOccurrence_roundTrip (entry : RuleEntry)
    (unannotated : entry.body.bindings = none) (label : entry.label = entry.body.name) :
    (nativeOccurrenceTerm? entry).bind decodeNativeOccurrence? = some entry := by
  rcases entry with ⟨origin, name, rule⟩
  dsimp only at label unannotated
  subst name
  cases encoded : nativeRuleTerm? rule with
  | none =>
    have impossible := decodeNativeRule_nativeRuleTerm rule unannotated
    simp only [encoded, Option.bind_none, reduceCtorEq] at impossible
  | some wire =>
    have decoded : decodeNativeRule? wire = some rule := by
      simpa only [encoded, Option.bind_some] using decodeNativeRule_nativeRuleTerm rule unannotated
    simp [nativeOccurrenceTerm?, encoded, decodeNativeOccurrence?, decoded]

/-- Decode the ordered export list directly, retaining all occurrences. -/
def decodeNativeOccurrences? (wire : CettaWire.Term) : Option (List RuleEntry) :=
  CettaWire.decodeList decodeNativeOccurrence? wire

def nativeOccurrencesTerm? : List RuleEntry → Option CettaWire.Term
  | [] => some (.symbol "LNil")
  | entry :: entries => do
    let first ← nativeOccurrenceTerm? entry
    let rest ← nativeOccurrencesTerm? entries
    pure (.application "LCons" [first, rest])

theorem nativeOccurrences_roundTrip (entries : List RuleEntry)
    (unannotated : ∀ entry ∈ entries, entry.body.bindings = none)
    (labels : ∀ entry ∈ entries, entry.label = entry.body.name) :
    (nativeOccurrencesTerm? entries).bind decodeNativeOccurrences? = some entries := by
  induction entries with
  | nil => simp [nativeOccurrencesTerm?, decodeNativeOccurrences?, CettaWire.decodeList]
  | cons entry entries ih =>
    have first := nativeOccurrence_roundTrip entry (unannotated entry (by simp)) (labels entry (by simp))
    have rest := ih (fun row member => unannotated row (by simp [member]))
      (fun row member => labels row (by simp [member]))
    cases firstEncoded : nativeOccurrenceTerm? entry with
    | none => simp only [firstEncoded, Option.bind_none, reduceCtorEq] at first
    | some wire =>
      cases restEncoded : nativeOccurrencesTerm? entries with
      | none => simp only [restEncoded, Option.bind_none, reduceCtorEq] at rest
      | some wires =>
        simp only [firstEncoded, Option.bind_some] at first
        simp only [restEncoded, Option.bind_some] at rest
        change CettaWire.decodeList decodeNativeOccurrence? wires = some entries at rest
        simp [nativeOccurrencesTerm?, firstEncoded, restEncoded, decodeNativeOccurrences?,
          CettaWire.decodeList, first, rest]

def Source.checkCompatible (source : Source) : Bool :=
  source.order.all fun first => source.order.all fun second =>
    source.contract.entryCompatible first second

theorem Source.checkCompatible_iff (source : Source) :
    source.checkCompatible = true ↔
      List.AllCompatible source.contract.entryCompatible source.order := by
  simp only [Source.checkCompatible, List.all_eq_true, List.AllCompatible]

/-- Literal provider values must lie in the existing subject compiler's
image. Closedness and authored sorts are checked by the typed query profile. -/
def checkProviderFirstOrder (provider : GeneralPremise.ProviderSnapshot) : Bool :=
  provider.rows.all fun row => Match.isMatchCorrectListAux row.values

theorem checkProviderFirstOrder_relations {provider : GeneralPremise.ProviderSnapshot}
    (checked : checkProviderFirstOrder provider = true) :
    MeTTaILFirstOrderRuleCompilation.FirstOrderRelations (providerRelEnv provider) := by
  intro relation arguments _ tuple member
  obtain ⟨row, rowMember, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · have same := Option.some.inj selected
    simpa only [← same] using List.all_eq_true.mp checked row rowMember
  · cases selected

inductive Refusal where
  | duplicateDeclaration
  | orderCoverage
  | conflictingDeclarations
  | ruleLabelMismatch
  | coreRuleMismatch
  | equations
  | typedQueryProfile
  | incompleteRootPlan
  | unsupportedFirstOrderCompilation
  | nonFirstOrderProviderPayload
  deriving Repr, DecidableEq

/-- Independent checks on source data; no unsupported row is filtered out. -/
def sourceIssues (source : Source) : List Refusal :=
  (if source.order.Nodup then [] else [.duplicateDeclaration]) ++
  (if source.order.toFinset = source.fragment then [] else [.orderCoverage]) ++
  (if source.checkCompatible then []
    else [.conflictingDeclarations]) ++
  (if source.order.all (fun entry => entry.label == entry.body.name) then []
    else [.ruleLabelMismatch]) ++
  (if source.core.rewrites = source.ruleRows then [] else [.coreRuleMismatch]) ++
  (if source.core.equations.isEmpty then [] else [.equations])

def issues (source : Source) (provider : GeneralPremise.ProviderSnapshot) : List Refusal :=
  sourceIssues source ++
  (if checkQueryProfileFacts source.core provider then [] else [.typedQueryProfile]) ++
  (if (rootPlan source.core provider).complete then [] else [.incompleteRootPlan]) ++
  (if (MeTTaILFirstOrderRuleCompilation.compileProgram? source.core.rewrites).isSome then []
    else [.unsupportedFirstOrderCompilation]) ++
  (if checkProviderFirstOrder provider then [] else [.nonFirstOrderProviderPayload])

/-- Constructed admission facts bind both executor inputs to one source. -/
structure Admitted (source : Source) (provider : GeneralPremise.ProviderSnapshot) where
  view : OrderedView source.fragment
  order_eq : view.entries = source.order
  compatible : List.AllCompatible source.contract.entryCompatible source.order
  labels : source.order.all (fun entry => entry.label == entry.body.name) = true
  rows_eq : source.core.rewrites = source.ruleRows
  equationFree : source.core.equations = []
  profile : QueryProfileFacts source.core provider
  rootComplete : (rootPlan source.core provider).complete = true
  program : MeTTaILFirstOrderRuleCompilation.RuleProgram source.core.rewrites
  providerFirstOrder : checkProviderFirstOrder provider = true

def admit? (source : Source) (provider : GeneralPremise.ProviderSnapshot) :
    Option (Admitted source provider) :=
  if ordered : source.order.Nodup ∧ source.order.toFinset = source.fragment then do
    if accepted : source.checkCompatible = true ∧
      source.order.all (fun entry => entry.label == entry.body.name) = true ∧
      source.core.rewrites = source.ruleRows ∧ source.core.equations.isEmpty = true ∧
      checkQueryProfileFacts source.core provider = true ∧
      (rootPlan source.core provider).complete = true then
    if payloads : checkProviderFirstOrder provider = true then
    let program ← MeTTaILFirstOrderRuleCompilation.compileProgram? source.core.rewrites
    some {
      view := ⟨source.order, ordered.1, ordered.2⟩
      order_eq := rfl
      compatible := (source.checkCompatible_iff).mp accepted.1
      labels := accepted.2.1
      rows_eq := accepted.2.2.1
      equationFree := List.isEmpty_iff.mp accepted.2.2.2.1
      profile := QueryProfileFacts.of_check accepted.2.2.2.2.1
      rootComplete := accepted.2.2.2.2.2
      program
      providerFirstOrder := payloads }
    else none
    else none
  else none

theorem admit_isSome_iff (source : Source) (provider : GeneralPremise.ProviderSnapshot) :
    (admit? source provider).isSome = true ↔
      source.order.Nodup ∧ source.order.toFinset = source.fragment ∧
      source.checkCompatible = true ∧
      source.order.all (fun entry => entry.label == entry.body.name) = true ∧
      source.core.rewrites = source.ruleRows ∧ source.core.equations.isEmpty = true ∧
      checkQueryProfileFacts source.core provider = true ∧
      (rootPlan source.core provider).complete = true ∧
      (MeTTaILFirstOrderRuleCompilation.compileProgram? source.core.rewrites).isSome = true ∧
      checkProviderFirstOrder provider = true := by
  unfold admit?
  split
  · rename_i validView
    split
    · rename_i accepted
      split
      · rename_i payloads
        simp only [validView.1, validView.2, true_and, accepted.1, accepted.2.1,
          accepted.2.2.1, accepted.2.2.2.1, accepted.2.2.2.2.1, accepted.2.2.2.2.2, payloads, and_true]
        cases programChecked : MeTTaILFirstOrderRuleCompilation.compileProgram? source.core.rewrites <;> rfl
      · rename_i noPayloads
        simp only [Option.isSome_none, Bool.false_eq_true]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_, _, _, _, _, _, _, _, _, payloads⟩
          exact noPayloads payloads
    · rename_i refused
      simp only [Option.isSome_none, Bool.false_eq_true]
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨_, _, compatible, labels, rows, equations, profile, complete, _⟩
        exact refused ⟨compatible, labels, rows, equations, profile, complete⟩
  · rename_i noView
    simp only [Option.isSome_none, Bool.false_eq_true]
    constructor
    · intro accepted
      cases accepted
    · rintro ⟨unique, coverage, _⟩
      exact noView ⟨unique, coverage⟩

private theorem issue_absent (proposition : Prop) [Decidable proposition] (refusal : Refusal) :
    (if proposition then [] else [refusal]) = [] ↔ proposition := by
  by_cases accepted : proposition <;> simp [accepted]

/-- Diagnostics and the executable admission decision agree in both directions. -/
theorem admit_isSome_iff_issues_empty (source : Source) (provider : GeneralPremise.ProviderSnapshot) :
    (admit? source provider).isSome = true ↔ issues source provider = [] := by
  rw [admit_isSome_iff]
  simp only [issues, sourceIssues, List.append_eq_nil_iff, issue_absent, and_assoc]

theorem admit_none_iff_issues_nonempty (source : Source) (provider : GeneralPremise.ProviderSnapshot) :
    admit? source provider = none ↔ issues source provider ≠ [] := by
  have agrees := admit_isSome_iff_issues_empty source provider
  cases checked : admit? source provider with
  | none => simp only [checked, Option.isSome_none, Bool.false_eq_true, false_iff] at agrees; simp [agrees]
  | some admitted =>
    have empty : issues source provider = [] := agrees.mp (by rw [checked]; rfl)
    simp [empty]

/-- Provider identity includes the complete ordered signature and row lists.
Equal-valued repeated rows and their positions are not collapsed. -/
def Admitted.sameProvider {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (_admitted : Admitted source provider) (current : GeneralPremise.ProviderSnapshot) : Bool :=
  decide (current = provider)

theorem Admitted.sameProvider_iff {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (current : GeneralPremise.ProviderSnapshot) :
    admitted.sameProvider current = true ↔ current = provider := by
  simp [Admitted.sameProvider]

theorem Admitted.provider_changed {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (current : GeneralPremise.ProviderSnapshot)
    (changed : current ≠ provider) : admitted.sameProvider current = false := by
  simp [Admitted.sameProvider, changed]

/-- The admitted snapshot earns the existing compiler closure condition from
its actual literal rows, independently of any query's answers. -/
theorem Admitted.relations_firstOrder {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) :
    MeTTaILFirstOrderRuleCompilation.FirstOrderRelations (providerRelEnv provider) :=
  checkProviderFirstOrder_relations admitted.providerFirstOrder

/-- Admission refines the selected original finite-fragment import contract. -/
theorem Admitted.import_valid {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) :
    match source.contract with
    | .coherentOrigin => ModuleAlgebra.Valid source.fragment
    | .structuralView => OriginView.Valid source.fragment := by
  have checked : (source.contract.check? source.order).isSome = true :=
    (List.unionCompatible?_from_empty_isSome_iff source.contract.entryCompatible
      source.contract.entryCompatible_self source.contract.entryCompatible_symm source.order).mpr
        admitted.compatible
  have valid := (source.contract.check_isSome_iff source.order).mp checked
  have covered : source.order.toFinset = source.fragment := by
    rw [← admitted.order_eq]
    exact admitted.view.covers
  cases contract : source.contract <;> simp only [contract] at valid ⊢ <;>
    simpa only [covered] using valid

/-- Origin lookup and language lookup describe exactly the same occurrence. -/
theorem Admitted.rule_at {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (index : Fin source.order.length) :
    source.core.rewrites[index.val]? = some source.order[index].body ∧
      source.originAt? index.val = some source.order[index].origin := by
  rw [admitted.rows_eq]
  simp [Source.ruleRows, Source.originAt?, index.isLt]

theorem Admitted.program_length {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) : admitted.program.plans.length = source.order.length := by
  rw [admitted.program.plans_length, admitted.rows_eq]
  simp [Source.ruleRows]

theorem Admitted.unannotated {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) {entry : RuleEntry} (member : entry ∈ source.order) :
    entry.body.bindings = none := by
  have authored : entry.body ∈ source.core.rewrites := by
    rw [admitted.rows_eq, Source.ruleRows]
    exact List.mem_map_of_mem member
  rw [← admitted.program.erase_eq_source,
    MeTTaILFirstOrderRuleCompilation.eraseRulePlans] at authored
  obtain ⟨plan, _, same⟩ := List.mem_map.mp authored
  rw [← same]
  rfl

/-- Every admitted native row can replay its full body and portable origin. -/
theorem Admitted.native_roundTrip {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) {entry : RuleEntry} (member : entry ∈ source.order) :
    (nativeOccurrenceTerm? entry).bind decodeNativeOccurrence? = some entry :=
  nativeOccurrence_roundTrip entry (admitted.unannotated member)
    (by simpa only [beq_iff_eq] using List.all_eq_true.mp admitted.labels entry member)

theorem Admitted.native_rows_roundTrip {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) :
    (nativeOccurrencesTerm? source.order).bind decodeNativeOccurrences? = some source.order :=
  nativeOccurrences_roundTrip source.order (fun _ member => admitted.unannotated member)
    (fun entry member => by simpa only [beq_iff_eq] using List.all_eq_true.mp admitted.labels entry member)

/-- The fused program's occurrence erases to the original declaration body. -/
theorem Admitted.compiled_rule_at {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (index : Fin source.order.length) :
    (admitted.program.planAt ⟨index.val, by simpa only [admitted.rows_eq, Source.ruleRows, List.length_map] using index.isLt⟩).erase =
      source.order[index].body := by
  rw [admitted.program.erase_planAt]
  simp [admitted.rows_eq, Source.ruleRows]

/-- Raw compilation of the complete source-indexed structural matrix and every leaf
with its own admitted rule plan. The compiler derives its fuel from the matrix
work account rather than imposing a language-specific cutoff. -/
def Admitted.fusedProgram? {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) :
    Option (OrderedDecisionRuleFusion.Program
      MeTTaILPatternMatrixCompilation.Matrix.Head
      (MeTTaILPatternMatrixCompilation.Matrix.RuleOccurrence source.core)
      MeTTaILFirstOrderRuleCompilation.RulePlan) :=
  OrderedDecisionRuleFusion.compileWildcard?
    (fun occurrence => some (admitted.program.planAt occurrence))
    (OrderedPatternMatrixWildcardColumnCompilation.compile
      (MeTTaILPatternMatrixCompilation.Matrix.ofLanguage source.core))

theorem Admitted.fusedProgram_isSome {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider) :
    admitted.fusedProgram?.isSome = true := by
  obtain ⟨program, compiled⟩ := OrderedDecisionRuleFusion.compileWildcard?_exists
    (fun occurrence => some (admitted.program.planAt occurrence))
    (fun occurrence => ⟨admitted.program.planAt occurrence, rfl⟩)
    (OrderedPatternMatrixWildcardColumnCompilation.compile
      (MeTTaILPatternMatrixCompilation.Matrix.ofLanguage source.core))
  simpa only [Admitted.fusedProgram?, compiled] using (show (some program).isSome = true from rfl)

/-- The raw optimized artifact exists for every admitted finite module.
Typed invocation dispatch uses `sortedFusedProgram` below. -/
def Admitted.fusedProgram {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) :
    OrderedDecisionRuleFusion.Program
      MeTTaILPatternMatrixCompilation.Matrix.Head
      (MeTTaILPatternMatrixCompilation.Matrix.RuleOccurrence source.core)
      MeTTaILFirstOrderRuleCompilation.RulePlan :=
  admitted.fusedProgram?.get admitted.fusedProgram_isSome

theorem Admitted.fusedProgram?_eq_some {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider) :
    admitted.fusedProgram? = some admitted.fusedProgram :=
  (Option.some_get admitted.fusedProgram_isSome).symm

/-- Raw fused leaf evaluation agrees with the source-order rule-plan
emissions, including all binding and query fields. Source-typing and scoped
receipt correspondence are separate obligations, not premises of compilation. -/
theorem Admitted.fusedProgram_emissions {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (subject : Pattern) :
    admitted.fusedProgram.evalAll
        (fun leaf => leaf.plan.runEmissions relations source.core leaf.occurrence.val subject)
        [MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject] =
      (List.finRange source.core.rewrites.length).flatMap
        (fun occurrence => (admitted.program.planAt occurrence).runEmissions
          relations source.core occurrence.val subject) := by
  rw [OrderedDecisionRuleFusion.evalAll_eq_of_compileWildcard?
    (fun occurrence => some (admitted.program.planAt occurrence))
    (fun occurrence => (admitted.program.planAt occurrence).runEmissions
      relations source.core occurrence.val subject)
    (fun leaf => leaf.plan.runEmissions relations source.core leaf.occurrence.val subject)
    (by intro occurrence plan compiled; cases Option.some.inj compiled; rfl)
    _ _ admitted.fusedProgram?_eq_some]
  rw [OrderedPatternMatrixWildcardColumnCompilation.compile_all_correct]
  apply MeTTaILPatternMatrixCompilation.Matrix.runMatrixAll_ofLanguage_eq_occurrenceFold
  intro occurrence rejected
  have empty := MeTTaILPatternMatrixCompilation.Matrix.matchPattern_eq_nil_of_structural_rejection
    (MeTTaILPatternMatrixCompilation.Matrix.ruleAt source.core occurrence).left subject rejected
  have left : (admitted.program.planAt occurrence).left.erase =
      (MeTTaILPatternMatrixCompilation.Matrix.ruleAt source.core occurrence).left :=
    congrArg RewriteRule.left (admitted.program.erase_planAt occurrence)
  simp only [MeTTaILFirstOrderRuleCompilation.RulePlan.runEmissions,
    MeTTaILFirstOrderRuleCompilation.run_eq_matchPattern, left, empty, List.flatMap_nil]

/-- Select checked invocation sorts from the existing structural matrix.
Each retained row still carries its original source-list `Fin` occurrence. -/
def Admitted.sortedMatrix {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (_admitted : Admitted source provider) (type : TypeExpr) :=
  (MeTTaILPatternMatrixCompilation.Matrix.ofLanguage source.core).filter fun row =>
    rootInvocationGuard source.core provider type row.rule.val

theorem Admitted.sortedMatrix_occurrences {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (type : TypeExpr) :
    (admitted.sortedMatrix type).map OrderedPatternMatrixCompilation.Row.rule =
      (List.finRange source.core.rewrites.length).filter
        (fun occurrence => rootInvocationGuard source.core provider type occurrence.val) := by
  simp only [Admitted.sortedMatrix, MeTTaILPatternMatrixCompilation.Matrix.ofLanguage,
    List.filter_map, List.map_map]
  change ((List.finRange source.core.rewrites.length).filter
    (fun occurrence => rootInvocationGuard source.core provider type occurrence.val)).map id = _
  exact List.map_id _

/-- Compile the selected rows through the total wildcard-column compiler and
resolve each surviving leaf through its original source-indexed plan lookup. -/
def Admitted.sortedFusedProgram? {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (type : TypeExpr) :
    Option (OrderedDecisionRuleFusion.Program MeTTaILPatternMatrixCompilation.Matrix.Head
      (MeTTaILPatternMatrixCompilation.Matrix.RuleOccurrence source.core)
      MeTTaILFirstOrderRuleCompilation.RulePlan) :=
  OrderedDecisionRuleFusion.compileWildcard?
    (fun occurrence => some (admitted.program.planAt occurrence))
    (OrderedPatternMatrixWildcardColumnCompilation.compile (admitted.sortedMatrix type))

theorem Admitted.sortedFusedProgram_isSome {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (type : TypeExpr) :
    (admitted.sortedFusedProgram? type).isSome = true := by
  obtain ⟨program, compiled⟩ := OrderedDecisionRuleFusion.compileWildcard?_exists
    (fun occurrence => some (admitted.program.planAt occurrence))
    (fun occurrence => ⟨admitted.program.planAt occurrence, rfl⟩)
    (OrderedPatternMatrixWildcardColumnCompilation.compile (admitted.sortedMatrix type))
  simpa only [Admitted.sortedFusedProgram?, compiled] using (show (some program).isSome = true from rfl)

def Admitted.sortedFusedProgram {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (type : TypeExpr) :
    OrderedDecisionRuleFusion.Program MeTTaILPatternMatrixCompilation.Matrix.Head
      (MeTTaILPatternMatrixCompilation.Matrix.RuleOccurrence source.core)
      MeTTaILFirstOrderRuleCompilation.RulePlan :=
  (admitted.sortedFusedProgram? type).get (admitted.sortedFusedProgram_isSome type)

theorem Admitted.sortedFusedProgram?_eq_some {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (type : TypeExpr) :
    admitted.sortedFusedProgram? type = some (admitted.sortedFusedProgram type) :=
  (Option.some_get (admitted.sortedFusedProgram_isSome type)).symm

private theorem runMatrixAll_filter_rule {Head Rule Result : Type} [DecidableEq Head]
    (matrix : OrderedPatternMatrixCompilation.Matrix Head Rule) (selected : Rule → Bool)
    (attempt : Rule → List Result) (subjects : List (OrderedPatternMatrixCompilation.Subject Head)) :
    OrderedPatternMatrixCompilation.runMatrixAll attempt
        (matrix.filter fun row => selected row.rule) subjects =
      OrderedPatternMatrixCompilation.runMatrixAll
        (fun rule => if selected rule then attempt rule else []) matrix subjects := by
  induction matrix with
  | nil => rfl
  | cons row rows ih =>
    cases accepted : selected row.rule <;>
      cases structural : OrderedPatternMatrixCompilation.structuralMatchList row.patterns subjects <;>
      simp [accepted, OrderedPatternMatrixCompilation.runMatrixAll, structural, ih]

/-- The checked sort dispatch preserves the complete original-index emission
fold: captures, completed bindings, ordered query choices and target. -/
theorem Admitted.sortedFusedProgram_emissions {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (type : TypeExpr) (subject : Pattern) :
    (admitted.sortedFusedProgram type).evalAll
        (fun leaf => leaf.plan.runEmissions relations source.core leaf.occurrence.val subject)
        [MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject] =
      (List.finRange source.core.rewrites.length).flatMap fun occurrence =>
        if rootInvocationGuard source.core provider type occurrence.val then
          (admitted.program.planAt occurrence).runEmissions relations source.core occurrence.val subject
        else [] := by
  rw [OrderedDecisionRuleFusion.evalAll_eq_of_compileWildcard?
    (fun occurrence => some (admitted.program.planAt occurrence))
    (fun occurrence => (admitted.program.planAt occurrence).runEmissions
      relations source.core occurrence.val subject)
    (fun leaf => leaf.plan.runEmissions relations source.core leaf.occurrence.val subject)
    (by intro occurrence plan compiled; cases Option.some.inj compiled; rfl)
    _ _ (admitted.sortedFusedProgram?_eq_some type)]
  rw [OrderedPatternMatrixWildcardColumnCompilation.compile_all_correct]
  change OrderedPatternMatrixCompilation.runMatrixAll _
    ((MeTTaILPatternMatrixCompilation.Matrix.ofLanguage source.core).filter
      (fun row => rootInvocationGuard source.core provider type row.rule.val)) _ = _
  rw [runMatrixAll_filter_rule (MeTTaILPatternMatrixCompilation.Matrix.ofLanguage source.core)
    (fun occurrence => rootInvocationGuard source.core provider type occurrence.val)
    (fun occurrence => (admitted.program.planAt occurrence).runEmissions
      relations source.core occurrence.val subject)
    [MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject]]
  apply MeTTaILPatternMatrixCompilation.Matrix.runMatrixAll_ofLanguage_eq_occurrenceFold
  intro occurrence rejected
  have empty := MeTTaILPatternMatrixCompilation.Matrix.matchPattern_eq_nil_of_structural_rejection
    (MeTTaILPatternMatrixCompilation.Matrix.ruleAt source.core occurrence).left subject rejected
  have left : (admitted.program.planAt occurrence).left.erase =
      (MeTTaILPatternMatrixCompilation.Matrix.ruleAt source.core occurrence).left :=
    congrArg RewriteRule.left (admitted.program.erase_planAt occurrence)
  split
  · simp only [MeTTaILFirstOrderRuleCompilation.RulePlan.runEmissions,
      MeTTaILFirstOrderRuleCompilation.run_eq_matchPattern, left, empty, List.flatMap_nil]
  · rfl

/-- Every actual original-index emission stays in the existing first-order
compiler image when the admitted subject and provider payloads do. -/
theorem Admitted.emission_target_firstOrder {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider)
    (occurrence : Fin source.core.rewrites.length) (subject : Pattern)
    (subjectFirstOrder : Match.isMatchCorrectAux subject = true)
    (emission : MeTTaILFirstOrderRuleCompilation.RuleEmission Nat)
    (member : emission ∈ (admitted.program.planAt occurrence).runEmissions
      (providerRelEnv provider) source.core occurrence.val subject) :
    Match.isMatchCorrectAux emission.target = true := by
  have targetMember : emission.target ∈ (admitted.program.planAt occurrence).run
      (providerRelEnv provider) source.core subject := by
    rw [← MeTTaILFirstOrderRuleCompilation.RulePlan.runEmissions_targets
      (providerRelEnv provider) source.core occurrence.val (admitted.program.planAt occurrence) subject]
    exact List.mem_map_of_mem member
  exact MeTTaILFirstOrderRuleCompilation.RulePlan.run_firstOrder
    (providerRelEnv provider) source.core admitted.relations_firstOrder
    (admitted.program.planAt occurrence) subject subjectFirstOrder emission.target targetMember

private theorem firstOrder_of_compiler_scope_zero {pattern : Pattern}
    (image : Match.isMatchCorrectAux pattern = true) (scopeZero : pattern.isWellScopedAt 0 = true) :
    GeneralFirstOrderProjection.FirstOrder pattern := by
  induction pattern using Pattern.inductionOn with
  | hfvar name => exact .metavariable name
  | hbvar index => simp [Pattern.isWellScopedAt] at scopeZero
  | happly label arguments ih =>
    refine .constructor label arguments (fun argument member => ?_)
    have imageEach := (MatchSpec.isMatchCorrectListAux_iff_forall arguments).mp image
    have scopeEach := (ScopedPattern.isWellScopedListAt_eq_true_iff 0 arguments).mp scopeZero
    exact ih argument member (imageEach argument member) (scopeEach argument member)
  | hlambda | hmultiLambda | hsubst | hcollection => simp [Match.isMatchCorrectAux] at image

/-- Scope zero rules out the rigid bound-index nodes accepted by the compiler
image checker, yielding the stronger first-order subject predicate. -/
theorem Admitted.emission_target_firstOrder_of_scope_zero {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider)
    (occurrence : Fin source.core.rewrites.length) (subject : Pattern)
    (subjectFirstOrder : Match.isMatchCorrectAux subject = true)
    (emission : MeTTaILFirstOrderRuleCompilation.RuleEmission Nat)
    (member : emission ∈ (admitted.program.planAt occurrence).runEmissions
      (providerRelEnv provider) source.core occurrence.val subject)
    (scopeZero : emission.target.isWellScopedAt 0 = true) :
    GeneralFirstOrderProjection.FirstOrder emission.target :=
  firstOrder_of_compiler_scope_zero
    (admitted.emission_target_firstOrder occurrence subject subjectFirstOrder emission member) scopeZero

theorem Admitted.sortedFusedProgram_target_firstOrder {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider)
    (type : TypeExpr) (subject : Pattern) (subjectFirstOrder : Match.isMatchCorrectAux subject = true)
    (emission : MeTTaILFirstOrderRuleCompilation.RuleEmission Nat)
    (member : emission ∈ (admitted.sortedFusedProgram type).evalAll
      (fun leaf => leaf.plan.runEmissions (providerRelEnv provider) source.core leaf.occurrence.val subject)
      [MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject]) :
    Match.isMatchCorrectAux emission.target = true := by
  rw [admitted.sortedFusedProgram_emissions] at member
  obtain ⟨occurrence, _, emitted⟩ := List.mem_flatMap.mp member
  split at emitted
  · exact admitted.emission_target_firstOrder occurrence subject subjectFirstOrder emission emitted
  · cases emitted

theorem Admitted.sortedFusedProgram_target_firstOrder_of_scope_zero {source : Source}
    {provider : GeneralPremise.ProviderSnapshot} (admitted : Admitted source provider)
    (type : TypeExpr) (subject : Pattern) (subjectFirstOrder : Match.isMatchCorrectAux subject = true)
    (emission : MeTTaILFirstOrderRuleCompilation.RuleEmission Nat)
    (member : emission ∈ (admitted.sortedFusedProgram type).evalAll
      (fun leaf => leaf.plan.runEmissions (providerRelEnv provider) source.core leaf.occurrence.val subject)
      [MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject])
    (scopeZero : emission.target.isWellScopedAt 0 = true) :
    GeneralFirstOrderProjection.FirstOrder emission.target :=
  firstOrder_of_compiler_scope_zero
    (admitted.sortedFusedProgram_target_firstOrder type subject subjectFirstOrder emission member) scopeZero

private theorem map_filterMap_exact {α β : Type} (rows : List α) (compile : α → Option β)
    (readout : β → α) (total : ∀ row ∈ rows, ∃ plan, compile row = some plan)
    (faithful : ∀ row ∈ rows, ∀ plan, compile row = some plan → readout plan = row) :
    (rows.filterMap compile).map readout = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨plan, compiled⟩ := total row (by simp)
    simp only [List.filterMap_cons, compiled, List.map_cons]
    rw [faithful row (by simp) plan compiled]
    congr 1
    exact ih (fun entry member => total entry (by simp [member]))
      (fun entry member => faithful entry (by simp [member]))

/-- A complete authored admission plan retains every declaration and index in
order; coverage is stronger than membership of an admitted rule. -/
theorem Admitted.authored_rows {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) :
    ((rootPlan source.core provider).rules.map fun plan =>
      (plan.authored, plan.declarationIndex)) = source.core.rewrites.zipIdx := by
  let snapshot : GeneralExecutionAdmission.Snapshot := ⟨source.core, [], provider⟩
  have total : ∀ row ∈ source.core.rewrites.zipIdx,
      ∃ plan, GeneralExecutionAdmission.rulePlan? snapshot row.2 row.1 = some plan := by
    intro row member
    obtain ⟨plan, _, compiled⟩ := GeneralExecutionAdmission.complete_rule_coverage
      admitted.rootComplete member (by rfl)
    exact ⟨plan, compiled⟩
  have readout : ∀ row ∈ source.core.rewrites.zipIdx, ∀ plan,
      GeneralExecutionAdmission.rulePlan? snapshot row.2 row.1 = some plan →
        (plan.authored, plan.declarationIndex) = row := by
    intro row _ plan compiled
    obtain ⟨index, body, _⟩ := GeneralExecutionAdmission.rulePlan_readout compiled
    exact Prod.ext body index
  have result := map_filterMap_exact source.core.rewrites.zipIdx
    (fun row => GeneralExecutionAdmission.rulePlan? snapshot row.2 row.1)
    (fun plan => (plan.authored, plan.declarationIndex)) total readout
  simpa [rootPlan, GeneralExecutionAdmission.compile, GeneralExecutionAdmission.rules,
    GeneralExecutionAdmission.selectedRules, GeneralExecutionAdmission.selected, snapshot] using result

/-- The authored driver's ordinal is the original module declaration index. -/
theorem Admitted.authored_rule_at {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) {index : Nat} {plan : GeneralExecutionAdmission.RulePlan}
    (selected : (rootPlan source.core provider).rules[index]? = some plan) :
    source.core.rewrites[index]? = some plan.authored ∧ plan.declarationIndex = index := by
  have point := congrArg (fun rows => rows[index]?) admitted.authored_rows
  simp only [List.getElem?_map, selected, Option.map_some, List.getElem?_zipIdx, Nat.zero_add] at point
  cases declared : source.core.rewrites[index]? with
  | none => simp only [declared, Option.map_none, reduceCtorEq] at point
  | some rule =>
    have same : (plan.authored, plan.declarationIndex) = (rule, index) := by
      simpa only [declared, Option.map_some, Option.some.injEq] using point
    exact ⟨congrArg some (congrArg Prod.fst same).symm, congrArg Prod.snd same⟩

theorem Admitted.authored_origin {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) {index : Nat} {plan : GeneralExecutionAdmission.RulePlan}
    (selected : (rootPlan source.core provider).rules[index]? = some plan) :
    source.originAt? plan.declarationIndex = source.originAt? index := by
  rw [(admitted.authored_rule_at selected).2]

theorem Admitted.authored_exists_at {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) {index : Nat} {rule : RewriteRule}
    (declared : source.core.rewrites[index]? = some rule) :
    ∃ plan, (rootPlan source.core provider).rules[index]? = some plan ∧
      plan.authored = rule ∧ plan.declarationIndex = index := by
  have point := congrArg (fun rows => rows[index]?) admitted.authored_rows
  simp only [List.getElem?_map, List.getElem?_zipIdx, declared, Option.map_some, Nat.zero_add] at point
  cases selected : (rootPlan source.core provider).rules[index]? with
  | none => simp only [selected, Option.map_none, reduceCtorEq] at point
  | some plan =>
    have same : (plan.authored, plan.declarationIndex) = (rule, index) := by
      simpa only [selected, Option.map_some, Option.some.injEq] using point
    exact ⟨plan, rfl, congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- The provider-only profile excludes the engine's special `eq` query. This
follows from its existing premise law and exact source-to-plan row binding. -/
theorem Admitted.query_not_eq {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) {index : Nat} {rule : RewriteRule}
    (declared : source.core.rewrites[index]? = some rule) {relation : String} {arguments : List Pattern}
    (query : Premise.relationQuery relation arguments ∈ rule.premises) : relation ≠ "eq" := by
  obtain ⟨plan, selected, authored, _⟩ := admitted.authored_exists_at declared
  have executed : (environment source.core provider).language.rewrites[index]? = some plan.rule := by
    change ((rootPlan source.core provider).rules.map GeneralExecutionAdmission.RulePlan.rule)[index]? = _
    simp only [List.getElem?_map, selected, Option.map_some]
  have actualQuery : Premise.relationQuery relation arguments ∈ plan.rule.premises := by
    simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate,
      authored] using query
  have supported := (admitted.profile.firstOrder.rowFacts executed).premises _ actualQuery
  rcases supported with ⟨_, _, impossible, _, _⟩ | ⟨_, impossible, _⟩ | ⟨name, values, same, different, _⟩
  · cases impossible
  · cases impossible
  · cases same
    exact different

/-- Every admitted compiled query is an explicit provider query. The fact is
derived from original premises and complete source-to-plan erasure. -/
theorem Admitted.explicit_queries {source : Source} {provider : GeneralPremise.ProviderSnapshot}
    (admitted : Admitted source provider) (occurrence : Fin source.core.rewrites.length)
    (query : MeTTaILFirstOrderRuleCompilation.PremisePlan)
    (member : query ∈ (admitted.program.planAt occurrence).premises) : query.relation ≠ "eq" := by
  have erased : query.erase ∈ (admitted.program.planAt occurrence).erase.premises :=
    List.mem_map_of_mem member
  have original : query.erase ∈ source.core.rewrites[occurrence].premises :=
    congrArg RewriteRule.premises (admitted.program.erase_planAt occurrence) ▸ erased
  exact admitted.query_not_eq (List.getElem?_eq_getElem occurrence.isLt) original

theorem refuse_missing_declaration (source : Source) (provider : GeneralPremise.ProviderSnapshot)
    (missing : source.order.toFinset ≠ source.fragment) : admit? source provider = none := by
  cases checked : admit? source provider with
  | none => rfl
  | some admitted =>
    exact False.elim (missing (by rw [← admitted.order_eq]; exact admitted.view.covers))

theorem refuse_core_mismatch (source : Source) (provider : GeneralPremise.ProviderSnapshot)
    (mismatch : source.core.rewrites ≠ source.ruleRows) : admit? source provider = none := by
  cases admit? source provider with
  | none => rfl
  | some admitted => exact False.elim (mismatch admitted.rows_eq)

theorem refuse_equations (source : Source) (provider : GeneralPremise.ProviderSnapshot)
    (equations : source.core.equations ≠ []) : admit? source provider = none := by
  cases admit? source provider with
  | none => rfl
  | some admitted => exact False.elim (equations admitted.equationFree)

theorem refuse_unsupported_compilation (source : Source) (provider : GeneralPremise.ProviderSnapshot)
    (unsupported : MeTTaILFirstOrderRuleCompilation.compileProgram? source.core.rewrites = none) :
    admit? source provider = none := by
  apply (admit_none_iff_issues_nonempty source provider).mpr
  intro empty
  have accepted := (admit_isSome_iff source provider).mp
    ((admit_isSome_iff_issues_empty source provider).mpr empty)
  obtain ⟨_, _, _, _, _, _, _, _, compiled, _⟩ := accepted
  rw [unsupported] at compiled
  cases compiled

theorem refuse_provider_payload (source : Source) (provider : GeneralPremise.ProviderSnapshot)
    (unsupported : checkProviderFirstOrder provider = false) : admit? source provider = none := by
  cases checked : admit? source provider with
  | none => rfl
  | some admitted =>
    have accepted := admitted.providerFirstOrder
    rw [unsupported] at accepted
    cases accepted

namespace Controls

open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- The two equal-output declarations have different labels and origins. -/
def core : LanguageDef := languageDef! {
  name : "OrderedDuplicateZero"
  types { Nat }
  terms {
    NatZ . |- "z" : Nat;
    NatS . value:Nat |- "s" "(" value ")" : Nat;
    NatAdd . left:Nat, right:Nat |- "add" "(" left "," right ")" : Nat;
  }
  equations {}
  rewrites {
    AddZero . value:Nat |- (NatAdd (NatZ) value) ~> value;
    AddZeroAgain . value:Nat |- (NatAdd (NatZ) value) ~> value;
  }
}

def entries : List RuleEntry := core.rewrites.mapIdx fun index rule =>
  ⟨("ordered-module-control", "declaration:" ++ toString index), rule.name, rule⟩

def source : Source := ⟨"ordered-module-control-v1", .structuralView,
  entries.toFinset, entries, core⟩

def noProvider : GeneralPremise.ProviderSnapshot := ⟨[], []⟩

theorem duplicate_outputs_admitted : (admit? source noProvider).isSome = true := by
  rw [admit_isSome_iff]
  cbv
  decide

def checkedSource : Admitted source noProvider :=
  (admit? source noProvider).get duplicate_outputs_admitted

theorem distinct_origins : source.originAt? 0 ≠ source.originAt? 1 := by decide

def reversedCore : LanguageDef := { core with «rewrites» := core.rewrites.reverse }

def reversed : Source := {source with order := entries.reverse, core := reversedCore}

theorem reversed_order_admitted : (admit? reversed noProvider).isSome = true := by
  rw [admit_isSome_iff]
  cbv
  decide

theorem reversed_origin_order :
    reversed.originAt? 0 = source.originAt? 1 ∧ reversed.originAt? 1 = source.originAt? 0 := by decide

theorem stale_core_refused :
    admit? {source with order := entries.reverse} noProvider = none :=
  refuse_core_mismatch _ _ (by decide)

theorem missing_rule_refused : admit? {source with order := entries.tail} noProvider = none :=
  refuse_missing_declaration _ _ (by decide)

def queryRule : RewriteRule := {
  «name» := "Follow", typeContext := [("x", .base "Nat"), ("y", .base "Nat")]
  premises := [.relationQuery "next" [.fvar "x", .fvar "y"]]
  left := .apply "NatS" [.fvar "x"], right := .fvar "y" }

def queryCore : LanguageDef := {core with «rewrites» := [queryRule]}

def queryEntries : List RuleEntry := [⟨("ordered-query-control", "declaration:0"), "Follow", queryRule⟩]

def querySource : Source := ⟨"ordered-query-control-v1", .structuralView,
  queryEntries.toFinset, queryEntries, queryCore⟩

def duplicateProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[⟨"next", [.base "Nat", .base "Nat"], [.input, .output]⟩],
   [⟨"next", [.apply "NatZ" [], .apply "NatS" [.apply "NatZ" []]]⟩,
    ⟨"next", [.apply "NatZ" [], .apply "NatS" [.apply "NatZ" []]]⟩]⟩

theorem duplicate_provider_rows_admitted : (admit? querySource duplicateProvider).isSome = true := by
  rw [admit_isSome_iff]
  cbv
  decide

def checkedQuerySource : Admitted querySource duplicateProvider :=
  (admit? querySource duplicateProvider).get duplicate_provider_rows_admitted

theorem duplicate_provider_rows_retained : duplicateProvider.rows.length = 2 := rfl

def malformedProvider : GeneralPremise.ProviderSnapshot :=
  {duplicateProvider with rows := [⟨"next", [.apply "Undeclared" [], .apply "NatZ" []]⟩]}

theorem malformed_provider_refused : admit? querySource malformedProvider = none := by
  rw [admit_none_iff_issues_nonempty]
  cbv
  decide

theorem provider_change_refused (admitted : Admitted querySource duplicateProvider) :
    admitted.sameProvider noProvider = false :=
  admitted.provider_changed noProvider (by decide)

def nonlinearRule : RewriteRule := {
  «name» := "Same", typeContext := [("value", .base "Nat")], premises := []
  left := .apply "NatAdd" [.fvar "value", .fvar "value"], right := .fvar "value" }

def nonlinearCore : LanguageDef := {core with «rewrites» := [nonlinearRule]}

def nonlinearEntries : List RuleEntry :=
  [⟨("ordered-nonlinear-control", "declaration:0"), "Same", nonlinearRule⟩]

def nonlinearSource : Source := ⟨"ordered-nonlinear-control-v1", .structuralView,
  nonlinearEntries.toFinset, nonlinearEntries, nonlinearCore⟩

theorem nonlinear_rule_admitted : (admit? nonlinearSource noProvider).isSome = true := by
  rw [admit_isSome_iff]
  cbv
  decide

def withRule (rule : RewriteRule) : Source :=
  let row : RuleEntry := ⟨("unsupported-module-control", "declaration:0"), rule.name, rule⟩
  {source with fragment := [row].toFinset, order := [row], core := {core with «rewrites» := [rule]}}

def binderRule : RewriteRule := { nonlinearRule with
  left := .lambda none (.bvar 0), right := .lambda none (.bvar 0) }

theorem binder_refused : admit? (withRule binderRule) noProvider = none :=
  refuse_unsupported_compilation _ _ (by rfl)

def collectionRule : RewriteRule := { nonlinearRule with
  left := .collection .hashBag [.fvar "value"] none }

theorem collection_refused : admit? (withRule collectionRule) noProvider = none :=
  refuse_unsupported_compilation _ _ (by rfl)

def quantifiedRule : RewriteRule := { queryRule with
  premises := [.forAll "items" "item" (.relationQuery "next" [.fvar "x", .fvar "y"])] }

theorem quantified_premise_refused : admit? (withRule quantifiedRule) noProvider = none :=
  refuse_unsupported_compilation _ _ (by rfl)

def equalityRule : RewriteRule := {queryRule with
  premises := [.relationQuery "eq" [.fvar "x", .fvar "y"]]}

/-- An explicit row asserting unequal constructors cannot override builtin
equality under the existing provider-only query profile. -/
def equalityProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[⟨"eq", [.base "Nat", .base "Nat"], [.input, .output]⟩],
   [⟨"eq", [.apply "NatZ" [], .apply "NatS" [.apply "NatZ" []]]⟩]⟩

theorem builtin_equality_query_refused : admit? (withRule equalityRule) equalityProvider = none := by
  rw [admit_none_iff_issues_nonempty]
  cbv
  decide

theorem malformed_origin_refused : decodeOrigin? (.application "SyntaxOriginV1"
    [.string "source", .natural 0]) = none := rfl

theorem callable_origin_is_data :
    decodeOrigin? (originTerm ("(println! effect)", "declaration:0")) =
      some ("(println! effect)", "declaration:0") := rfl

theorem native_duplicate_rows_replay :
    (nativeOccurrencesTerm? source.order).bind decodeNativeOccurrences? = some source.order :=
  checkedSource.native_rows_roundTrip

/-- The same typed rows as the root-sort controls, submitted in the native
five-field representation without explicit binding annotations. -/
def mixedCore : LanguageDef :=
  {RootSortControls.mixedLanguage with «rewrites» :=
    RootSortControls.mixedLanguage.rewrites.map fun rule => {rule with bindings := none}}

def mixedEntries : List RuleEntry := mixedCore.rewrites.mapIdx fun index rule =>
  ⟨("mixed-sort-module", "declaration:" ++ toString index), rule.name, rule⟩

def mixedSource : Source := ⟨"mixed-sort-module-v1", .structuralView,
  mixedEntries.toFinset, mixedEntries, mixedCore⟩

theorem mixed_query_profile : checkQueryProfileFacts mixedSource.core noProvider = true := by
  change checkQueryProfileFacts mixedCore noProvider = true
  cbv

theorem wildcard_module_admitted : (admit? mixedSource noProvider).isSome = true := by
  rw [admit_isSome_iff]
  simp only [true_and, Source.checkCompatible, Source.ruleRows, mixedSource]
  cbv
  decide

def checkedMixedSource : Admitted mixedSource noProvider :=
  (admit? mixedSource noProvider).get wildcard_module_admitted

theorem sorted_nat_original_indices :
    ((checkedMixedSource.sortedMatrix (.base "Nat")).map
      (fun row => row.rule.val)) = [0, 2, 3] := by
  unfold Admitted.sortedMatrix
  simp only [mixedSource]
  cbv

theorem sorted_bool_original_index :
    ((checkedMixedSource.sortedMatrix (.base "Bool")).map
      (fun row => row.rule.val)) = [1] := by
  unfold Admitted.sortedMatrix
  simp only [mixedSource]
  cbv

theorem undeclared_sort_has_no_rows : checkedMixedSource.sortedMatrix (.base "Other") = [] := by
  unfold Admitted.sortedMatrix
  simp only [mixedSource]
  cbv

open MeTTaILFirstOrderRuleCompilation Match

private theorem emissions_without_premises (relations : Engine.RelationEnv) (language : LanguageDef)
    (plan : RulePlan) (premiseFree : plan.erase.premises = []) (ordinal : Nat) (subject : Pattern) :
    plan.runEmissions relations language ordinal subject =
      (matchPattern plan.erase.left subject).map fun initial =>
        ⟨ordinal, initial, initial, [], applyBindings initial plan.erase.right⟩ := by
  have noPremises : plan.premises = [] := by
    cases pending : plan.premises with
    | nil => rfl
    | cons query rest => simp [RulePlan.erase, erasePremisePlans, pending] at premiseFree
  simp [RulePlan.runEmissions, run_eq_matchPattern, noPremises, runPremiseReceipts,
    RulePlan.erase, instantiate_eq_applyBindings]
  exact List.map_eq_flatMap.symm

private theorem mixed_plan_emissions (occurrence : Fin mixedSource.core.rewrites.length)
    (subject : Pattern) :
    (checkedMixedSource.program.planAt occurrence).runEmissions
        (providerRelEnv noProvider) mixedSource.core occurrence.val subject =
      (matchPattern mixedSource.core.rewrites[occurrence].left subject).map fun initial =>
        ⟨occurrence.val, initial, initial, [], applyBindings initial mixedSource.core.rewrites[occurrence].right⟩ := by
  have premiseFree : (checkedMixedSource.program.planAt occurrence).erase.premises = [] := by
    rw [checkedMixedSource.program.erase_planAt]
    fin_cases occurrence <;> rfl
  rw [emissions_without_premises _ _ _ premiseFree,
    checkedMixedSource.program.erase_planAt]

def mixedEmissions (type : TypeExpr) (subject : Pattern) :
    List (MeTTaILFirstOrderRuleCompilation.RuleEmission Nat) :=
  (checkedMixedSource.sortedFusedProgram type).evalAll
    (fun leaf => leaf.plan.runEmissions (providerRelEnv noProvider) mixedSource.core leaf.occurrence.val subject)
    [MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject]

/-- The actual compiled artifact emits duplicate values at their original
indices while retaining each complete capture and receipt. -/
theorem sorted_nat_full_emissions : mixedEmissions (.base "Nat") (.apply "NZero" []) =
    [{ origin := 0, initialBindings := [("x", .apply "NZero" [])],
       bindings := [("x", .apply "NZero" [])], choices := [], target := .apply "NZero" [] },
     { origin := 2, initialBindings := [], bindings := [], choices := [],
       target := .apply "NSucc" [.apply "NZero" []] },
     { origin := 3, initialBindings := [("x", .apply "NZero" [])],
       bindings := [("x", .apply "NZero" [])], choices := [], target := .apply "NZero" [] }] := by
  unfold mixedEmissions
  rw [checkedMixedSource.sortedFusedProgram_emissions]
  simp_rw [mixed_plan_emissions]
  simp only [mixedSource]
  cbv

theorem sorted_bool_full_emission : mixedEmissions (.base "Bool") (.apply "BoolF" []) =
    [{ origin := 1, initialBindings := [("b", .apply "BoolF" [])],
       bindings := [("b", .apply "BoolF" [])], choices := [], target := .apply "BoolF" [] }] := by
  unfold mixedEmissions
  rw [checkedMixedSource.sortedFusedProgram_emissions]
  simp_rw [mixed_plan_emissions]
  simp only [mixedSource]
  cbv

theorem other_sort_has_no_emissions : mixedEmissions (.base "Other") (.apply "NZero" []) = [] := by
  unfold mixedEmissions
  rw [checkedMixedSource.sortedFusedProgram_emissions]
  simp_rw [mixed_plan_emissions]
  simp only [mixedSource]
  cbv

theorem constructor_provider_payloads : checkProviderFirstOrder duplicateProvider = true := by cbv

open private ClosureControls.escapingPayload from
  Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

def typedEscapeRule : RewriteRule :=
  { «name» := "TypedProviderEscape", typeContext := [("x", .arrow (.base "Nat") (.base "Nat"))],
    premises := [.relationQuery "value" [.fvar "x"]],
    left := .apply "Start" [], right := .apply "Box" [.fvar "x"] }

def typedEscapeCore : LanguageDef :=
  LanguageDef.ofCore "TypedProviderEscape" ["Nat", "Carrier"]
    (core.terms ++
      [{ label := "Start", category := "Carrier", params := [], syntaxPattern := [] },
       { label := "Box", category := "Carrier", params :=
           [.simple "function" (.arrow (.base "Nat") (.base "Nat"))],
         syntaxPattern := [.nonTerminal "function"] }]) [] [typedEscapeRule]

def typedEscapeEntries : List RuleEntry :=
  [⟨("typed-provider-escape", "declaration:0"), typedEscapeRule.name, typedEscapeRule⟩]

def typedEscapeSource : Source := ⟨"typed-provider-escape-v1", .structuralView,
  typedEscapeEntries.toFinset, typedEscapeEntries, typedEscapeCore⟩

def typedLambdaProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[⟨"value", [.arrow (.base "Nat") (.base "Nat")], [.output]⟩],
    [⟨"value", [ClosureControls.escapingPayload.eraseBinderMetadata]⟩]⟩

/-- Typing and closedness permit this value; the literal syntax check supplies
the independent first-order boundary. -/
theorem lambda_payload_typed_closed :
    GeneralPremise.checkProviderClosed typedEscapeCore (fun _ => none) typedLambdaProvider = true := by cbv

theorem lambda_payload_refused : checkProviderFirstOrder typedLambdaProvider = false := by cbv

theorem typed_lambda_source_refused : admit? typedEscapeSource typedLambdaProvider = none :=
  refuse_provider_payload _ _ lambda_payload_refused

/-- Every former source/provider check succeeds; the new payload refusal is
the sole diagnostic and preserves the submitted source and snapshot. -/
theorem typed_lambda_only_issue : issues typedEscapeSource typedLambdaProvider =
    [.nonFirstOrderProviderPayload] := by
  unfold issues sourceIssues Source.checkCompatible Source.ruleRows
  simp only [typedEscapeSource]
  cbv

def typedEscapePlan : RulePlan :=
  { «name» := "TypedProviderEscape", typeContext := [("x", .arrow (.base "Nat") (.base "Nat"))],
    premises := [⟨"value", [.metavariable "x"]⟩], left := .application "Start" [],
    right := .application "Box" [.metavariable "x"] }

theorem typed_escape_plan_compiles : compileRule? typedEscapeRule = some typedEscapePlan := by cbv

/-- Without the literal-row condition, this typed first-order rule would
return a lambda beneath an ordinary constructor from a first-order source. -/
theorem unchecked_typed_provider_escapes :
    typedEscapePlan.run (providerRelEnv typedLambdaProvider) typedEscapeCore (.apply "Start" []) =
      [.apply "Box" [ClosureControls.escapingPayload.eraseBinderMetadata]] := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OrderedFirstOrderAdmission
