import Mettapedia.OSLF.MeTTaIL.TypedContextualEquationExecution
import Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier
import Mettapedia.OSLF.Framework.GeneralReferenceAgreement

/-!
# Authored conditional equations and reductions at typed licensed sites

Every supplied site is a real typed zipper into the current source. Equations
are enumerated in both orientations and remain separate from primitive rule
occurrences. The same resumable frontier consumes both finite enumerations.
Site-generation obligations are copied into both phases and survive exhaustion
of the representative queue. A supplied finite site list alone does not assert
coverage of the operational permission profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open ScopedEquationExecution (Orientation orientedRule)
open TypedContextualEquationExecution (Site)

inductive SiteGenerationIssue where
  | unexploredContext (context : OneHoleContext)
  | unavailableTyping
  | uncertifiedCoverage
deriving Repr, DecidableEq

/-- Generation retains proved sites and concrete unfinished work. Coverage
is earned separately against the licensed typed-site judgment. -/
structure GeneratedSites (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern) where
  sites : List (Site language free bound expected permissions source)
  unresolved : List SiteGenerationIssue

/-- The actual root generator checks the complete object carrier. Non-root
permissions remain pending instead of being silently discarded. -/
def rootSites (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern) : GeneratedSites language free bound expected permissions source :=
  if sorted : checkOpenPatternWellSorted language free bound expected source = true then
    { sites := if permitted : OneHoleContext.hole ∈ permissions then
        [Site.root (checkOpenPatternWellSorted_sound sorted).1 permitted] else []
      unresolved := (permissions.filter (fun context => context != .hole)).map
        SiteGenerationIssue.unexploredContext }
  else ⟨[], [.unavailableTyping]⟩

theorem rootSites_has_root (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern)
    (sorted : checkOpenPatternWellSorted language free bound expected source = true)
    (permitted : OneHoleContext.hole ∈ permissions) :
    ∃ site ∈ (rootSites language free bound expected permissions source).sites,
      site.context = .hole ∧ site.focus = source ∧
        site.focusBound = bound ∧ site.focusType = expected := by
  simp [rootSites, sorted, permitted, Site.root]

theorem rootSites_nonroot_pending (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern)
    (sorted : checkOpenPatternWellSorted language free bound expected source = true)
    (context : OneHoleContext) (permitted : context ∈ permissions)
    (nonroot : context ≠ .hole) :
    SiteGenerationIssue.unexploredContext context ∈
      (rootSites language free bound expected permissions source).unresolved := by
  simp [rootSites, sorted, List.mem_filter, permitted, nonroot]

theorem rootSites_unavailable (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern)
    (rejected : checkOpenPatternWellSorted language free bound expected source ≠ true) :
    (rootSites language free bound expected permissions source).sites = [] ∧
      (rootSites language free bound expected permissions source).unresolved = [.unavailableTyping] := by
  simp [rootSites, rejected]

/-- This is a mathematical coverage predicate, not an input field accepted
by execution. Concrete site generators must prove it on their admitted profile. -/
def SitesCover (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source) : Prop :=
  ∀ site : Site language free bound expected permissions source,
    ∃ contextIndex, (site, contextIndex) ∈ generated.sites.zipIdx

theorem root_only_site_unique (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (typed : HasType language free bound source expected)
    (site : Site language free bound expected [.hole] source) :
    site = Site.root typed (by simp) := by
  have context : site.context = .hole := by simpa using site.permitted
  have indices := TypedAt.hole_indices (context ▸ site.typed)
  have focus : site.focus = source := by simpa [context] using site.source_eq
  cases site
  simp_all [Site.root]

/-- The root generator earns complete typed-site coverage for every object
term of any language with the root-only operational permission profile. -/
theorem rootSites_covers_root_only (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (sorted : checkOpenPatternWellSorted language free bound expected source = true) :
    SitesCover language free bound expected [.hole] source
      (rootSites language free bound expected [.hole] source) := by
  intro site
  refine ⟨0, ?_⟩
  rw [root_only_site_unique language free bound expected source
    (checkOpenPatternWellSorted_sound sorted).1 site]
  simp [rootSites, sorted]

theorem rootSites_root_only_resolved (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (sorted : checkOpenPatternWellSorted language free bound expected source = true) :
    (rootSites language free bound expected [.hole] source).unresolved = [] := by
  simp [rootSites, sorted]

structure EquationOrigin where
  equationIndex : Nat
  orientation : Orientation
  contextual : TypedContextualEquationExecution.Receipt
deriving Repr, DecidableEq

inductive Obligation where
  | siteGeneration (reason : SiteGenerationIssue)
  | equation (contextIndex equationIndex : Nat) (context : OneHoleContext)
      (orientation : Orientation) (reason : ConditionalEquationExecution.Pending)
  | primitive (contextIndex ruleIndex : Nat) (context : OneHoleContext)
      (reason : ConditionalEquationExecution.Pending)
deriving Repr, DecidableEq

structure EquationOutcome where
  receipts : List EquationOrigin
  pending : List Obligation
deriving Repr, DecidableEq

structure RuleOutcome where
  receipts : List TypedContextualEquationExecution.Receipt
  pending : List Obligation
deriving Repr, DecidableEq

def applyEquationAt (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (site : Site language free bound expected permissions source) : EquationOutcome :=
  let result := TypedContextualEquationExecution.applyAt relEnv language free bound expected
    permissions source contextIndex equationIndex (orientedRule equation orientation) site
  { receipts := result.receipts.map fun contextual => ⟨equationIndex, orientation, contextual⟩
    pending := result.pending.map fun blocked =>
      .equation blocked.contextIndex equationIndex blocked.context orientation blocked.reason }

def executeEquations (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source) : EquationOutcome :=
  let results := generated.sites.zipIdx.flatMap fun (site, contextIndex) =>
    language.equations.zipIdx.flatMap fun (equation, equationIndex) =>
      [Orientation.forward, Orientation.reverse].map fun orientation =>
        applyEquationAt relEnv language free bound expected permissions source
          contextIndex equationIndex equation orientation site
  { receipts := results.flatMap EquationOutcome.receipts
    pending := generated.unresolved.map Obligation.siteGeneration ++
      results.flatMap EquationOutcome.pending }

def executeRules (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source) : RuleOutcome :=
  let result := TypedContextualEquationExecution.executeSites relEnv language free bound expected
    permissions source generated.sites
  { receipts := result.receipts
    pending := generated.unresolved.map Obligation.siteGeneration ++
      result.pending.map fun blocked =>
        .primitive blocked.contextIndex blocked.ruleIndex blocked.context blocked.reason }

/-- A proof-side view keeps receipt geometry separate from the independently
judged atomic evidence. The executable default keeps its original receipt. -/
structure ContextualEvidence (Receipt : Type) where
  contextIndex : Receipt → Nat
  context : Receipt → OneHoleContext
  focusBound : Receipt → List TypeExpr
  focusType : Receipt → TypeExpr
  declarationIndex : Receipt → Nat
  localTarget : Receipt → Pattern
  target : Receipt → Pattern
  atomic : Engine.RelationEnv → LanguageDef → FreeTypeContext → List TypeExpr → TypeExpr →
    Nat → RewriteRule → Pattern → Receipt → Prop

/-- The existing query-only atomic judgment remains the default. -/
def conditionalEvidence : ContextualEvidence TypedContextualEquationExecution.Receipt where
  contextIndex := TypedContextualEquationExecution.Receipt.contextIndex
  context := TypedContextualEquationExecution.Receipt.context
  focusBound := TypedContextualEquationExecution.Receipt.focusBound
  focusType := TypedContextualEquationExecution.Receipt.focusType
  declarationIndex := TypedContextualEquationExecution.Receipt.ruleIndex
  localTarget := fun receipt => receipt.atomic.target
  target := TypedContextualEquationExecution.Receipt.target
  atomic := fun relEnv language free bound expected _ rule source receipt =>
    ConditionalEquationExecution.RuleInstance relEnv language free bound expected rule source receipt.atomic

/-- The original rule witness is independent of the retained execution receipt.
Its actual indexed source declaration and typed local endpoint are required. -/
def referenceEvidence : ContextualEvidence (Nat × GeneralRuleJobs.Receipt × ReferenceStep.Witness) where
  contextIndex := Prod.fst
  context := fun framed => framed.2.1.job.site.context
  focusBound := fun framed => framed.2.1.job.site.focusBound
  focusType := fun framed => framed.2.1.job.site.focusType
  declarationIndex := fun framed => framed.2.1.job.declaration.declarationIndex
  localTarget := fun framed => framed.2.1.localTarget
  target := fun framed => framed.2.1.target
  atomic := fun relEnv language free bound expected index rule source framed =>
    language.rewrites[index]? = some rule ∧
      OpenPatternWellSorted language free bound expected framed.2.1.localTarget ∧
      (∃ bindings witnesses, framed.2.2 = .rule index bindings witnesses) ∧
      ReferenceStep.StepValid relEnv language source framed.2.2 framed.2.1.localTarget

/-- A filled atomic instance is judged independently of contextual execution.
The actual indexed root derivation and exact zipper fill are both retained. -/
inductive ContextualInstance (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex declarationIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source)
    {Receipt : Type} (receipt : Receipt)
    (evidence : ContextualEvidence Receipt := by exact conditionalEvidence) : Prop where
  | fill (contextOrigin : evidence.contextIndex receipt = contextIndex)
      (context : evidence.context receipt = site.context)
      (focusBound : evidence.focusBound receipt = site.focusBound)
      (focusType : evidence.focusType receipt = site.focusType)
      (declaration : evidence.declarationIndex receipt = declarationIndex)
      (atomic : evidence.atomic relEnv language free site.focusBound site.focusType
        declarationIndex rule site.focus receipt)
      (target : evidence.target receipt = site.context.fill (evidence.localTarget receipt))
      (scoping : (evidence.target receipt).isWellScopedAt bound.length = true)
      (typing : HasType language free bound (evidence.target receipt) expected) :
      ContextualInstance relEnv language free bound expected permissions source
        contextIndex declarationIndex rule site (evidence := evidence) receipt

/-- The default evidence view has exactly the original query-only judgment
and receipt fields. General evidence adds no default execution cases. -/
theorem ContextualInstance.conditional_iff (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex declarationIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source)
    (receipt : TypedContextualEquationExecution.Receipt) :
    ContextualInstance relEnv language free bound expected permissions source
      contextIndex declarationIndex rule site receipt ↔
    receipt.contextIndex = contextIndex ∧ receipt.context = site.context ∧
      receipt.focusBound = site.focusBound ∧ receipt.focusType = site.focusType ∧
      receipt.ruleIndex = declarationIndex ∧
      ConditionalEquationExecution.RuleInstance relEnv language free site.focusBound site.focusType
        rule site.focus receipt.atomic ∧
      receipt.target = site.context.fill receipt.atomic.target ∧
      receipt.target.isWellScopedAt bound.length = true ∧
      HasType language free bound receipt.target expected := by
  constructor
  · intro valid
    cases valid with
    | fill origin context focusBound focusType declaration atomic target scoping typing =>
        exact ⟨origin, context, focusBound, focusType, declaration, atomic, target, scoping, typing⟩
  · rintro ⟨origin, context, focusBound, focusType, declaration, atomic, target, scoping, typing⟩
    exact .fill origin context focusBound focusType declaration atomic target scoping typing

/-- Changing selected reduction rows leaves the same typed occurrence zipper. -/
theorem typedAt_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {focus : Pattern} {context : OneHoleContext}
    {bound focusBound : List TypeExpr} {expected focusType : TypeExpr}
    (typed : TypedAt first free focus context bound expected focusBound focusType) :
    TypedAt second free focus context bound expected focusBound focusType := by
  induction typed with
  | here focusTyped => exact .here (GeneralLanguageTyping.type_transport same focusTyped)
  | application declared ordinary arguments parameters beforeLength parameter inner ih =>
      exact .application (same ▸ declared) ordinary
        (GeneralLanguageTyping.arguments_transport same arguments) parameters beforeLength parameter ih
  | lambda inner ih => exact .lambda ih
  | multiLambda inner ih => exact .multiLambda ih
  | substBody replacement inner ih =>
      exact .substBody (GeneralLanguageTyping.type_transport same replacement) ih
  | substReplacement body inner ih =>
      exact .substReplacement (GeneralLanguageTyping.type_transport same body) ih
  | collection elements inner ih =>
      exact .collection (GeneralLanguageTyping.elements_transport same elements) ih
  | collectionConstructor declared shape elements inner ih =>
      exact .collectionConstructor (same ▸ declared) shape
        (GeneralLanguageTyping.elements_transport same elements) ih


/-- Original grammar equality transports the complete licensed site data,
including declaration positions and retained typing alternatives. -/
theorem licensed_transport {first second : LanguageDef} (same : first.terms = second.terms)
    {free : FreeTypeContext} {permissions : GeneralTypedSites.OperationalPermissions}
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : GeneralTypedSites.SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
      first free permissions bound expected source site) :
    Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
      second free permissions bound expected source site := by
  induction licensed with
  | here enabled object typed =>
      exact .here enabled object (GeneralLanguageTyping.type_transport same typed)
  | application declared ordinary arguments objects selected parameterSelected parameterTyped permitted child ih =>
      exact .application (same ▸ declared) ordinary
        (GeneralLanguageTyping.arguments_transport same arguments) objects selected parameterSelected
        parameterTyped permitted ih
  | lambda permitted child ih => exact .lambda permitted ih
  | multiLambda permitted child ih => exact .multiLambda permitted ih
  | directCollection permitted elements objects selected child ih =>
      exact .directCollection permitted (GeneralLanguageTyping.elements_transport same elements)
        objects selected ih
  | authoredCollection declared shape permitted elements objects selected child ih =>
      exact .authoredCollection (same ▸ declared) shape permitted
        (GeneralLanguageTyping.elements_transport same elements) objects selected ih


theorem contextual_sound (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex declarationIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source)
    (receipt : TypedContextualEquationExecution.Receipt)
    (member : receipt ∈ (TypedContextualEquationExecution.applyAt relEnv language free
      bound expected permissions source contextIndex declarationIndex rule site).receipts) :
    ContextualInstance relEnv language free bound expected permissions source
      contextIndex declarationIndex rule site receipt := by
  obtain ⟨atomic, atomicMember, origin, context, focusBound, focusType, declaration,
    atomicEq, target, scoping, typing⟩ :=
    TypedContextualEquationExecution.applyAt_readout relEnv language free bound expected
      permissions source contextIndex declarationIndex rule site receipt member
  have instanceReadout := ConditionalEquationExecution.applyRuleAtOutcome_sound relEnv language
    free site.focusBound site.focusType rule site.focus atomic atomicMember
  rw [← atomicEq] at instanceReadout target
  exact .fill origin context focusBound focusType declaration instanceReadout target scoping typing

theorem contextual_complete (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex declarationIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source)
    (receipt : TypedContextualEquationExecution.Receipt)
    (supported : ∀ spec, rule.bindings = some spec →
      ConditionalEquationExecution.queriesSupported spec 0 rule.premises = true)
    (object : isObjectPattern receipt.target = true)
    (hinstance : ContextualInstance relEnv language free bound expected permissions source
      contextIndex declarationIndex rule site receipt) :
    receipt ∈ (TypedContextualEquationExecution.applyAt relEnv language free bound expected
      permissions source contextIndex declarationIndex rule site).receipts := by
  cases hinstance with
  | fill origin context focusBound focusType declaration atomic target scoping typing =>
      dsimp only [conditionalEvidence] at origin context focusBound focusType declaration atomic target scoping typing
      have atomicMember := ConditionalEquationExecution.applyRuleAtOutcome_complete relEnv language
        free site.focusBound site.focusType rule site.focus receipt.atomic supported atomic
      have checked := checkHasType_complete_of_object typing object
      simp only [TypedContextualEquationExecution.applyAt, List.mem_filterMap]
      refine ⟨receipt.atomic, atomicMember, ?_⟩
      unfold TypedContextualEquationExecution.fillReceipt?
      rw [← target]
      dsimp only
      rw [scoping, checked]
      simp only [Bool.and_self, if_true]
      cases receipt
      simp_all

def EquationInstance (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (site : Site language free bound expected permissions source) (origin : EquationOrigin) : Prop :=
  origin.equationIndex = equationIndex ∧ origin.orientation = orientation ∧
    ContextualInstance relEnv language free bound expected permissions source contextIndex
      equationIndex (orientedRule equation orientation) site origin.contextual

theorem applyEquationAt_sound (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (site : Site language free bound expected permissions source) (origin : EquationOrigin)
    (member : origin ∈ (applyEquationAt relEnv language free bound expected permissions source
      contextIndex equationIndex equation orientation site).receipts) :
    EquationInstance relEnv language free bound expected permissions source contextIndex
      equationIndex equation orientation site origin := by
  simp only [applyEquationAt, List.mem_map] at member
  obtain ⟨receipt, receiptMember, represented⟩ := member
  cases represented
  exact ⟨rfl, rfl, contextual_sound relEnv language free bound expected permissions source
    contextIndex equationIndex (orientedRule equation orientation) site receipt receiptMember⟩

theorem applyEquationAt_complete (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex equationIndex : Nat) (equation : Equation) (orientation : Orientation)
    (site : Site language free bound expected permissions source) (origin : EquationOrigin)
    (supported : ∀ spec, (orientedRule equation orientation).bindings = some spec →
      ConditionalEquationExecution.queriesSupported spec 0 equation.premises = true)
    (object : isObjectPattern origin.contextual.target = true)
    (hinstance : EquationInstance relEnv language free bound expected permissions source
      contextIndex equationIndex equation orientation site origin) :
    origin ∈ (applyEquationAt relEnv language free bound expected permissions source
      contextIndex equationIndex equation orientation site).receipts := by
  obtain ⟨declaration, direction, interpreted⟩ := hinstance
  have present := contextual_complete relEnv language free bound expected permissions source
    contextIndex equationIndex (orientedRule equation orientation) site origin.contextual
    (by simpa only [ScopedEquationExecution.orientedRule_premises] using supported)
    object interpreted
  simp only [applyEquationAt, List.mem_map]
  refine ⟨origin.contextual, present, ?_⟩
  cases origin
  simp_all

theorem executeEquations_sound (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source) (origin : EquationOrigin)
    (member : origin ∈ (executeEquations relEnv language free bound expected permissions source generated).receipts) :
    ∃ site contextIndex equation equationIndex orientation,
      (site, contextIndex) ∈ generated.sites.zipIdx ∧
      (equation, equationIndex) ∈ language.equations.zipIdx ∧
      EquationInstance relEnv language free bound expected permissions source contextIndex
        equationIndex equation orientation site origin := by
  simp only [executeEquations, List.mem_flatMap, List.mem_map] at member
  obtain ⟨result, ⟨⟨site, contextIndex⟩, siteMember, ⟨equation, equationIndex⟩,
    declared, orientation, _, represented⟩, firing⟩ := member
  cases represented
  exact ⟨site, contextIndex, equation, equationIndex, orientation, siteMember, declared,
    applyEquationAt_sound relEnv language free bound expected permissions source
      contextIndex equationIndex equation orientation site origin firing⟩

/-- Completeness covers the complete firing receipt at an actual generated
site and authored declaration, rather than merely its endpoint. -/
theorem executeEquations_complete (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source)
    (site : Site language free bound expected permissions source) (contextIndex : Nat)
    (selected : (site, contextIndex) ∈ generated.sites.zipIdx)
    (equation : Equation) (equationIndex : Nat)
    (declared : (equation, equationIndex) ∈ language.equations.zipIdx)
    (orientation : Orientation) (origin : EquationOrigin)
    (supported : ∀ spec, (orientedRule equation orientation).bindings = some spec →
      ConditionalEquationExecution.queriesSupported spec 0 equation.premises = true)
    (object : isObjectPattern origin.contextual.target = true)
    (hinstance : EquationInstance relEnv language free bound expected permissions source
      contextIndex equationIndex equation orientation site origin) :
    origin ∈ (executeEquations relEnv language free bound expected permissions source generated).receipts := by
  have orientationPresent : orientation ∈ [Orientation.forward, Orientation.reverse] := by
    cases orientation <;> simp
  have present := applyEquationAt_complete relEnv language free bound expected permissions source
    contextIndex equationIndex equation orientation site origin supported object hinstance
  simp only [executeEquations, List.mem_flatMap, List.mem_map]
  exact ⟨_, ⟨(site, contextIndex), selected, (equation, equationIndex), declared,
    orientation, orientationPresent, rfl⟩, present⟩

theorem executeRules_sound (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source)
    (receipt : TypedContextualEquationExecution.Receipt)
    (member : receipt ∈ (executeRules relEnv language free bound expected permissions source generated).receipts) :
    ∃ site contextIndex rule ruleIndex,
      (site, contextIndex) ∈ generated.sites.zipIdx ∧
      (rule, ruleIndex) ∈ language.rewrites.zipIdx ∧
      ContextualInstance relEnv language free bound expected permissions source
        contextIndex ruleIndex rule site receipt := by
  obtain ⟨site, contextIndex, rule, ruleIndex, selected, declared, firing⟩ :=
    TypedContextualEquationExecution.executeSites_readout relEnv language free bound expected
      permissions source generated.sites receipt member
  exact ⟨site, contextIndex, rule, ruleIndex, selected, declared,
    contextual_sound relEnv language free bound expected permissions source
      contextIndex ruleIndex rule site receipt firing⟩

theorem executeRules_complete (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (generated : GeneratedSites language free bound expected permissions source)
    (site : Site language free bound expected permissions source) (contextIndex : Nat)
    (selected : (site, contextIndex) ∈ generated.sites.zipIdx)
    (rule : RewriteRule) (ruleIndex : Nat)
    (declared : (rule, ruleIndex) ∈ language.rewrites.zipIdx)
    (receipt : TypedContextualEquationExecution.Receipt)
    (supported : ∀ spec, rule.bindings = some spec →
      ConditionalEquationExecution.queriesSupported spec 0 rule.premises = true)
    (object : isObjectPattern receipt.target = true)
    (hinstance : ContextualInstance relEnv language free bound expected permissions source
      contextIndex ruleIndex rule site receipt) :
    receipt ∈ (executeRules relEnv language free bound expected permissions source generated).receipts := by
  have present := contextual_complete relEnv language free bound expected permissions source
    contextIndex ruleIndex rule site receipt supported object hinstance
  simp only [executeRules, TypedContextualEquationExecution.executeSites,
    List.mem_flatMap, List.mem_map]
  exact ⟨_, ⟨(site, contextIndex), selected, (rule, ruleIndex), declared, rfl⟩, present⟩

/-- The shared queue receives distinct equation and primitive providers.
Every generation/root obligation remains attached to its processing phase. -/
def model (relEnv : Engine.RelationEnv) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (generate : ∀ source, GeneratedSites language free bound expected permissions source) :
    Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.Model Pattern
      EquationOrigin TypedContextualEquationExecution.Receipt Obligation where
  equations source :=
    let result := executeEquations relEnv language free bound expected permissions source (generate source)
    ⟨result.receipts.map (fun origin => (origin, origin.contextual.target)), result.pending⟩
  firings source :=
    let result := executeRules relEnv language free bound expected permissions source (generate source)
    ⟨result.receipts.map (fun receipt => (receipt, receipt.target)), result.pending⟩

theorem model_equations_sound (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext)
    (generate : ∀ source, GeneratedSites language free bound expected permissions source)
    (source target : Pattern) (origin : EquationOrigin)
    (member : (origin, target) ∈
      ((model relEnv language free bound expected permissions generate).equations source).answers) :
    target = origin.contextual.target ∧
      ∃ site contextIndex equation equationIndex orientation,
        (site, contextIndex) ∈ (generate source).sites.zipIdx ∧
        (equation, equationIndex) ∈ language.equations.zipIdx ∧
        EquationInstance relEnv language free bound expected permissions source contextIndex
          equationIndex equation orientation site origin := by
  simp only [model, List.mem_map] at member
  obtain ⟨actual, present, represented⟩ := member
  cases represented
  exact ⟨rfl, executeEquations_sound relEnv language free bound expected permissions source
    (generate source) origin present⟩

theorem model_firings_sound (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext)
    (generate : ∀ source, GeneratedSites language free bound expected permissions source)
    (source target : Pattern) (receipt : TypedContextualEquationExecution.Receipt)
    (member : (receipt, target) ∈
      ((model relEnv language free bound expected permissions generate).firings source).answers) :
    target = receipt.target ∧
      ∃ site contextIndex rule ruleIndex,
        (site, contextIndex) ∈ (generate source).sites.zipIdx ∧
        (rule, ruleIndex) ∈ language.rewrites.zipIdx ∧
        ContextualInstance relEnv language free bound expected permissions source
          contextIndex ruleIndex rule site receipt := by
  simp only [model, List.mem_map] at member
  obtain ⟨actual, present, represented⟩ := member
  cases represented
  exact ⟨rfl, executeRules_sound relEnv language free bound expected permissions source
    (generate source) receipt present⟩

theorem model_equations_retains_generation_issue (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (permissions : List OneHoleContext)
    (generate : ∀ source, GeneratedSites language free bound expected permissions source)
    (source : Pattern) (issue : SiteGenerationIssue)
    (unfinished : issue ∈ (generate source).unresolved) :
    Obligation.siteGeneration issue ∈
      ((model relEnv language free bound expected permissions generate).equations source).unresolved := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨issue, unfinished, rfl⟩)

theorem model_firings_retains_generation_issue (relEnv : Engine.RelationEnv)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (permissions : List OneHoleContext)
    (generate : ∀ source, GeneratedSites language free bound expected permissions source)
    (source : Pattern) (issue : SiteGenerationIssue)
    (unfinished : issue ∈ (generate source).unresolved) :
    Obligation.siteGeneration issue ∈
      ((model relEnv language free bound expected permissions generate).firings source).unresolved := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨issue, unfinished, rfl⟩)

end Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax

mutual
/-- Remap rule ordinals throughout the retained source derivation, including
child premises and every ordered quantified body. -/
def Witness.reindexRules (rename : Nat → Nat) : Witness → Witness
  | .base result => .base result
  | .premiseStep child candidate matched result =>
      .premiseStep (child.reindexRules rename) candidate matched result
  | .rule index initial premises => .rule (rename index) initial (reindexWitnesses rename premises)
  | .forAll bodies => .forAll (reindexWitnesses rename bodies)
termination_by witness => sizeOf witness
decreasing_by all_goals simp_wf; all_goals omega

def reindexWitnesses (rename : Nat → Nat) : List Witness → List Witness
  | [] => []
  | head :: tail => head.reindexRules rename :: reindexWitnesses rename tail
termination_by witnesses => sizeOf witnesses
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- A real indexed embedding of rule cores transports the full literal
reference derivation; rule annotations do not select a new matcher. -/
theorem stepValid_reindex {first second : LanguageDef} (rename : Nat → Nat)
    (rows : ∀ index rule, first.rewrites[index]? = some rule →
      ∃ other, second.rewrites[rename index]? = some other ∧
        rule.left = other.left ∧ rule.right = other.right ∧ rule.premises = other.premises)
    (relEnv : Engine.RelationEnv) {source target : Pattern} {witness : Witness}
    (valid : StepValid relEnv first source witness target) :
    StepValid relEnv second source (witness.reindexRules rename) target :=
  match valid with
  | .rule (index := index) (rule := rule) (initial := initial) (final := final) (witnesses := witnesses)
      declared matched premises => by
      obtain ⟨other, selected, left, right, samePremises⟩ := rows index rule declared
      have sites : captureSites rule = captureSites other := by
        simp only [captureSites, left, samePremises]
      have matched' : initial ∈ ReflectiveCanonical.matchPatternForRule second other source := by
        simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, ← left] using matched
      have transported := premisesValid_reindex rename rows relEnv premises
      have premises' : PremisesValid relEnv second (captureSites other) initial other.premises
          (reindexWitnesses rename witnesses) final := by
        simpa only [← sites, ← samePremises] using transported
      have stepped := StepValid.rule selected matched' premises'
      simpa only [Witness.reindexRules, ← sites, ← right] using stepped
termination_by sizeOf witness
decreasing_by all_goals simp_wf

theorem premisesValid_reindex {first second : LanguageDef} (rename : Nat → Nat)
    (rows : ∀ index rule, first.rewrites[index]? = some rule →
      ∃ other, second.rewrites[rename index]? = some other ∧
        rule.left = other.left ∧ rule.right = other.right ∧ rule.premises = other.premises)
    (relEnv : Engine.RelationEnv) {sites : Pattern} {initial final : Match.Bindings}
    {premises : List Premise} {witnesses : List Witness}
    (valid : PremisesValid relEnv first sites initial premises witnesses final) :
    PremisesValid relEnv second sites initial premises (reindexWitnesses rename witnesses) final :=
  match valid with
  | .nil bindings => by
      simpa only [reindexWitnesses] using (PremisesValid.nil (relEnv := relEnv)
        (language := second) (sites := sites) bindings)
  | .cons head tail => by
      simpa only [reindexWitnesses] using PremisesValid.cons
        (premiseValid_reindex rename rows relEnv head) (premisesValid_reindex rename rows relEnv tail)
termination_by sizeOf witnesses
decreasing_by all_goals simp_wf; all_goals omega

theorem premiseValid_reindex {first second : LanguageDef} (rename : Nat → Nat)
    (rows : ∀ index rule, first.rewrites[index]? = some rule →
      ∃ other, second.rewrites[rename index]? = some other ∧
        rule.left = other.left ∧ rule.right = other.right ∧ rule.premises = other.premises)
    (relEnv : Engine.RelationEnv) {sites : Pattern} {initial final : Match.Bindings}
    {premise : Premise} {witness : Witness}
    (valid : PremiseValid relEnv first sites initial premise witness final) :
    PremiseValid relEnv second sites initial premise (witness.reindexRules rename) final :=
  match valid with
  | .base shape member => by
      have languageUnused : Engine.premiseStepWithEnv relEnv first initial premise =
          Engine.premiseStepWithEnv relEnv second initial premise := by
        cases premise <;> rfl
      simpa only [Witness.reindexRules] using (PremiseValid.base (sites := sites)
        shape (languageUnused ▸ member))
  | .step endpoints child matched merged => by
      simpa only [Witness.reindexRules] using PremiseValid.step endpoints
        (stepValid_reindex rename rows relEnv child) matched merged
  | .forAll selected bodies => by
      simpa only [Witness.reindexRules] using PremiseValid.forAll selected
        (forAllValid_reindex rename rows relEnv bodies)
termination_by sizeOf witness
decreasing_by all_goals simp_wf; all_goals omega

theorem forAllValid_reindex {first second : LanguageDef} (rename : Nat → Nat)
    (rows : ∀ index rule, first.rewrites[index]? = some rule →
      ∃ other, second.rewrites[rename index]? = some other ∧
        rule.left = other.left ∧ rule.right = other.right ∧ rule.premises = other.premises)
    (relEnv : Engine.RelationEnv) {sites : Pattern} {bindings : Match.Bindings}
    {parameter : String} {body : Premise} {items : List Pattern} {witnesses : List Witness}
    (valid : ForAllValid relEnv first sites bindings parameter body items witnesses) :
    ForAllValid relEnv second sites bindings parameter body items
      (reindexWitnesses rename witnesses) :=
  match valid with
  | .nil => by
      simpa only [reindexWitnesses] using (ForAllValid.nil (relEnv := relEnv)
        (language := second) (sites := sites) (bindings := bindings) (parameter := parameter) (body := body))
  | .cons head tail => by
      simpa only [reindexWitnesses] using ForAllValid.cons
        (premiseValid_reindex rename rows relEnv head) (forAllValid_reindex rename rows relEnv tail)
termination_by sizeOf witnesses
decreasing_by all_goals simp_wf; all_goals omega
end

#print axioms stepValid_reindex
#print axioms premisesValid_reindex
#print axioms premiseValid_reindex
#print axioms forAllValid_reindex

end Mettapedia.OSLF.MeTTaIL.ReferenceStep

namespace Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

/-- Recover the original declaration index from an in-range selected row.
The fallback leaves an invalid selected index unchanged; valid witnesses never use it. -/
def sourceRuleIndex (plan : Plan) (ordinal : Nat) : Nat :=
  match plan.rules[ordinal]? with
  | some declaration => declaration.declarationIndex
  | none => ordinal

/-- Compilation retains the authored row and its original declaration index,
independently of the selected execution ordinal. -/
theorem compiled_rule_readout (snapshot : Snapshot) (permissions : Permissions)
    {ordinal : Nat} {declaration : RulePlan}
    (position : (compile snapshot permissions).rules[ordinal]? = some declaration) :
    snapshot.language.rewrites[declaration.declarationIndex]? = some declaration.authored ∧
      selected permissions.ruleIndices declaration.declarationIndex = true ∧
      sourceRuleIndex (compile snapshot permissions) ordinal = declaration.declarationIndex := by
  obtain ⟨authored, index, declared, permitted, checked⟩ :=
    compiled_rule_origin (List.mem_of_getElem? position)
  obtain ⟨originalIndex, originalRule, _⟩ := rulePlan_readout checked
  refine ⟨?_, originalIndex ▸ permitted, ?_⟩
  · simpa only [originalIndex, originalRule] using
      (List.mk_mem_zipIdx_iff_getElem?.mp declared)
  · simp only [sourceRuleIndex, position]

/-- Every selected rule core is embedded at its actual source ordinal.
This is a source-row fact, not an assumption about whole execution. -/
theorem compiled_rule_embedding (snapshot : Snapshot) (permissions : Permissions) :
    ∀ ordinal rule, (environment (compile snapshot permissions)).language.rewrites[ordinal]? =
      some rule →
      ∃ authored, snapshot.language.rewrites[sourceRuleIndex (compile snapshot permissions) ordinal]? =
        some authored ∧ rule.left = authored.left ∧ rule.right = authored.right ∧
          rule.premises = authored.premises := by
  intro ordinal rule selectedRule
  simp only [environment, List.getElem?_map] at selectedRule
  obtain ⟨declaration, position, same⟩ := Option.map_eq_some_iff.mp selectedRule
  obtain ⟨sourceRow, _, sourceIndex⟩ := compiled_rule_readout snapshot permissions position
  refine ⟨declaration.authored, sourceIndex ▸ sourceRow, ?_⟩
  subst rule
  exact ⟨rfl, rfl, rfl⟩

#print axioms compiled_rule_readout
#print axioms compiled_rule_embedding

end Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open QuantifiedReference

/-- The actual licensed zipper uses the original grammar. Membership in the
independent finite context policy is supplied explicitly. -/
def Job.sourceSite {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound type source) {contexts : List OneHoleContext}
    (permitted : job.site.context ∈ contexts) :
    TypedContextualEquationExecution.Site plan.snapshot.language plan.snapshot.free
      bound type contexts source where
  context := job.site.context
  focus := job.site.focus
  focusBound := job.site.focusBound
  focusType := job.site.focusType
  permitted := permitted
  source_eq := valid.2.source_eq
  typed := ContextualAuthoredEquationExecution.typedAt_transport
    (GeneralPlanEnvironment.grammar plan) valid.2.typedAt

/-- Source generation retains the complete licensed site, with the original
typing declaration alternatives and address. -/
theorem Job.source_site_member {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound type source) :
    job.site ∈ GeneralTypedSites.generate plan.snapshot.language plan.snapshot.free
      plan.permissions.sites bound type source := by
  exact (GeneralTypedSites.generate_spec _ _ _ _ _ _ _).mpr
    (ContextualAuthoredEquationExecution.licensed_transport (GeneralPlanEnvironment.grammar plan) valid.2)

/-- The original grammar and declared operational permissions generate the
actual licensed context, without any assumption about executor outputs. -/
theorem Job.sourcePolicy_member {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} {job : Job}
    (valid : job.Valid plan bound type source) :
    job.site.context ∈ GeneralTypedSites.generatedPermissions plan.snapshot.language plan.snapshot.free
      plan.permissions.sites bound type source := by
  exact List.mem_map.mpr ⟨job.site, Job.source_site_member valid, rfl⟩

/-- The full source derivation is at the licensed focus. The selected rule
ordinal remains explicit, independently of its authored declaration index. -/
theorem Receipt.selected_reference_focus {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {receipt : Receipt}
    (profile : DirectedForwardProfile Schema (GeneralPlanEnvironment.environment plan))
    (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv (GeneralPlanEnvironment.environment plan).provider)
    (valid : receipt.Valid plan bound type source) :
    (GeneralPlanEnvironment.environment plan).language.rewrites[receipt.job.ordinal]? =
        some receipt.job.declaration.rule ∧
    plan.permissions.sites.permitsContext receipt.job.site.context = true ∧
    TypedAt (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      receipt.job.site.focus receipt.job.site.context bound type
      receipt.job.site.focusBound receipt.job.site.focusType ∧
    receipt.job.site.context.fill receipt.job.site.focus = source ∧
    receipt.target = receipt.job.site.context.fill receipt.localTarget ∧
    ∃ bindings witnesses, ReferenceStep.StepValid relEnv (GeneralPlanEnvironment.environment plan).language
      receipt.job.site.focus (.rule receipt.job.ordinal bindings witnesses) receipt.localTarget := by
  obtain ⟨bindings, witnesses, reference⟩ :=
    directed_root_toReference_of_forward profile relEnv reads valid.2.1
  exact ⟨Job.selected_rule valid.1, valid.1.2.permitted, valid.1.2.typedAt,
    valid.1.2.source_eq, valid.2.2.2.1, bindings, witnesses, reference⟩

/-- A compiled ordinary receipt retains a complete derivation of the
original source declaration at its licensed focus. Every recursive child and
quantified body uses original declaration indices, not selected row numbers. -/
theorem Receipt.original_reference_focus {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    (snapshot : GeneralExecutionAdmission.Snapshot) (permissions : GeneralExecutionAdmission.Permissions)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {receipt : Receipt}
    (profile : DirectedForwardProfile Schema
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)))
    (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv snapshot.provider)
    (valid : receipt.Valid (GeneralExecutionAdmission.compile snapshot permissions) bound type source) :
    (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)).language.rewrites[
        receipt.job.ordinal]? = some receipt.job.declaration.rule ∧
    snapshot.language.rewrites[receipt.job.declaration.declarationIndex]? =
        some receipt.job.declaration.authored ∧
    GeneralExecutionAdmission.selected permissions.ruleIndices receipt.job.declaration.declarationIndex = true ∧
    permissions.sites.permitsContext receipt.job.site.context = true ∧
    TypedAt (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)).language
      snapshot.free receipt.job.site.focus receipt.job.site.context bound type
      receipt.job.site.focusBound receipt.job.site.focusType ∧
    receipt.job.site.context.fill receipt.job.site.focus = source ∧
    receipt.target = receipt.job.site.context.fill receipt.localTarget ∧
    ∃ bindings witnesses, ReferenceStep.StepValid relEnv snapshot.language receipt.job.site.focus
      (.rule receipt.job.declaration.declarationIndex bindings witnesses) receipt.localTarget := by
  obtain ⟨selected, permitted, typed, filled, target, bindings, witnesses, focused⟩ :=
    receipt.selected_reference_focus profile relEnv reads valid
  have position := List.mk_mem_zipIdx_iff_getElem?.mp valid.1.1
  obtain ⟨authored, originalPermitted, sourceIndex⟩ :=
    GeneralPlanEnvironment.compiled_rule_readout snapshot permissions position
  have original := ReferenceStep.stepValid_reindex
    (GeneralPlanEnvironment.sourceRuleIndex (GeneralExecutionAdmission.compile snapshot permissions))
    (GeneralPlanEnvironment.compiled_rule_embedding snapshot permissions) relEnv focused
  refine ⟨selected, authored, originalPermitted, permitted, typed, filled, target,
    bindings, ReferenceStep.reindexWitnesses
      (GeneralPlanEnvironment.sourceRuleIndex (GeneralExecutionAdmission.compile snapshot permissions)) witnesses, ?_⟩
  simpa only [ReferenceStep.Witness.reindexRules, sourceIndex] using original

/-- At the root permission the original focus derivation is already an
original whole-source step. No spatial congruence declaration is needed. -/
theorem Receipt.original_root_reference_step {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    (snapshot : GeneralExecutionAdmission.Snapshot) (permissions : GeneralExecutionAdmission.Permissions)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {receipt : Receipt}
    (profile : DirectedForwardProfile Schema
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)))
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv snapshot.provider)
    (valid : receipt.Valid (GeneralExecutionAdmission.compile snapshot permissions) bound type source)
    (root : receipt.job.site.context = .hole) :
    ReferenceStep.Step relEnv snapshot.language source receipt.target := by
  obtain ⟨_, _, _, _, _, filled, target, bindings, witnesses, original⟩ :=
    receipt.original_reference_focus snapshot permissions profile relEnv reads valid
  simp only [root, OneHoleContext.fill] at filled target
  rw [← filled, target]
  exact ⟨.rule receipt.job.declaration.declarationIndex bindings witnesses, original⟩

/-- The full original reference witness lifts only through the explicit
source-context policy. The compiler's operational permission is retained as
separate evidence; no authored congruence is manufactured. -/
theorem Receipt.original_contextual_instance {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    (snapshot : GeneralExecutionAdmission.Snapshot) (permissions : GeneralExecutionAdmission.Permissions)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {receipt : Receipt}
    (profile : DirectedForwardProfile Schema
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)))
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv snapshot.provider)
    (valid : receipt.Valid (GeneralExecutionAdmission.compile snapshot permissions) bound type source)
    (contexts : List OneHoleContext) (contextIndex : Nat)
    (permitted : receipt.job.site.context ∈ contexts) :
    ∃ bindings witnesses,
      permissions.sites.permitsContext receipt.job.site.context = true ∧
      ContextualAuthoredEquationExecution.ContextualInstance relEnv snapshot.language snapshot.free
        bound type contexts source contextIndex receipt.job.declaration.declarationIndex
        receipt.job.declaration.authored (receipt.job.sourceSite valid.1 permitted)
        (evidence := ContextualAuthoredEquationExecution.referenceEvidence)
        (contextIndex, receipt, .rule receipt.job.declaration.declarationIndex bindings witnesses) := by
  obtain ⟨_, authored, _, operational, _, _, target, bindings, witnesses, original⟩ :=
    receipt.original_reference_focus snapshot permissions profile relEnv reads valid
  have localTyped := GeneralLanguageTyping.open_transport
    (GeneralPlanEnvironment.grammar (GeneralExecutionAdmission.compile snapshot permissions))
    (receipt_root_readout valid).2.2.2.2
  have targetTyped := GeneralLanguageTyping.open_transport
    (GeneralPlanEnvironment.grammar (GeneralExecutionAdmission.compile snapshot permissions))
    valid.2.2.2.2
  refine ⟨bindings, witnesses, operational, .fill rfl rfl rfl rfl rfl ?_ target
    targetTyped.2.2.2 targetTyped.1⟩
  exact ⟨authored, localTyped, ⟨bindings, witnesses, rfl⟩, original⟩

/-- The genuine source site generator discharges the finite context-policy
membership required by the generic lift. This remains a forward statement. -/
theorem Receipt.original_generated_contextual_instance {Schema : Pattern → Prop} [BinderFreeSyntax Schema]
    (snapshot : GeneralExecutionAdmission.Snapshot) (permissions : GeneralExecutionAdmission.Permissions)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {receipt : Receipt}
    (profile : DirectedForwardProfile Schema
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)))
    (relEnv : Engine.RelationEnv) (reads : ReadsProvider relEnv snapshot.provider)
    (valid : receipt.Valid (GeneralExecutionAdmission.compile snapshot permissions) bound type source) :
    ∃ contextIndex,
      (receipt.job.site, contextIndex) ∈
        (GeneralTypedSites.generate snapshot.language snapshot.free permissions.sites bound type source).zipIdx ∧
      ∃ bindings witnesses,
      permissions.sites.permitsContext receipt.job.site.context = true ∧
      ContextualAuthoredEquationExecution.ContextualInstance relEnv snapshot.language snapshot.free
        bound type (GeneralTypedSites.generatedPermissions snapshot.language snapshot.free permissions.sites
          bound type source) source contextIndex receipt.job.declaration.declarationIndex
        receipt.job.declaration.authored (receipt.job.sourceSite valid.1 (Job.sourcePolicy_member valid.1))
        (evidence := ContextualAuthoredEquationExecution.referenceEvidence)
        (contextIndex, receipt, .rule receipt.job.declaration.declarationIndex bindings witnesses) := by
  obtain ⟨contextIndex, selected⟩ := List.mem_iff_getElem?.mp (Job.source_site_member valid.1)
  refine ⟨contextIndex, List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
  exact receipt.original_contextual_instance snapshot permissions profile relEnv reads valid
    _ contextIndex (Job.sourcePolicy_member valid.1)

#print axioms Job.source_site_member
#print axioms ContextualAuthoredEquationExecution.licensed_transport
#print axioms Job.sourcePolicy_member
#print axioms Receipt.original_generated_contextual_instance

#print axioms ContextualAuthoredEquationExecution.typedAt_transport
#print axioms Receipt.selected_reference_focus
#print axioms Receipt.original_contextual_instance
#print axioms Receipt.original_reference_focus

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs

#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.ContextualInstance.conditional_iff
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralRuleJobs.Receipt.original_root_reference_step
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.rootSites_has_root
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.rootSites_nonroot_pending
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.rootSites_unavailable
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.root_only_site_unique
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.rootSites_covers_root_only
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.rootSites_root_only_resolved
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.contextual_sound
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.contextual_complete
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.applyEquationAt_sound
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.applyEquationAt_complete
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.executeEquations_sound
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.executeEquations_complete
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.executeRules_sound
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.executeRules_complete
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.model_equations_sound
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.model_firings_sound
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.model_equations_retains_generation_issue
#print axioms Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution.model_firings_retains_generation_issue
