import Mettapedia.OSLF.MeTTaIL.TypedContextualEquationExecution
import Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

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

open Syntax DerivedContexts
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

/-- A filled atomic instance is judged independently of contextual execution.
The actual indexed root derivation and exact zipper fill are both retained. -/
inductive ContextualInstance (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex declarationIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source)
    (receipt : TypedContextualEquationExecution.Receipt) : Prop where
  | fill (contextOrigin : receipt.contextIndex = contextIndex)
      (context : receipt.context = site.context)
      (focusBound : receipt.focusBound = site.focusBound)
      (focusType : receipt.focusType = site.focusType)
      (declaration : receipt.ruleIndex = declarationIndex)
      (atomic : ConditionalEquationExecution.RuleInstance relEnv language free
        site.focusBound site.focusType rule site.focus receipt.atomic)
      (target : receipt.target = site.context.fill receipt.atomic.target)
      (scoping : receipt.target.isWellScopedAt bound.length = true)
      (typing : HasType language free bound receipt.target expected) :
      ContextualInstance relEnv language free bound expected permissions source
        contextIndex declarationIndex rule site receipt

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
