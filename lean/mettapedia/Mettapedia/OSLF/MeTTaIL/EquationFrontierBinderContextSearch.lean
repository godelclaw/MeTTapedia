import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderContexts
import Mettapedia.OSLF.MeTTaIL.ContextualAuthoredEquationExecution

/-!
# Equation transport and directed firing below a retained binder

The site generator searches the complete finite ambient-indexed family by
actual pattern equality. It never chooses a phase from hidden state. A decoded
source earns its typed binder-body site; other inputs retain a site-generation
obligation. The shared queue then performs both equation orientations and all
authored primitive rules at that same licensed site.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderContextSearch

open Syntax Engine DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationFrontierBinderProfile
open EquationFrontierBinderContexts (bindingContext permissions)
open ScopedEquationExecution (Orientation orientedRule)

def decode? (ambient : Nat) (source : Pattern) : Option (State (ambient + 1)) :=
  (allStates (ambient + 1)).find? fun state => nu state.pattern == source

theorem decode?_family (ambient : Nat) (state : State (ambient + 1)) :
    decode? ambient (nu state.pattern) = some state := by
  unfold decode?
  cases found : (allStates (ambient + 1)).find?
      (fun candidate => nu candidate.pattern == nu state.pattern) with
  | none =>
      have absent := List.find?_eq_none.mp found state (allStates_complete state)
      simp at absent
  | some actual =>
      have sameEncoded : nu actual.pattern = nu state.pattern := by
        have matchedEncoded : (nu actual.pattern == nu state.pattern) = true :=
          List.find?_some (p := fun candidate : State (ambient + 1) =>
            nu candidate.pattern == nu state.pattern) found
        exact beq_iff_eq.mp matchedEncoded
      have same : actual.pattern = state.pattern := by
        simpa [nu] using sameEncoded
      have equal := state_pattern_injective same
      exact congrArg some equal

/-- A real finite decoder constructs the proved context site after checking
the actual source. An unrepresented term keeps unfinished generation work. -/
def generateSites (ambient : Nat) (source : Pattern) :
    ContextualAuthoredEquationExecution.GeneratedSites language FreeTypeContext.empty
      (ambientContext ambient) .proc permissions source :=
  match decode? ambient source with
  | none => ⟨[], [.uncertifiedCoverage]⟩
  | some state =>
      if represented : nu state.pattern = source then
        let licensed := EquationFrontierBinderContexts.site state
        ⟨[{ context := licensed.context, focus := licensed.focus,
            focusBound := licensed.focusBound, focusType := licensed.focusType,
            permitted := licensed.permitted,
            source_eq := licensed.source_eq.trans represented,
            typed := licensed.typed }], []⟩
      else ⟨[], [.unavailableTyping]⟩

theorem generateSites_family (ambient : Nat) (state : State (ambient + 1)) :
    generateSites ambient (nu state.pattern) =
      ⟨[EquationFrontierBinderContexts.site state], []⟩ := by
  simp [generateSites, decode?_family]

theorem generateSites_undecoded (ambient : Nat) (source : Pattern)
    (unknown : decode? ambient source = none) :
    (generateSites ambient source).sites = [] ∧
      (generateSites ambient source).unresolved = [.uncertifiedCoverage] := by
  simp [generateSites, unknown]

def model (ambient : Nat) (allowed : List Token) :=
  ContextualAuthoredEquationExecution.model (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc permissions (generateSites ambient)

def search (ambient : Nat) (allowed : List Token) (source : Pattern) (fuel : Nat) :=
  Framework.ResumableEquationOccurrenceFrontier.run (model ambient allowed) fuel
    (Framework.ResumableEquationOccurrenceFrontier.initial source)

def liftReceipt (ambient declaration : Nat) (atomic : ConditionalEquationExecution.Receipt) :
    TypedContextualEquationExecution.Receipt :=
  ⟨0, bindingContext, ambientContext (ambient + 1), .proc, declaration, atomic,
    nu atomic.target⟩

def liftEquationReceipt (ambient : Nat) (atomic : ConditionalEquationExecution.EquationReceipt) :
    ContextualAuthoredEquationExecution.EquationOrigin :=
  ⟨atomic.equationIndex, atomic.orientation, liftReceipt ambient atomic.equationIndex atomic.toReceipt⟩

theorem fill_expected (ambient : Nat) (index : Fin ((ambient + 1) + 1))
    (token : Token) (phase : Phase) (declaration resultIndex : Nat) :
    TypedContextualEquationExecution.fillReceipt? language FreeTypeContext.empty
      (ambientContext ambient) .proc 0 declaration bindingContext
      (ambientContext (ambient + 1)) .proc
      (expectedReceipt (ambient + 1) index token phase resultIndex) =
        some (liftReceipt ambient declaration
          (expectedReceipt (ambient + 1) index token phase resultIndex)) := by
  let targetState : State (ambient + 1) := ⟨phase, index, token⟩
  have bodyTyped : HasType language FreeTypeContext.empty
      (.name :: ambientContext ambient) targetState.pattern .proc := by
    simpa only [← EquationFrontierBinderContexts.ambientContext_succ] using state_typed targetState
  have targetChecked := checkHasType_complete_of_object
    (nu_typed (ambientContext ambient) targetState.pattern bodyTyped)
    (by simp [nu, isObjectPattern, isObjectPatternList, state_object])
  have targetScoped : (nu targetState.pattern).isWellScopedAt ambient = true := by
    simpa [nu, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using state_scoped targetState
  simp only [TypedContextualEquationExecution.fillReceipt?, expectedReceipt,
    bindingContext, OneHoleContext.fill, List.nil_append]
  change (if (nu targetState.pattern).isWellScopedAt (ambientContext ambient).length &&
    checkHasType language FreeTypeContext.empty (ambientContext ambient)
      (nu targetState.pattern) .proc then _ else _) = _
  simp only [ambientContext_length, targetScoped, targetChecked, Bool.and_self, if_true]
  rfl

theorem fill_expected_receipts (allowed : List Token) (ambient : Nat)
    (index : Fin ((ambient + 1) + 1)) (token : Token) (phase : Phase) (declaration : Nat) :
    (expectedReceipts allowed (ambient + 1) index token phase).filterMap
      (TypedContextualEquationExecution.fillReceipt? language FreeTypeContext.empty
        (ambientContext ambient) .proc 0 declaration bindingContext
        (ambientContext (ambient + 1)) .proc) =
      (expectedReceipts allowed (ambient + 1) index token phase).map
        (liftReceipt ambient declaration) := by
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro atomic present
  simp only [expectedReceipts, List.mem_map] at present
  obtain ⟨row, _, represented⟩ := present
  cases represented
  exact fill_expected ambient index token phase declaration row.2

theorem applyEquationAt_family (ambient : Nat) (allowed : List Token)
    (state : State (ambient + 1)) (orientation : Orientation) :
    ContextualAuthoredEquationExecution.applyEquationAt (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc permissions (nu state.pattern)
      0 0 extrusionEquation orientation (EquationFrontierBinderContexts.site state) =
      ⟨(expectedEquationReceipts allowed (ambient + 1) state 0 orientation).map
        (liftEquationReceipt ambient), []⟩ := by
  by_cases active : state.phase = equationSourcePhase orientation
  · simp only [ContextualAuthoredEquationExecution.applyEquationAt,
      TypedContextualEquationExecution.applyAt, EquationFrontierBinderContexts.site,
      extrusion_outcome_family, active, if_true, expectedEquationReceipts,
      fill_expected_receipts, List.map_nil]
    simp only [List.map_map, liftEquationReceipt, Function.comp_def]
  · simp [ContextualAuthoredEquationExecution.applyEquationAt,
      TypedContextualEquationExecution.applyAt, EquationFrontierBinderContexts.site,
      extrusion_outcome_family, expectedEquationReceipts, active]

theorem applyConsumeAt_family (ambient : Nat) (allowed : List Token)
    (state : State (ambient + 1)) (declaration : Nat) (name : String) :
    TypedContextualEquationExecution.applyAt (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc permissions (nu state.pattern) 0 declaration
      { consumeRule with name := name } (EquationFrontierBinderContexts.site state) =
      ⟨(expectedRuleReceipts allowed (ambient + 1) state).map
        (liftReceipt ambient declaration), []⟩ := by
  by_cases active : state.phase = .exposed
  · simp only [TypedContextualEquationExecution.applyAt, EquationFrontierBinderContexts.site,
      consume_rename_outcome, consume_outcome_family, active, if_true,
      expectedRuleReceipts, fill_expected_receipts, List.map_nil]
  · simp [TypedContextualEquationExecution.applyAt, EquationFrontierBinderContexts.site,
      consume_rename_outcome, consume_outcome_family, expectedRuleReceipts, active]

def expectedEquations (ambient : Nat) (allowed : List Token) (state : State (ambient + 1)) :=
  (expectedEquationReceipts allowed (ambient + 1) state 0 .forward).map
      (fun atomic => (liftEquationReceipt ambient atomic, nu atomic.target)) ++
    (expectedEquationReceipts allowed (ambient + 1) state 0 .reverse).map
      (fun atomic => (liftEquationReceipt ambient atomic, nu atomic.target))

def expectedFirings (ambient : Nat) (allowed : List Token) (state : State (ambient + 1)) :=
  (expectedRuleReceipts allowed (ambient + 1) state).map
      (fun atomic => (liftReceipt ambient 0 atomic, nu atomic.target)) ++
    (expectedRuleReceipts allowed (ambient + 1) state).map
      (fun atomic => (liftReceipt ambient 1 atomic, nu atomic.target))

theorem equationBatch_family (ambient : Nat) (allowed : List Token)
    (state : State (ambient + 1)) :
    (model ambient allowed).equations (nu state.pattern) =
      ⟨expectedEquations ambient allowed state, []⟩ := by
  simp [model, ContextualAuthoredEquationExecution.model,
    ContextualAuthoredEquationExecution.executeEquations, generateSites_family,
    language_equations, applyEquationAt_family, expectedEquations,
    List.map_map, Function.comp_def, liftEquationReceipt, liftReceipt]

theorem firingBatch_family (ambient : Nat) (allowed : List Token)
    (state : State (ambient + 1)) :
    (model ambient allowed).firings (nu state.pattern) =
      ⟨expectedFirings ambient allowed state, []⟩ := by
  have original := applyConsumeAt_family ambient allowed state 0 consumeRule.name
  change TypedContextualEquationExecution.applyAt (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc permissions (nu state.pattern) 0 0 consumeRule
      (EquationFrontierBinderContexts.site state) = _ at original
  simp [model, ContextualAuthoredEquationExecution.model,
    ContextualAuthoredEquationExecution.executeRules, TypedContextualEquationExecution.executeSites,
    generateSites_family, language_rewrites, original, applyConsumeAt_family, expectedFirings,
    List.map_map, Function.comp_def, liftReceipt]

/-- Every equation answer retains the typed outer context and the actual
root equation derivation under its additional ambient name. -/
theorem model_equations_readout (ambient : Nat) (allowed : List Token)
    (state : State (ambient + 1))
    (origin : ContextualAuthoredEquationExecution.EquationOrigin) (target : Pattern)
    (present : (origin, target) ∈ ((model ambient allowed).equations (nu state.pattern)).answers) :
    origin.contextual.context = bindingContext ∧
      origin.contextual.focusBound = ambientContext (ambient + 1) ∧
      origin.contextual.focusType = .proc ∧
      target = nu origin.contextual.atomic.target ∧
      HasType language FreeTypeContext.empty (ambientContext ambient) target .proc ∧
      ∃ equation, (equation, origin.equationIndex) ∈ language.equations.zipIdx ∧
        ConditionalEquationExecution.RuleInstance (provider allowed) language
          FreeTypeContext.empty (ambientContext (ambient + 1)) .proc
          (orientedRule equation origin.orientation) state.pattern origin.contextual.atomic := by
  obtain ⟨targetEq, selected, contextIndex, equation, equationIndex, orientation,
    siteMember, declared, interpreted⟩ :=
    ContextualAuthoredEquationExecution.model_equations_sound (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc permissions (generateSites ambient)
      (nu state.pattern) target origin present
  have selectedEq : selected = EquationFrontierBinderContexts.site state := by
    have member := List.fst_mem_of_mem_zipIdx siteMember
    simpa only [generateSites_family, List.mem_singleton] using member
  subst selected
  rcases interpreted with ⟨declarationEq, orientationEq, interpreted⟩
  cases interpreted with
  | fill _ context focusBound focusType _ atomic filled _ typed =>
      refine ⟨context, focusBound, focusType, ?_, targetEq ▸ typed, equation, ?_, ?_⟩
      · rw [targetEq, filled]
        rfl
      · simpa only [declarationEq] using declared
      · simpa only [orientationEq, EquationFrontierBinderContexts.site] using atomic

/-- Primitive answers carry the same whole/focus contexts and preserve the
authored rule index and full atomic conditional receipt. -/
theorem model_firings_readout (ambient : Nat) (allowed : List Token)
    (state : State (ambient + 1))
    (receipt : TypedContextualEquationExecution.Receipt) (target : Pattern)
    (present : (receipt, target) ∈ ((model ambient allowed).firings (nu state.pattern)).answers) :
    receipt.context = bindingContext ∧ receipt.focusBound = ambientContext (ambient + 1) ∧
      receipt.focusType = .proc ∧ target = nu receipt.atomic.target ∧
      HasType language FreeTypeContext.empty (ambientContext ambient) target .proc ∧
      ∃ rule, (rule, receipt.ruleIndex) ∈ language.rewrites.zipIdx ∧
        ConditionalEquationExecution.RuleInstance (provider allowed) language
          FreeTypeContext.empty (ambientContext (ambient + 1)) .proc
          rule state.pattern receipt.atomic := by
  obtain ⟨targetEq, selected, contextIndex, rule, ruleIndex,
    siteMember, declared, interpreted⟩ :=
    ContextualAuthoredEquationExecution.model_firings_sound (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc permissions (generateSites ambient)
      (nu state.pattern) target receipt present
  have selectedEq : selected = EquationFrontierBinderContexts.site state := by
    have member := List.fst_mem_of_mem_zipIdx siteMember
    simpa only [generateSites_family, List.mem_singleton] using member
  subst selected
  cases interpreted with
  | fill _ context focusBound focusType declaration atomic filled _ typed =>
      refine ⟨context, focusBound, focusType, ?_, targetEq ▸ typed, rule, ?_, atomic⟩
      · rw [targetEq, filled]
        rfl
      · simpa only [declaration] using declared

def tucked : State 1 := ⟨.tucked, 0, .permit⟩

def exposed : State 1 := ⟨.exposed, 0, .permit⟩

def finished : State 1 := ⟨.finished, 0, .permit⟩

open Framework.ResumableEquationOccurrenceFrontier

def forwardOrigin : ContextualAuthoredEquationExecution.EquationOrigin :=
  liftEquationReceipt 0 ⟨expectedReceipt 1 0 .permit .exposed 0, 0, .forward⟩

def reverseOrigin : ContextualAuthoredEquationExecution.EquationOrigin :=
  liftEquationReceipt 0 ⟨expectedReceipt 1 0 .permit .tucked 0, 0, .reverse⟩

def primitiveOrigin (declaration : Nat) : TypedContextualEquationExecution.Receipt :=
  liftReceipt 0 declaration (expectedReceipt 1 0 .permit .finished 0)

def firstEntry : Entry Pattern ContextualAuthoredEquationExecution.EquationOrigin :=
  ⟨nu tucked.pattern, []⟩

def secondEntry : Entry Pattern ContextualAuthoredEquationExecution.EquationOrigin :=
  ⟨nu exposed.pattern, [(forwardOrigin, nu exposed.pattern)]⟩

def firedReceipt (declaration : Nat) :
    Receipt Pattern ContextualAuthoredEquationExecution.EquationOrigin
      TypedContextualEquationExecution.Receipt :=
  ⟨secondEntry, declaration, primitiveOrigin declaration, nu finished.pattern⟩

theorem exposed_ne_tucked : nu exposed.pattern ≠ nu tucked.pattern := by
  intro equal
  have bodyEqual : exposed.pattern = tucked.pattern :=
    (Pattern.lambda.inj (List.cons.inj (Pattern.apply.inj equal).2).1).2
  have states := state_pattern_injective bodyEqual
  have phases := congrArg State.phase states
  cases phases

theorem equation_batches :
    (model 0 [.permit]).equations (nu tucked.pattern) =
      ⟨[(forwardOrigin, nu exposed.pattern)], []⟩ ∧
    (model 0 [.permit]).equations (nu exposed.pattern) =
      ⟨[(reverseOrigin, nu tucked.pattern)], []⟩ := by
  constructor <;> rw [equationBatch_family] <;> rfl

theorem firing_batches :
    (model 0 [.permit]).firings (nu tucked.pattern) = ⟨[], []⟩ ∧
    (model 0 [.permit]).firings (nu exposed.pattern) =
      ⟨[(primitiveOrigin 0, nu finished.pattern),
        (primitiveOrigin 1, nu finished.pattern)], []⟩ := by
  constructor <;> rw [firingBatch_family] <;> rfl

def paused : Snapshot Pattern ContextualAuthoredEquationExecution.EquationOrigin
    TypedContextualEquationExecution.Receipt ContextualAuthoredEquationExecution.Obligation where
  pending := [secondEntry]
  visited := [firstEntry]
  conversions := [secondEntry]
  receipts := []
  parked := []
  work := 1

def completed : Snapshot Pattern ContextualAuthoredEquationExecution.EquationOrigin
    TypedContextualEquationExecution.Receipt ContextualAuthoredEquationExecution.Obligation where
  pending := []
  visited := [firstEntry, secondEntry]
  conversions := [secondEntry, secondEntry.extend (reverseOrigin, nu tucked.pattern)]
  receipts := [firedReceipt 0, firedReceipt 1]
  parked := []
  work := 2

theorem run_one : search 0 [.permit] (nu tucked.pattern) 1 = paused := by
  have equations := equation_batches.1
  have firings := firing_batches.1
  simp [search, run, tick, initial, equations, firings, discoveries, Entry.extend,
    readouts, obligations, paused, firstEntry, secondEntry, exposed_ne_tucked]

theorem resume_one : run (model 0 [.permit]) 1 paused = completed := by
  have equations := equation_batches.2
  have firings := firing_batches.2
  simp [run, tick, paused, firstEntry, secondEntry, equations, firings,
    exposed_ne_tucked, discoveries, Entry.extend, readouts, obligations, completed, firedReceipt]

theorem run_two : search 0 [.permit] (nu tucked.pattern) 2 = completed := by
  unfold search
  rw [show (2 : Nat) = 1 + 1 from rfl, run_add]
  change run (model 0 [.permit]) 1 (search 0 [.permit] (nu tucked.pattern) 1) = _
  rw [run_one, resume_one]

theorem equation_transport_then_two_firings :
    (search 0 [.permit] (nu tucked.pattern) 2).receipts.length = 2 ∧
      (search 0 [.permit] (nu tucked.pattern) 2).conversions.length = 2 ∧
      (search 0 [.permit] (nu tucked.pattern) 2).parked = [] := by
  rw [run_two]
  exact ⟨rfl, rfl, rfl⟩

theorem two_firings_preserve_complete_origins :
    (search 0 [.permit] (nu tucked.pattern) 2).receipts.map
        (fun receipt => (receipt.origin.contextIndex, receipt.origin.ruleIndex,
          receipt.origin.context, receipt.origin.focusBound, receipt.target)) =
      [(0, 0, bindingContext, ambientContext 1, nu finished.pattern),
       (0, 1, bindingContext, ambientContext 1, nu finished.pattern)] := by
  rw [run_two]
  rfl

theorem equation_origins_preserve_binder_and_orientation :
    (search 0 [.permit] (nu tucked.pattern) 2).conversions.map
        (fun entry => entry.conversions.map (fun (origin, _) =>
          (origin.equationIndex, origin.orientation, origin.contextual.context,
            origin.contextual.focusBound))) =
      [[(0, .forward, bindingContext, ambientContext 1)],
       [(0, .forward, bindingContext, ambientContext 1),
        (0, .reverse, bindingContext, ambientContext 1)]] := by
  rw [run_two]
  rfl

theorem equation_administration_is_not_primitive_reduction :
    (search 0 [.permit] (nu tucked.pattern) 1).receipts = [] ∧
      (search 0 [.permit] (nu tucked.pattern) 1).conversions.length = 1 := by
  rw [run_one]
  exact ⟨rfl, rfl⟩

theorem reverse_equation_executes_under_binder :
    ((model 0 [.permit]).equations (nu exposed.pattern)).answers.map
        (fun (origin, target) => (origin.orientation, target)) =
      [(.reverse, nu tucked.pattern)] := by
  rw [equation_batches.2]
  rfl

theorem failed_query_has_no_firing_or_conversion :
    (search 0 [] (nu tucked.pattern) 2).receipts = [] ∧
      (search 0 [] (nu tucked.pattern) 2).conversions = [] ∧
      (search 0 [] (nu tucked.pattern) 2).parked = [] := by
  have equations : (model 0 []).equations (nu tucked.pattern) = ⟨[], []⟩ := by
    rw [equationBatch_family]
    rfl
  have firings : (model 0 []).firings (nu tucked.pattern) = ⟨[], []⟩ := by
    rw [firingBatch_family]
    rfl
  simp [search, run, tick, initial, equations, firings, discoveries, readouts, obligations]

theorem unknown_source_retains_generation_obligations :
    (search 0 [.permit] (guard .permit) 1).receipts = [] ∧
      (search 0 [.permit] (guard .permit) 1).parked.length = 2 ∧
      Framework.ResumableEquationOccurrenceFrontier.quiescent
        (search 0 [.permit] (guard .permit) 1) = false := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderContextSearch
