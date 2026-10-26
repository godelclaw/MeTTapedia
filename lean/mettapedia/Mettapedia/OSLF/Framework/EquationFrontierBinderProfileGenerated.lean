import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileExecution
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileCoverage
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.ContextualBindingExtension

/-!
# Generated presentation and alpha admission for the finite binder profile

The raw matcher ignores source binder display names. Consequently the raw
equation class contains noncanonical named presentations even when its source
is canonical. The admitted semantic carrier uses the existing alpha quotient;
erasure retains all binding indices, keys, constructor shapes and observations.
The comparison below is with the authored equation and operational relations,
not a definition of those relations from the finite executor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated

open Mettapedia.OSLF.MeTTaIL
open Syntax Engine Match ContextualStep DerivedContexts
open ReflectiveCanonical ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def base (allowed : List Token) : BasePremiseEvaluator :=
  engineBasePremises (provider allowed)

/-- Binder display metadata is retained outside the admitted alpha boundary. -/
def displayedPattern {ambient : Nat} (binder : Option String) (state : State ambient) : Pattern :=
  match state.phase with
  | .tucked => .apply "Nu" [.lambda binder (pair (cell state.name.val) (guard state.key))]
  | .exposed => pair (.apply "Nu" [.lambda binder (cell state.name.val)]) (guard state.key)
  | .finished => .apply "Nu" [.lambda binder (done (pair (cell state.name.val) (guard state.key)))]

theorem displayed_erasure {ambient : Nat} (binder : Option String) (state : State ambient) :
    (displayedPattern binder state).eraseBinderMetadata = state.pattern := by
  cases state with
  | mk phase name key =>
    cases phase <;> simp [displayedPattern, State.pattern, nu, pair, cell, EquationFrontierBinderProfile.guard,
      done, Token.pattern, Pattern.eraseBinderMetadata]

theorem displayed_none {ambient : Nat} (state : State ambient) :
    displayedPattern none state = state.pattern := by
  cases state with
  | mk phase name key => cases phase <;> rfl

theorem displayed_alpha {ambient : Nat} (binder : Option String) (state : State ambient) :
    Pattern.AlphaEquiv (displayedPattern binder state) state.pattern := by
  rw [Pattern.AlphaEquiv, displayed_erasure]
  exact (Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical state)).symm

theorem displayed_alpha_iff {ambient : Nat} (leftBinder rightBinder : Option String)
    (left right : State ambient) :
    Pattern.AlphaEquiv (displayedPattern leftBinder left) (displayedPattern rightBinder right) ↔
      left = right := by
  rw [Pattern.AlphaEquiv, displayed_erasure, displayed_erasure]
  exact state_pattern_injective.eq_iff

theorem raw_match_displayed_forward {ambient : Nat} (binder : Option String)
    (name : Fin (ambient + 1)) (key : Token) :
    matchPattern extrusionEquation.left (displayedPattern binder ⟨.tucked, name, key⟩) =
      [rawCaptured name.val key] := by
  simp [displayedPattern, extrusionEquation, ScopedEquationControls.extrusionEquation,
    pair, matchPattern, matchArgs, mergeBindings, rawCaptured]

theorem raw_premises_spec (allowed : List Token) (index : Nat) (key : Token)
    (fuel : Nat) (result : Bindings) :
    PremisesAt (base allowed) language fuel (rawCaptured index key)
      extrusionEquation.premises result ↔
        result = rawCaptured index key ∧ key ∈ allowed := by
  change PremisesAt (engineBasePremises (provider allowed)) language fuel
    (rawCaptured index key) extrusionEquation.premises result ↔ _
  rw [premisesAt_engineBase_iff_mem_applyPremisesWithEnv
    (show NoncontextualPremises extrusionEquation.premises from by
      exact .relationQuery .nil)]
  simp [extrusionEquation, applyPremisesWithEnv, premiseStepWithEnv,
    relation_query_results, and_comm]

/-- The original raw schema already produces canonical targets from named
sources; no additional alpha equation has been assumed. -/
theorem raw_named_forward {ambient : Nat} (allowed : List Token) (binder : Option String)
    (name : Fin (ambient + 1)) (key : Token) (admitted : key ∈ allowed) :
    EquationInstance (base allowed) language
      (displayedPattern binder ⟨.tucked, name, key⟩)
      (State.pattern (⟨.exposed, name, key⟩ : State ambient)) := by
  refine ⟨0, .forward (equation := extrusionEquation)
    (initialBindings := rawCaptured name.val key) (finalBindings := rawCaptured name.val key)
    (List.Mem.head _) ?_ ?_ ?_⟩
  · rw [raw_match_displayed_forward]
    simp
  · exact (raw_premises_spec allowed name.val key 0 _).mpr ⟨rfl, admitted⟩
  · simp [applyBindings, rawCaptured, extrusionEquation,
      ScopedEquationControls.extrusionEquation, State.pattern, nu, pair, cell,
      EquationFrontierBinderProfile.guard]

/-- The raw equation class of a canonical source contains arbitrarily named
presentations. Exact raw-state coverage by canonical endpoints would be false. -/
theorem raw_metadata_separator {ambient : Nat} (allowed : List Token) (binder : String)
    (name : Fin (ambient + 1)) (key : Token) (admitted : key ∈ allowed) :
    EquationEquiv (base allowed) language
      (State.pattern (⟨.exposed, name, key⟩ : State ambient))
      (displayedPattern (some binder) ⟨.tucked, name, key⟩) ∧
      (displayedPattern (some binder) (⟨.tucked, name, key⟩ : State ambient)).hasCanonicalBinderMetadata
        = false := by
  constructor
  · exact Relation.EqvGen.symm _ _ (equationInstance_equivalent
      (raw_named_forward allowed (some binder) name key admitted))
  · simp [displayedPattern, pair, cell, EquationFrontierBinderProfile.guard, Token.pattern,
      Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

/-- Root matching and primitive interpretation cannot discover an equation in
a tree whose every subterm is inert for both authored orientations. -/
inductive EquationInert : Pattern → Prop where
  | bvar (index : Nat) : EquationInert (.bvar index)
  | apply (constructor : String) (arguments : List Pattern) :
      matchPattern extrusionEquation.left (.apply constructor arguments) = [] →
      matchPattern extrusionEquation.right (.apply constructor arguments) = [] →
      (∀ argument ∈ arguments, EquationInert argument) →
      EquationInert (.apply constructor arguments)
  | lambda (binder : Option String) (body : Pattern) :
      EquationInert body → EquationInert (.lambda binder body)

theorem EquationInert.no_root {pattern : Pattern} (inert : EquationInert pattern) :
    matchPattern extrusionEquation.left pattern = [] ∧
      matchPattern extrusionEquation.right pattern = [] := by
  cases inert with
  | bvar index => simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  | apply _ _ left right _ => exact ⟨left, right⟩
  | lambda _ _ _ => simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]

theorem EquationInert.of_fill (context : OneHoleContext) (redex : Pattern)
    (inert : EquationInert (context.fill redex)) : EquationInert redex := by
  induction context with
  | hole => exact inert
  | apply constructor before inner after ih =>
    cases inert with
    | apply _ _ _ _ arguments =>
      exact ih (arguments (inner.fill redex) (by simp))
  | lambda binder inner ih =>
    cases inert with
    | lambda _ _ body => exact ih body
  | multiLambda _ _ _ _ => cases inert
  | substBody _ _ _ => cases inert
  | substReplacement _ _ _ => cases inert
  | collection _ _ _ _ _ _ => cases inert

theorem inert_token (key : Token) : EquationInert key.pattern := by
  apply EquationInert.apply
  · cases key <;> simp [Token.label, extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · cases key <;> simp [Token.label, extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · simp

theorem inert_guard (key : Token) : EquationInert (EquationFrontierBinderProfile.guard key) := by
  apply EquationInert.apply
  · simp [extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [extrusionEquation,
      ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact inert_token key

theorem inert_cell (index : Nat) : EquationInert (cell index) := by
  apply EquationInert.apply
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact .bvar index

theorem inert_cell_guard (index : Nat) (key : Token) :
    EquationInert (pair (cell index) (EquationFrontierBinderProfile.guard key)) := by
  apply EquationInert.apply
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [cell, extrusionEquation, ScopedEquationControls.extrusionEquation,
      matchPattern, matchArgs]
  · intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact inert_cell index
    · exact inert_guard key

theorem inert_nu_cell (binder : Option String) (index : Nat) :
    EquationInert (.apply "Nu" [.lambda binder (cell index)]) := by
  apply EquationInert.apply
  · simp [cell, extrusionEquation, ScopedEquationControls.extrusionEquation,
      matchPattern, matchArgs]
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact .lambda binder _ (inert_cell index)

theorem inert_done_cell_guard (index : Nat) (key : Token) :
    EquationInert (done (pair (cell index) (EquationFrontierBinderProfile.guard key))) := by
  apply EquationInert.apply
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · simp [extrusionEquation, ScopedEquationControls.extrusionEquation, matchPattern]
  · intro argument member
    have equal := List.mem_singleton.mp member
    subst argument
    exact inert_cell_guard index key

theorem displayed_arguments_inert {ambient : Nat} (binder : Option String)
    (state : State ambient) (constructor : String) (arguments : List Pattern)
    (shape : displayedPattern binder state = .apply constructor arguments) :
    ∀ argument ∈ arguments, EquationInert argument := by
  cases state with
  | mk phase name key =>
    cases phase <;>
      simp only [displayedPattern, pair, Pattern.apply.injEq] at shape
    · rcases shape with ⟨rfl, rfl⟩
      intro argument member
      have equal := List.mem_singleton.mp member
      subst argument
      exact .lambda binder _ (inert_cell_guard name.val key)
    · rcases shape with ⟨rfl, rfl⟩
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact inert_nu_cell binder name.val
      · exact inert_guard key
    · rcases shape with ⟨rfl, rfl⟩
      intro argument member
      have equal := List.mem_singleton.mp member
      subst argument
      exact .lambda binder _ (inert_done_cell_guard name.val key)

theorem no_collection_carrier {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule language rule kind) : False := by
  obtain ⟨parameter, element, parameters⟩ := declaration.selfSorted
  have authored := declaration.authored
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tokenRule, guardRule, cellRule, pairRule, nuRule, doneRule,
    TypeExpr.name, TypeExpr.proc, TypeExpr.baseType] at parameters

theorem no_collection_algebra {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (declaration : AlgebraRule language rule kind algebra) : False := by
  have authored := declaration.authored
  have declared := declaration.declared
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tokenRule, guardRule, cellRule, pairRule, nuRule, doneRule] at declared

theorem no_collection_type {rule : GrammarRule} {kind : CollType} {elements : List Pattern}
    (member : rule ∈ language.terms)
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind elements) : False := by
  have declared := usesCollection_eq_true_of_collectionTypedAt member typed
  have absent : language.usesCollection kind = false := by cases kind <;> rfl
  rw [absent] at declared
  cases declared

theorem no_derived {source target : Pattern} (derived : DerivedInstance language source target) :
    False := by
  cases derived with
  | bagPerm member kindTyped _ => exact no_collection_type member kindTyped
  | setPerm member kindTyped _ => exact no_collection_type member kindTyped
  | setDedup member kindTyped => exact no_collection_type member kindTyped
  | flatten declaration _ _ => exact no_collection_algebra declaration
  | singleton declaration _ _ => exact no_collection_algebra declaration
  | unitElim declaration _ _ => exact no_collection_algebra declaration
  | emptyUnit declaration _ _ => exact no_collection_algebra declaration

theorem authored_equation_unique {equation : Equation}
    (authored : List.Mem equation language.equations) : equation = extrusionEquation := by
  change List.Mem equation [extrusionEquation] at authored
  cases authored with
  | head => rfl
  | tail _ rest => cases rest

theorem inert_no_instance (allowed : List Token) {source target : Pattern}
    (inert : EquationInert source) (equationInstance : EquationInstance (base allowed) language source target) :
    False := by
  obtain ⟨_, equationInstance⟩ := equationInstance
  cases equationInstance with
  | forward authored matched _ _ =>
    have equal := authored_equation_unique authored
    subst_vars
    rw [inert.no_root.1] at matched
    cases matched
  | reverse authored matched _ _ =>
    have equal := authored_equation_unique authored
    subst_vars
    rw [inert.no_root.2] at matched
    cases matched

theorem inert_no_generator (allowed : List Token) {source target : Pattern}
    (inert : EquationInert source) (generator : EquationGenerator (base allowed) language source target) :
    False := by
  rcases generator with equationInstance | derived
  · exact inert_no_instance allowed inert equationInstance
  · exact no_derived derived

/-- Every proper subterm of the admitted family is equation-inert. Structural
equation contexts therefore cannot hide another conversion below its root. -/
theorem equation_context_root {ambient : Nat} (allowed : List Token) (binder : Option String)
    (state : State ambient) (context : OneHoleContext) (redex contractum : Pattern)
    (generator : EquationGenerator (base allowed) language redex contractum)
    (source : context.fill redex = displayedPattern binder state) : context = .hole := by
  cases context with
  | hole => rfl
  | apply constructor before inner after =>
    have children := displayed_arguments_inert binder state constructor
      (before ++ inner.fill redex :: after) source.symm
    have inert := children (inner.fill redex) (by simp)
    exact False.elim (inert_no_generator allowed (inert.of_fill inner redex) generator)
  | lambda _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | multiLambda _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | substBody _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | substReplacement _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source
  | collection _ _ _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at source

theorem apply_match_shape (constructor : String) (patterns : List Pattern)
    (target : Pattern) (bindings : Bindings)
    (member : bindings ∈ matchPattern (.apply constructor patterns) target) :
    ∃ arguments, target = .apply constructor arguments ∧
      patterns.length = arguments.length ∧ bindings ∈ matchArgs patterns arguments := by
  cases target <;> simp only [matchPattern] at member
  all_goals try simp only [List.not_mem_nil] at member
  case apply other arguments =>
    split at member
    · rename_i selected
      have selected' : (constructor == other) = true ∧
          (patterns.length == arguments.length) = true := by
        simpa only [Bool.and_eq_true] using selected
      have nameEqual := beq_iff_eq.mp selected'.1
      have lengthEqual := beq_iff_eq.mp selected'.2
      subst_vars
      exact ⟨_, rfl, lengthEqual, member⟩
    · simp only [List.not_mem_nil] at member

theorem lambda_match_shape (body : Pattern) (target : Pattern) (bindings : Bindings)
    (member : bindings ∈ matchPattern (.lambda none body) target) :
    ∃ binder inner, target = .lambda binder inner ∧
      bindings ∈ matchPattern body inner := by
  cases target <;> simp only [matchPattern] at member
  all_goals try simp only [List.not_mem_nil] at member
  exact ⟨_, _, rfl, member⟩

theorem matchArgs_singleton (pattern target : Pattern) :
    matchArgs [pattern] [target] = matchPattern pattern target := by
  simp [matchArgs, mergeBindings]

theorem list_length_one {α : Type} (list : List α) (length : list.length = 1) :
    ∃ value, list = [value] := by
  cases list with
  | nil => simp at length
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons _ _ => simp at length

theorem list_length_two {α : Type} (list : List α) (length : list.length = 2) :
    ∃ first second, list = [first, second] := by
  cases list with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => simp at length
    | cons second rest =>
      cases rest with
      | nil => exact ⟨first, second, rfl⟩
      | cons _ _ => simp at length

theorem raw_left_match_shape (source : Pattern) (bindings : Bindings)
    (member : bindings ∈ matchPattern extrusionEquation.left source) :
    ∃ binder left right,
      source = .apply "Nu" [.lambda binder (pair left right)] ∧
      bindings = [("Q", right), ("P", left)] := by
  have outer := apply_match_shape "Nu" [.lambda none (pair (.fvar "P") (.fvar "Q"))]
    source bindings member
  obtain ⟨arguments, rfl, length, matched⟩ := outer
  obtain ⟨argument, rfl⟩ := list_length_one arguments length.symm
  rw [matchArgs_singleton] at matched
  obtain ⟨binder, body, rfl, matchedBody⟩ := lambda_match_shape _ argument bindings matched
  obtain ⟨arguments, rfl, length, matchedPair⟩ :=
    apply_match_shape "Pair" [.fvar "P", .fvar "Q"] body bindings matchedBody
  obtain ⟨left, right, rfl⟩ := list_length_two arguments length.symm
  simp [matchArgs, matchPattern, mergeBindings] at matchedPair
  exact ⟨binder, left, right, rfl, matchedPair⟩

theorem raw_right_match_shape (source : Pattern) (bindings : Bindings)
    (member : bindings ∈ matchPattern extrusionEquation.right source) :
    ∃ binder left right,
      source = pair (.apply "Nu" [.lambda binder left]) right ∧
      bindings = [("Q", right), ("P", left)] := by
  obtain ⟨arguments, rfl, length, matched⟩ :=
    apply_match_shape "Pair" [.apply "Nu" [.lambda none (.fvar "P")], .fvar "Q"]
      source bindings member
  obtain ⟨outer, right, rfl⟩ := list_length_two arguments length.symm
  simp only [matchArgs] at matched
  obtain ⟨initial, matchedOuter, merged⟩ := List.mem_flatMap.mp matched
  obtain ⟨arguments, rfl, length, matchedNu⟩ :=
    apply_match_shape "Nu" [.lambda none (.fvar "P")] outer initial matchedOuter
  obtain ⟨argument, rfl⟩ := list_length_one arguments length.symm
  rw [matchArgs_singleton] at matchedNu
  obtain ⟨binder, left, rfl, matchedP⟩ := lambda_match_shape _ argument initial matchedNu
  simp only [matchPattern, List.mem_singleton] at matchedP
  subst initial
  simp [matchPattern, mergeBindings] at merged
  exact ⟨binder, left, right, rfl, merged⟩

theorem raw_apply_right_match (bindings : Bindings) :
    matchPattern extrusionEquation.right (applyBindings bindings extrusionEquation.right) =
      [[("Q", applyBindings bindings (.fvar "Q")),
        ("P", applyBindings bindings (.fvar "P"))]] := by
  simp [extrusionEquation, ScopedEquationControls.extrusionEquation,
    applyBindings, matchPattern, matchArgs, mergeBindings]

theorem raw_apply_left_match (bindings : Bindings) :
    matchPattern extrusionEquation.left (applyBindings bindings extrusionEquation.left) =
      [[("Q", applyBindings bindings (.fvar "Q")),
        ("P", applyBindings bindings (.fvar "P"))]] := by
  simp [extrusionEquation, ScopedEquationControls.extrusionEquation,
    applyBindings, matchPattern, matchArgs, mergeBindings]

theorem inert_no_instance_target (allowed : List Token) {source target : Pattern}
    (inert : EquationInert target)
    (equationInstance : EquationInstance (base allowed) language source target) : False := by
  obtain ⟨_, equationInstance⟩ := equationInstance
  cases equationInstance with
  | forward authored _ _ reduct =>
    have equal := authored_equation_unique authored
    subst_vars
    have matched := inert.no_root.2
    rw [raw_apply_right_match] at matched
    cases matched
  | reverse authored _ _ reduct =>
    have equal := authored_equation_unique authored
    subst_vars
    have matched := inert.no_root.1
    rw [raw_apply_left_match] at matched
    cases matched

theorem inert_no_generator_target (allowed : List Token) {source target : Pattern}
    (inert : EquationInert target)
    (generator : EquationGenerator (base allowed) language source target) : False := by
  rcases generator with equationInstance | derived
  · exact inert_no_instance_target allowed inert equationInstance
  · exact no_derived derived

theorem equation_context_root_target {ambient : Nat} (allowed : List Token)
    (binder : Option String) (state : State ambient) (context : OneHoleContext)
    (redex contractum : Pattern)
    (generator : EquationGenerator (base allowed) language redex contractum)
    (target : context.fill contractum = displayedPattern binder state) : context = .hole := by
  cases context with
  | hole => rfl
  | apply constructor before inner after =>
    have children := displayed_arguments_inert binder state constructor
      (before ++ inner.fill contractum :: after) target.symm
    have inert := children (inner.fill contractum) (by simp)
    exact False.elim (inert_no_generator_target allowed (inert.of_fill inner contractum) generator)
  | lambda _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | multiLambda _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | substBody _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | substReplacement _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target
  | collection _ _ _ _ _ =>
    cases state with
    | mk phase name key => cases phase <;> simp [displayedPattern, pair, OneHoleContext.fill] at target

def rawValues (left right : Pattern) : Bindings := [("Q", right), ("P", left)]

theorem raw_instance_shape (allowed : List Token) {source target : Pattern}
    (equationInstance : EquationInstance (base allowed) language source target) :
    ∃ binder left right fuel result,
      PremisesAt (base allowed) language fuel (rawValues left right)
        extrusionEquation.premises result ∧
      ((source = .apply "Nu" [.lambda binder (pair left right)] ∧
          target = pair (nu left) right) ∨
        (source = pair (.apply "Nu" [.lambda binder left]) right ∧
          target = nu (pair left right))) := by
  obtain ⟨fuel, equationInstance⟩ := equationInstance
  cases equationInstance with
  | forward authored matched premises reduct =>
    have unique := authored_equation_unique authored
    subst_vars
    obtain ⟨binder, left, right, sourceEq, captures⟩ := raw_left_match_shape _ _ matched
    subst_vars
    have extension := premises.bindingsExtends
    have foundQ := extension "Q" right (by simp)
    have foundP := extension "P" left (by simp)
    refine ⟨binder, left, right, fuel, _, premises, Or.inl ⟨rfl, ?_⟩⟩
    simp [extrusionEquation, ScopedEquationControls.extrusionEquation,
      applyBindings, foundQ, foundP, pair, nu]
  | reverse authored matched premises reduct =>
    have unique := authored_equation_unique authored
    subst_vars
    obtain ⟨binder, left, right, sourceEq, captures⟩ := raw_right_match_shape _ _ matched
    subst_vars
    have extension := premises.bindingsExtends
    have foundQ := extension "Q" right (by simp)
    have foundP := extension "P" left (by simp)
    refine ⟨binder, left, right, fuel, _, premises, Or.inr ⟨rfl, ?_⟩⟩
    simp [extrusionEquation, ScopedEquationControls.extrusionEquation,
      applyBindings, foundQ, foundP, pair, nu]

theorem erasure_apply_shape (constructor : String) (arguments : List Pattern)
    (source : Pattern) (equal : source.eraseBinderMetadata = .apply constructor arguments) :
    ∃ rawArguments, source = .apply constructor rawArguments ∧
      rawArguments.map Pattern.eraseBinderMetadata = arguments := by
  cases source <;> simp only [Pattern.eraseBinderMetadata, Pattern.apply.injEq] at equal
  all_goals try contradiction
  obtain ⟨rfl, argumentsEqual⟩ := equal
  exact ⟨_, rfl, argumentsEqual⟩

theorem erasure_apply_one (constructor : String) (argument source : Pattern)
    (equal : source.eraseBinderMetadata = .apply constructor [argument]) :
    ∃ rawArgument, source = .apply constructor [rawArgument] ∧
      rawArgument.eraseBinderMetadata = argument := by
  obtain ⟨arguments, rfl, erased⟩ := erasure_apply_shape constructor [argument] source equal
  have length : arguments.length = 1 := by
    simpa using congrArg List.length erased
  obtain ⟨rawArgument, rfl⟩ := list_length_one arguments length
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at erased
  exact ⟨rawArgument, rfl, erased⟩

theorem erasure_apply_two (constructor : String) (first second source : Pattern)
    (equal : source.eraseBinderMetadata = .apply constructor [first, second]) :
    ∃ rawFirst rawSecond, source = .apply constructor [rawFirst, rawSecond] ∧
      rawFirst.eraseBinderMetadata = first ∧ rawSecond.eraseBinderMetadata = second := by
  obtain ⟨arguments, rfl, erased⟩ := erasure_apply_shape constructor [first, second] source equal
  have length : arguments.length = 2 := by
    simpa using congrArg List.length erased
  obtain ⟨rawFirst, rawSecond, rfl⟩ := list_length_two arguments length
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at erased
  exact ⟨rawFirst, rawSecond, rfl, erased⟩

theorem erasure_lambda_shape (body source : Pattern)
    (equal : source.eraseBinderMetadata = .lambda none body) :
    ∃ binder rawBody, source = .lambda binder rawBody ∧ rawBody.eraseBinderMetadata = body := by
  cases source <;> simp only [Pattern.eraseBinderMetadata, Pattern.lambda.injEq] at equal
  all_goals try contradiction
  exact ⟨_, _, rfl, equal.2⟩

theorem erasure_token (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = key.pattern) : source = key.pattern := by
  obtain ⟨arguments, rfl, erased⟩ := erasure_apply_shape key.label [] source equal
  have empty : arguments = [] := List.map_eq_nil_iff.mp erased
  subst arguments
  rfl

theorem erasure_guard (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = guard key) : source = guard key := by
  obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Guard" key.pattern source equal
  rw [erasure_token key argument erased]
  rfl

theorem erasure_cell (index : Nat) (source : Pattern)
    (equal : source.eraseBinderMetadata = cell index) : source = cell index := by
  obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Cell" (.bvar index) source equal
  have argumentEqual : argument = .bvar index := by
    cases argument <;> simp_all [Pattern.eraseBinderMetadata]
  rw [argumentEqual]
  rfl

theorem erasure_cell_guard (index : Nat) (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = pair (cell index) (guard key)) :
    source = pair (cell index) (guard key) := by
  obtain ⟨first, second, rfl, firstEq, secondEq⟩ :=
    erasure_apply_two "Pair" (cell index) (guard key) source equal
  rw [erasure_cell index first firstEq, erasure_guard key second secondEq]
  rfl

theorem erasure_done_cell_guard (index : Nat) (key : Token) (source : Pattern)
    (equal : source.eraseBinderMetadata = done (pair (cell index) (guard key))) :
    source = done (pair (cell index) (guard key)) := by
  obtain ⟨argument, rfl, erased⟩ :=
    erasure_apply_one "Done" (pair (cell index) (guard key)) source equal
  rw [erasure_cell_guard index key argument erased]
  rfl

theorem erasure_inverse {ambient : Nat} (source : Pattern) (state : State ambient)
    (equal : source.eraseBinderMetadata = state.pattern) :
    ∃ binder, source = displayedPattern binder state := by
  cases state with
  | mk phase name key =>
    cases phase with
    | tucked =>
      obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Nu" _ source equal
      obtain ⟨binder, body, rfl, erasedBody⟩ := erasure_lambda_shape _ argument erased
      rw [erasure_cell_guard name.val key body erasedBody]
      exact ⟨binder, rfl⟩
    | exposed =>
      obtain ⟨first, second, rfl, firstEq, secondEq⟩ := erasure_apply_two "Pair" _ _ source equal
      obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Nu" _ first firstEq
      obtain ⟨binder, body, rfl, erasedBody⟩ := erasure_lambda_shape _ argument erased
      rw [erasure_cell name.val body erasedBody, erasure_guard key second secondEq]
      exact ⟨binder, rfl⟩
    | finished =>
      obtain ⟨argument, rfl, erased⟩ := erasure_apply_one "Nu" _ source equal
      obtain ⟨binder, body, rfl, erasedBody⟩ := erasure_lambda_shape _ argument erased
      rw [erasure_done_cell_guard name.val key body erasedBody]
      exact ⟨binder, rfl⟩

theorem raw_instance_from_displayed {ambient : Nat} (allowed : List Token)
    (sourceBinder : Option String) (source : State ambient) (target : Pattern)
    (equationInstance : EquationInstance (base allowed) language
      (displayedPattern sourceBinder source) target) :
    ∃ next : State ambient, target = next.pattern ∧
      (EquationEdge allowed source next ∨ EquationEdge allowed next source) := by
  obtain ⟨binder, left, right, fuel, result, premises, shape⟩ :=
    raw_instance_shape allowed equationInstance
  cases source with
  | mk phase name key =>
    rcases shape with ⟨sourceEq, targetEq⟩ | ⟨sourceEq, targetEq⟩
    · cases phase with
      | tucked =>
        simp only [displayedPattern, pair, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        rcases sourceEq with ⟨rfl, rfl, rfl⟩
        have admitted := (raw_premises_spec allowed name.val key fuel result).mp premises
        exact ⟨⟨.exposed, name, key⟩, targetEq, Or.inl (.extrusion name key admitted.2)⟩
      | exposed => simp [displayedPattern, pair] at sourceEq
      | finished => simp [displayedPattern, done, pair] at sourceEq
    · cases phase with
      | tucked => simp [displayedPattern, pair] at sourceEq
      | exposed =>
        simp only [displayedPattern, pair, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        rcases sourceEq with ⟨⟨rfl, rfl⟩, rfl⟩
        have admitted := (raw_premises_spec allowed name.val key fuel result).mp premises
        exact ⟨⟨.tucked, name, key⟩, targetEq, Or.inr (.extrusion name key admitted.2)⟩
      | finished => simp [displayedPattern, pair] at sourceEq

theorem raw_instance_into_displayed {ambient : Nat} (allowed : List Token)
    (targetBinder : Option String) (target : State ambient) (source : Pattern)
    (equationInstance : EquationInstance (base allowed) language source
      (displayedPattern targetBinder target)) :
    ∃ (binder : Option String) (previous : State ambient), source = displayedPattern binder previous ∧
      (EquationEdge allowed previous target ∨ EquationEdge allowed target previous) := by
  obtain ⟨binder, left, right, fuel, result, premises, shape⟩ :=
    raw_instance_shape allowed equationInstance
  cases target with
  | mk phase name key =>
    rcases shape with ⟨sourceEq, targetEq⟩ | ⟨sourceEq, targetEq⟩
    · cases phase with
      | tucked => simp [displayedPattern, pair, nu] at targetEq
      | exposed =>
        simp only [displayedPattern, pair, nu, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at targetEq
        rcases targetEq with ⟨⟨rfl, rfl⟩, rfl⟩
        have admitted := (raw_premises_spec allowed name.val key fuel result).mp premises
        exact ⟨binder, ⟨.tucked, name, key⟩, sourceEq,
          Or.inl (.extrusion name key admitted.2)⟩
      | finished => simp [displayedPattern, pair, nu] at targetEq
    · cases phase with
      | tucked =>
        simp only [displayedPattern, pair, nu, Pattern.apply.injEq, Pattern.lambda.injEq,
          List.cons.injEq, and_true, true_and] at targetEq
        rcases targetEq with ⟨rfl, rfl, rfl⟩
        have admitted := (raw_premises_spec allowed name.val key fuel result).mp premises
        exact ⟨binder, ⟨.exposed, name, key⟩, sourceEq,
          Or.inr (.extrusion name key admitted.2)⟩
      | exposed => simp [displayedPattern, pair, nu] at targetEq
      | finished => simp [displayedPattern, pair, nu, done] at targetEq

theorem raw_context_from_displayed {ambient : Nat} (allowed : List Token)
    (binder : Option String) (source : State ambient) (target : Pattern)
    (contextual : EquationContextStep (base allowed) language
      (displayedPattern binder source) target) :
    ∃ next : State ambient, target = next.pattern ∧
      (EquationEdge allowed source next ∨ EquationEdge allowed next source) := by
  generalize sourceEq : displayedPattern binder source = rawSource at contextual
  cases contextual with
  | inContext context generator =>
    have root := equation_context_root allowed binder source context _ _ generator sourceEq.symm
    subst context
    simp only [OneHoleContext.fill] at sourceEq ⊢
    rw [← sourceEq] at generator
    rcases generator with equationInstance | derived
    · exact raw_instance_from_displayed allowed binder source _ equationInstance
    · exact False.elim (no_derived derived)

theorem raw_context_into_displayed {ambient : Nat} (allowed : List Token)
    (binder : Option String) (target : State ambient) (source : Pattern)
    (contextual : EquationContextStep (base allowed) language source
      (displayedPattern binder target)) :
    ∃ (previousBinder : Option String) (previous : State ambient),
      source = displayedPattern previousBinder previous ∧
        (EquationEdge allowed previous target ∨ EquationEdge allowed target previous) := by
  generalize targetEq : displayedPattern binder target = rawTarget at contextual
  cases contextual with
  | inContext context generator =>
    have root := equation_context_root_target allowed binder target context _ _ generator targetEq.symm
    subst context
    simp only [OneHoleContext.fill] at targetEq ⊢
    rw [← targetEq] at generator
    rcases generator with equationInstance | derived
    · exact raw_instance_into_displayed allowed binder target _ equationInstance
    · exact False.elim (no_derived derived)

theorem neighbor_equivalent {ambient : Nat} (allowed : List Token)
    {source target : State ambient}
    (neighbor : EquationEdge allowed source target ∨ EquationEdge allowed target source) :
    Relation.EqvGen (EquationEdge allowed) source target := by
  rcases neighbor with forward | reverse
  · exact .rel _ _ forward
  · exact .symm _ _ (.rel _ _ reverse)

/-- Full raw contextual closure retains the finite carrier after alpha
normalization. Both directions matter: `EqvGen` also admits incoming raw
instances, whose binder display names need not have been canonical. -/
theorem raw_equiv_admitted {ambient : Nat} (allowed : List Token) {left right : Pattern}
    (equivalent : EquationEquiv (base allowed) language left right) :
    (∀ source : State ambient, left.eraseBinderMetadata = source.pattern →
      ∃ target : State ambient, right.eraseBinderMetadata = target.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target) ∧
    (∀ target : State ambient, right.eraseBinderMetadata = target.pattern →
      ∃ source : State ambient, left.eraseBinderMetadata = source.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target) := by
  induction equivalent with
  | rel left right contextual =>
    constructor
    · intro source admitted
      obtain ⟨binder, rfl⟩ := erasure_inverse left source admitted
      obtain ⟨target, rfl, neighbor⟩ := raw_context_from_displayed allowed binder source right contextual
      exact ⟨target, Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target),
        neighbor_equivalent allowed neighbor⟩
    · intro target admitted
      obtain ⟨binder, rfl⟩ := erasure_inverse right target admitted
      obtain ⟨sourceBinder, source, rfl, neighbor⟩ :=
        raw_context_into_displayed allowed binder target left contextual
      exact ⟨source, displayed_erasure sourceBinder source, neighbor_equivalent allowed neighbor⟩
  | refl pattern =>
    constructor
    · intro source admitted
      exact ⟨source, admitted, .refl source⟩
    · intro target admitted
      exact ⟨target, admitted, .refl target⟩
  | symm left right equivalent ih =>
    constructor
    · intro source admitted
      obtain ⟨target, targetAdmitted, relation⟩ := ih.2 source admitted
      exact ⟨target, targetAdmitted, .symm _ _ relation⟩
    · intro target admitted
      obtain ⟨source, sourceAdmitted, relation⟩ := ih.1 target admitted
      exact ⟨source, sourceAdmitted, .symm _ _ relation⟩
  | trans left middle right first second firstIH secondIH =>
    constructor
    · intro source admitted
      obtain ⟨midpoint, midpointAdmitted, firstRelation⟩ := firstIH.1 source admitted
      obtain ⟨target, targetAdmitted, secondRelation⟩ := secondIH.1 midpoint midpointAdmitted
      exact ⟨target, targetAdmitted, .trans _ _ _ firstRelation secondRelation⟩
    · intro target admitted
      obtain ⟨midpoint, midpointAdmitted, secondRelation⟩ := secondIH.2 target admitted
      obtain ⟨source, sourceAdmitted, firstRelation⟩ := firstIH.2 midpoint midpointAdmitted
      exact ⟨source, sourceAdmitted, .trans _ _ _ firstRelation secondRelation⟩

theorem finite_equiv_raw {ambient : Nat} (allowed : List Token)
    {source target : State ambient}
    (equivalent : Relation.EqvGen (EquationEdge allowed) source target) :
    EquationEquiv (base allowed) language source.pattern target.pattern := by
  induction equivalent with
  | rel source target edge =>
    cases edge with
    | extrusion name key admitted =>
      simpa only [displayed_none] using equationInstance_equivalent
        (raw_named_forward allowed none name key admitted)
  | refl source => exact .refl source.pattern
  | symm source target relation ih => exact .symm _ _ ih
  | trans source middle target first second firstIH secondIH =>
    exact .trans _ _ _ firstIH secondIH

/-- Finite representatives are complete for the authored contextual equation
theory on its canonical alpha section, for every ambient context and snapshot. -/
theorem canonical_equation_comparison {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    EquationEquiv (base allowed) language source.pattern target.pattern ↔
      Relation.EqvGen (EquationEdge allowed) source target := by
  constructor
  · intro equivalent
    obtain ⟨next, normalized, relation⟩ :=
      (raw_equiv_admitted allowed equivalent).1 source
        (Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical source))
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target)] at normalized
    have equal := state_pattern_injective normalized
    subst next
    exact relation
  · exact finite_equiv_raw allowed

/-- Raw equation detours never leave the admitted finite alpha carrier. The
normalization readout preserves the exact indexed name and provider key. -/
theorem raw_class_normalization {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern)
    (equivalent : EquationEquiv (base allowed) language source.pattern rawTarget) :
    ∃ target : State ambient, rawTarget.eraseBinderMetadata = target.pattern ∧
      Relation.EqvGen (EquationEdge allowed) source target :=
  (raw_equiv_admitted allowed equivalent).1 source
    (Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical source))

theorem rewrite_noncontextual (rule : RewriteRule) (authored : rule ∈ language.rewrites) :
    NoncontextualPremises rule.premises := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl <;> exact .relationQuery .nil

theorem rewrite_matching (rule : RewriteRule) (authored : rule ∈ language.rewrites)
    (source : Pattern) :
    matchPatternForRule language rule source = matchPattern consumeRule.left source := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl <;> rw [matchPatternForRule_eq_syntactic]

theorem rewrite_premises (rule : RewriteRule) (authored : rule ∈ language.rewrites) :
    rule.premises = extrusionEquation.premises := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl <;> rfl

theorem raw_rule_target {ambient : Nat} (rule : RewriteRule)
    (authored : rule ∈ language.rewrites) (name : Fin (ambient + 1)) (key : Token) :
    applyBindingsForRule language rule (rawCaptured name.val key) =
      State.pattern (⟨.finished, name, key⟩ : State ambient) := by
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl
  all_goals rw [applyBindingsForRule_eq_syntactic]
  all_goals simp [applyRuleBindings, consumeRule, rawCaptured,
    applyBindingsScoped, applyBindingsScopedList, captureDepth, captureDepthList,
    State.pattern, nu, done, pair, cell, EquationFrontierBinderProfile.guard,
    Token.pattern, Substitution.liftBVars, Substitution.liftBVarsList]

theorem raw_consume_displayed {ambient : Nat} (sourceBinder : Option String)
    (name : Fin (ambient + 1)) (key : Token) :
    matchPattern consumeRule.left (displayedPattern sourceBinder ⟨.exposed, name, key⟩) =
      [rawCaptured name.val key] := by
  simp [consumeRule, displayedPattern, nu, pair, matchPattern, matchArgs,
    mergeBindings, rawCaptured]

theorem raw_step_displayed_spec {ambient : Nat} (allowed : List Token)
    (sourceBinder : Option String) (source : State ambient) (target : Pattern) :
    Step (base allowed) language (displayedPattern sourceBinder source) target ↔
      source.phase = .exposed ∧ source.key ∈ allowed ∧
        target = State.pattern (⟨.finished, source.name, source.key⟩ : State ambient) := by
  change Step (engineBasePremises (provider allowed)) language _ _ ↔ _
  rw [step_iff_rootStep_of_noncontextualRules rewrite_noncontextual]
  constructor
  · rintro ⟨rule, authored, initial, matched, final, premises, reduct⟩
    rw [rewrite_matching rule authored] at matched
    rw [rewrite_premises rule authored] at premises
    have premisesRel : PremisesAt (base allowed) language 0 initial
        extrusionEquation.premises final :=
      (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
        (show NoncontextualPremises extrusionEquation.premises from .relationQuery .nil)).mpr premises
    cases source with
    | mk phase name key =>
      cases phase with
      | tucked => simp [consumeRule, displayedPattern, pair, nu, matchPattern] at matched
      | finished => simp [consumeRule, displayedPattern, pair, nu, matchPattern] at matched
      | exposed =>
        rw [raw_consume_displayed] at matched
        have initialEq := List.mem_singleton.mp matched
        subst initial
        obtain ⟨finalEq, admitted⟩ := (raw_premises_spec allowed name.val key 0 final).mp premisesRel
        subst final
        rw [raw_rule_target rule authored] at reduct
        exact ⟨rfl, admitted, reduct.symm⟩
  · rintro ⟨phase, admitted, targetEq⟩
    cases source with
    | mk sourcePhase name key =>
      simp only at phase
      subst sourcePhase
      subst target
      refine ⟨consumeRule, by simp [language], rawCaptured name.val key, ?_,
        rawCaptured name.val key, ?_, ?_⟩
      · rw [matchPatternForRule_eq_syntactic, raw_consume_displayed]
        simp
      · rw [show consumeRule.premises = extrusionEquation.premises from rfl]
        exact (premisesAt_engineBase_iff_mem_applyPremisesWithEnv
          (show NoncontextualPremises extrusionEquation.premises from .relationQuery .nil)).mp
            ((raw_premises_spec allowed name.val key 0 _).mpr ⟨rfl, admitted⟩)
      · exact raw_rule_target consumeRule (by simp [language]) name key

theorem raw_step_comparison {ambient : Nat} (allowed : List Token)
    (sourceBinder : Option String) (source : State ambient) (target : Pattern) :
    Step (base allowed) language (displayedPattern sourceBinder source) target ↔
      ∃ (origin : Origin) (next : State ambient),
        Firing allowed source origin next ∧ target = next.pattern := by
  rw [raw_step_displayed_spec]
  constructor
  · rintro ⟨phase, admitted, targetEq⟩
    obtain ⟨row, found⟩ := List.mem_iff_getElem?.mp admitted
    cases source with
    | mk sourcePhase name key =>
      simp only at phase
      subst sourcePhase
      exact ⟨⟨0, row⟩, ⟨.finished, name, key⟩, .consume name key 0 row found, targetEq⟩
  · rintro ⟨origin, next, firing, targetEq⟩
    cases firing with
    | consume name key declaration row found =>
      exact ⟨rfl, List.mem_of_getElem? found, targetEq⟩

/-- Raw execution is invariant under the declared alpha section on this
whole binder-aware carrier, rather than only on selected ground examples. -/
theorem raw_step_normalization {ambient : Nat} (allowed : List Token)
    (source : Pattern) (state : State ambient) (target : Pattern)
    (admitted : source.eraseBinderMetadata = state.pattern) :
    Step (base allowed) language source target ↔
      Step (base allowed) language state.pattern target := by
  obtain ⟨binder, rfl⟩ := erasure_inverse source state admitted
  rw [raw_step_displayed_spec, ← displayed_none state, raw_step_displayed_spec]

/-- The finite operational profile is a proved restriction of the genuinely
generated GSLT relation, including arbitrary contextual equation detours at
both ends. The original raw relation has not been replaced by the enumerator. -/
theorem generated_gslt_step_comparison {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    StepModuloEquations (base allowed) language source.pattern target.pattern ↔
      EquationFrontierBinderProfile.Step allowed source target := by
  constructor
  · rintro ⟨redex, contractum, before, firing, after⟩
    obtain ⟨representative, normalized, beforeFinite⟩ :=
      raw_class_normalization allowed source redex before
    obtain ⟨binder, redexEq⟩ := erasure_inverse redex representative normalized
    rw [redexEq] at firing
    obtain ⟨origin, next, primitive, contractumEq⟩ :=
      (raw_step_comparison allowed binder representative contractum).mp firing
    rw [contractumEq] at after
    have afterFinite := (canonical_equation_comparison allowed next target).mp after
    exact ⟨representative, ⟨origin, next⟩, beforeFinite, primitive, afterFinite⟩
  · rintro ⟨representative, event, before, firing, after⟩
    refine ⟨representative.pattern, event.target.pattern, finite_equiv_raw allowed before,
      ?_, finite_equiv_raw allowed after⟩
    simpa only [displayed_none] using
      (raw_step_comparison allowed none representative event.target.pattern).mpr
        ⟨event.origin, event.target, firing, rfl⟩

theorem raw_modulo_class_normalization {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern)
    (step : StepModuloEquations (base allowed) language source.pattern rawTarget) :
    ∃ target : State ambient, rawTarget.eraseBinderMetadata = target.pattern ∧
      EquationFrontierBinderProfile.Step allowed source target := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  obtain ⟨representative, normalized, beforeFinite⟩ :=
    raw_class_normalization allowed source redex before
  obtain ⟨binder, redexEq⟩ := erasure_inverse redex representative normalized
  rw [redexEq] at firing
  obtain ⟨origin, next, primitive, contractumEq⟩ :=
    (raw_step_comparison allowed binder representative contractum).mp firing
  rw [contractumEq] at after
  obtain ⟨target, targetNormalized, afterFinite⟩ :=
    raw_class_normalization allowed next rawTarget after
  exact ⟨target, targetNormalized, representative, ⟨origin, next⟩,
    beforeFinite, primitive, afterFinite⟩

/-- The checked finite certificate covers the raw equation class after its
existing alpha quotient. A named raw endpoint need not itself be the canonical
representative: the comparison quantifies the represented member of its class. -/
theorem alpha_equation_certificate_comparison {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern) :
    (∃ representative : Pattern,
      EquationEquiv (base allowed) language source.pattern representative ∧
        Pattern.AlphaEquiv representative rawTarget) ↔
      ∃ target ∈ (certificate allowed source).representatives source,
        Pattern.AlphaEquiv target.pattern rawTarget := by
  constructor
  · rintro ⟨raw, equivalent, alpha⟩
    obtain ⟨target, normalized, finite⟩ := raw_class_normalization allowed source raw equivalent
    refine ⟨target, (representatives_complete allowed source target).mpr finite, ?_⟩
    change target.pattern.eraseBinderMetadata = rawTarget.eraseBinderMetadata
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target),
      ← normalized]
    exact alpha
  · rintro ⟨target, represented, alpha⟩
    exact ⟨target.pattern,
      finite_equiv_raw allowed ((representatives_complete allowed source target).mp represented),
      alpha⟩

/-- Both raw equation detours and operational targets are covered on the
alpha quotient by the actual checked occurrence frontier. Endpoint coverage
forgets authored origins; the occurrence theorem remains a separate readout. -/
theorem alpha_operational_frontier_comparison {ambient : Nat} (allowed : List Token)
    (source : State ambient) (rawTarget : Pattern) :
    (∃ representative : Pattern,
      StepModuloEquations (base allowed) language source.pattern representative ∧
        Pattern.AlphaEquiv representative rawTarget) ↔
      ∃ target : State ambient, EquationFrontierBinderProfile.Step allowed source target ∧
        Pattern.AlphaEquiv target.pattern rawTarget := by
  constructor
  · rintro ⟨raw, step, alpha⟩
    obtain ⟨target, normalized, finite⟩ := raw_modulo_class_normalization allowed source raw step
    refine ⟨target, finite, ?_⟩
    change target.pattern.eraseBinderMetadata = rawTarget.eraseBinderMetadata
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical (state_canonical target),
      ← normalized]
    exact alpha
  · rintro ⟨target, step, alpha⟩
    exact ⟨target.pattern, (generated_gslt_step_comparison allowed source target).mpr step, alpha⟩

theorem generated_frontier_target_classes {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Quotient.mk (Relation.EqvGen.setoid (EquationEdge allowed)) target ∈
      FiniteEquationCoverage.classFrontier (EquationEdge allowed) (occurrences allowed) Event.target
        (certificate allowed source) source ↔
      (gsltModuloEquations (base allowed) language).rewrites source.pattern target.pattern := by
  change _ ↔ StepModuloEquations (base allowed) language source.pattern target.pattern
  rw [generated_gslt_step_comparison]
  exact frontier_target_classes allowed source target

theorem generated_frontier_diamond {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : State ambient → Bool)
    (invariant : ∀ before after, Relation.EqvGen (EquationEdge allowed) before after →
      test before = test after) :
    (FiniteEquationCoverage.endpoints Event.target (frontier allowed source)).any test = true ↔
      ∃ target : State ambient,
        (gsltModuloEquations (base allowed) language).rewrites source.pattern target.pattern ∧
          test target = true := by
  simp only [show (gsltModuloEquations (base allowed) language).rewrites =
    StepModuloEquations (base allowed) language from rfl, generated_gslt_step_comparison]
  exact frontier_diamond allowed source test invariant

/-- This is the outgoing universal modality. It is distinct from OSLF's
incoming adjoint box, whose predicate lives on predecessors. -/
theorem generated_frontier_outgoing_universal {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : State ambient → Bool)
    (invariant : ∀ before after, Relation.EqvGen (EquationEdge allowed) before after →
      test before = test after) :
    (FiniteEquationCoverage.endpoints Event.target (frontier allowed source)).all test = true ↔
      ∀ target : State ambient,
        (gsltModuloEquations (base allowed) language).rewrites source.pattern target.pattern →
          test target = true := by
  simp only [show (gsltModuloEquations (base allowed) language).rewrites =
    StepModuloEquations (base allowed) language from rfl, generated_gslt_step_comparison]
  exact frontier_outgoing_universal allowed source test invariant

theorem generated_frontier_empty_iff {ambient : Nat} (allowed : List Token)
    (source : State ambient) :
    frontier allowed source = [] ↔
      ¬ ∃ target : Pattern,
        (gsltModuloEquations (base allowed) language).rewrites source.pattern target := by
  rw [frontier_empty_iff]
  constructor
  · intro noFinite ⟨rawTarget, rawStep⟩
    obtain ⟨target, _, finite⟩ := raw_modulo_class_normalization allowed source rawTarget rawStep
    exact noFinite ⟨target, finite⟩
  · intro noRaw ⟨target, finite⟩
    exact noRaw ⟨target.pattern, (generated_gslt_step_comparison allowed source target).mpr finite⟩

end Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated
