import Mettapedia.Languages.HOLLight.MeTTa.Lookup
import Mettapedia.Languages.HOLLight.MeTTa.TermSubstitution
import Mettapedia.Languages.HOLLight.MeTTa.TermInstantiation
import Mettapedia.Languages.HOLLight.MeTTa.TermJudgment
import Mettapedia.Languages.HOLLight.MeTTa.ContextLookup
import Mettapedia.Languages.HOLLight.MeTTa.TypeFormation
import Mettapedia.Languages.HOLLight.MeTTa.Initialization
import Mettapedia.Languages.HOLLight.MeTTa.Equality
import Mettapedia.Languages.HOLLight.MeTTa.TypeMatching
import Mettapedia.Languages.HOLLight.MeTTa.TermReading
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-!
# Authored HOL operations in the existing generated MeTTa language

The source execution proofs are transported through PeTTa's configuration
language, with its actual control and continuation rules. The resulting paths
retain the complete store and the ordered answers. No HOL-checking primitive
is added to the generated language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Execution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.Framework.TypeSynthesis (langGSLTUsing)
open ConfigurationEncoding
open Mettapedia.Languages.OpenTheory

/-- Once an authored evaluation has a pure return, every completed execution
has exactly that store, singleton answer and empty I/O observation. -/
theorem completed_observation_iff (script : SpaceSemantics.Program)
    (bindings : Subst) (before expected : Effects.State) (expression value : Atom)
    (returned : Eval.PureReturns script bindings before expression expected value)
    (after : Effects.State) (answers input output : List Atom) :
    (Eval.theory script).MultiStep
      { state := before, control := .evaluate bindings expression }
      (Eval.finished after answers input output) ↔
      after = expected ∧ answers = [value] ∧ input = [] ∧ output = [] := by
  constructor
  · intro path
    obtain ⟨firstFuel, first⟩ :=
      Eval.path_has_sufficient_fuel script _ after answers input output path
    obtain ⟨secondFuel, second⟩ :=
      Eval.pure_returns_has_sufficient_fuel script bindings before expected expression value returned
    exact Eval.completed_result_unique script firstFuel secondFuel _ after expected
      answers input output [value] [] [] first second
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact returned

/-- The same exact observation characterizes all completed finite runs,
independently of the fuel required to reach it. -/
theorem completed_run_observation_iff (script : SpaceSemantics.Program)
    (bindings : Subst) (before expected : Effects.State) (expression value : Atom)
    (returned : Eval.PureReturns script bindings before expression expected value)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ fuel, Eval.run script fuel
      { state := before, control := .evaluate bindings expression } =
        .complete after answers input output) ↔
      after = expected ∧ answers = [value] ∧ input = [] ∧ output = [] :=
  (Eval.completed_run_iff_path script _ after answers input output).trans
    (completed_observation_iff script bindings before expected expression value returned
      after answers input output)

/-- Generated-language paths have exactly the same completed observations;
reflection excludes additional completed answers introduced by the encoding. -/
theorem generated_observation_iff (script : SpaceSemantics.Program)
    (bindings : Subst) (before expected : Effects.State) (expression value : Atom)
    (returned : Eval.PureReturns script bindings before expression expected value)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv script)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state := before, control := .evaluate bindings expression } names) target ∧
      decode target = some (Eval.finished after answers input output)) ↔
      after = expected ∧ answers = [value] ∧ input = [] ∧ output = [] :=
  (ConfigurationLanguageDef.completed_run_iff_generated_path script _ names vacant covers
    after answers input output).symm.trans
      (completed_run_observation_iff script bindings before expected expression value returned
        after answers input output)

/-- Transport a proved authored evaluation through the existing language
definition, retaining its final store, answer and I/O readout. -/
theorem generated_return_of_pure_return (script : SpaceSemantics.Program)
    (bindings : Subst) (before after : Effects.State) (expression value : Atom)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (returned : Eval.PureReturns script bindings before expression after value) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv script)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state := before, control := .evaluate bindings expression } names) target ∧
      decode target = some (Eval.finished after [value] [] []) := by
  obtain ⟨finalNames, path, finalVacant, finalCovers⟩ :=
    ConfigurationLanguageDef.path_realized script _ _ names vacant covers returned
  exact ⟨_, path, decode_encode _ finalNames finalVacant finalCovers⟩

/-- All ten primitive request forms compute their ordered premise occurrences
by execution in the generated PeTTa language. -/
theorem authored_premises_generated (bindings : Subst) (state : Effects.State)
    (kind : InferenceKind) (payload first second : Atom) (name : String)
    (captured : applySubst bindings (.var name) = Premises.request kind payload first second)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:premises", .var name]) } names) target ∧
      decode target = some (Eval.finished state
        [Premises.keys (Premises.occurrences kind first second)] [] []) := by
  exact generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (Premises.authored_premises_return bindings state kind payload first second name captured)

/-- First-match lookup of declarations, proof references or substitution entries
is an authored path in the same generated language. Captured values stay data. -/
theorem authored_lookup_generated (bindings : Subst) (state : Effects.State) (key : Atom)
    (entries : List (Atom × Atom)) (keyName entriesName : String)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (capturedEntries : applySubst bindings (.var entriesName) = Lookup.table entries)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:lookup", .var keyName, .var entriesName]) } names) target ∧
      decode target = some (Eval.finished state [Lookup.answer (entries.lookup key)] [] []) := by
  exact generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (Lookup.authored_lookup_return bindings state key entries keyName entriesName
      capturedKey capturedEntries)

/-- The source's first-match simultaneous type action is a path of the same
generated language for arbitrary finite types and maplet lists. -/
theorem authored_type_substitution_generated (operators : TypeOp → Atom) (bindings : Subst)
    (state : Effects.State) (entries : List (Ty × Ty)) (type : Ty) (entriesKey typeKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = TypeSubstitution.maplets operators entries)
    (capturedType : applySubst bindings (.var typeKey) = TypeSubstitution.typeAtom operators type)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:type-subst", .var entriesKey, .var typeKey]) } names) target ∧
      decode target = some (Eval.finished state
        [TypeSubstitution.typeAtom operators ((SourceSubstitution.typeSubstitution entries).apply type)] [] []) := by
  exact generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (TypeSubstitution.authored_type_substitution_return operators bindings state entries type
      entriesKey typeKey capturedEntries capturedType)

/-- Registered free-variable substitution remains authored computation in
the generated language, retaining its full contextual representation. -/
theorem authored_term_substitution_generated (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : Effects.State)
    (entries : List (SourceVar × CheckedSourceTerm))
    (entriesFormed : ∀ entry ∈ entries, SignatureFormation.TypeFormed theory.signature entry.1.ty)
    (context : List Ty) (term : DBTerm) (formed : SignatureFormation.AnnotationsFormed theory.signature term)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = TermSubstitution.table Representation.registeredOperatorAtom constants entries)
    (capturedTerm : applySubst bindings (.var termKey) = Representation.termAtom Representation.registeredOperatorAtom constants context term)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:term-subst", .var entriesKey, .var termKey]) } names) target ∧
      decode target = some (Eval.finished state
        [Representation.termAtom Representation.registeredOperatorAtom constants context
          ((TermSubst.mk TypeSubst.empty entries).applyDB term)] [] []) := by
  exact generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (TermSubstitution.authored_registered_term_substitution_return theory constants bindings state entries
      entriesFormed context term formed entriesKey termKey capturedEntries capturedTerm)

/-- Type instantiation transports the binder context as well as the term.
The generated path retains the same ordered result and complete store. -/
theorem authored_type_instantiation_generated (operators : TypeOp → Atom) (constants : Const → Atom)
    (bindings : Subst) (state : Effects.State) (entries : List (Ty × Ty)) (context : List Ty)
    (term : DBTerm) (type : Ty) (checked : term.inferType context = some type)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = TypeSubstitution.maplets operators entries)
    (capturedTerm : applySubst bindings (.var termKey) = Representation.termAtom operators constants context term)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:term-inst-type", .var entriesKey, .var termKey]) } names) target ∧
      decode target = some (Eval.finished state
        [Representation.termAtom operators constants (context.map (SourceSubstitution.typeSubstitution entries).apply)
          ((SourceSubstitution.typeOnlySubstitution entries).raw.applyDB term)] [] []) := by
  exact generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (TermInstantiation.authored_type_instantiation_return operators constants bindings state entries context term type checked
      entriesKey termKey capturedEntries capturedTerm)

/-- Shared STT type judgments are computed by the authored program inside
the generated PeTTa language, with the same complete final observation. -/
theorem authored_term_type_generated (constants : Const → Atom) (bindings : Subst)
    (state : Effects.State) (context : List Ty) (term : DBTerm) (type : Ty)
    (checked : term.inferType context = some type) (termKey : String)
    (capturedTerm : applySubst bindings (.var termKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants context term)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:term-type", .var termKey]) } names) target ∧
      decode target = some (Eval.finished state
        [.expression [.symbol "Some", TypeSubstitution.typeAtom Representation.registeredOperatorAtom type]] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (TermJudgment.authored_term_type_return constants bindings state context term type checked termKey capturedTerm)

/-- The declared context's typed names enter the same generated execution
language through the authored nearest-binder lookup. -/
theorem authored_bound_index_generated (theory : DefinitionAdapters.TheoryContext)
    (needle : SourceVar) (needleFormed : SignatureFormation.TypeFormed theory.signature needle.ty)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed theory.signature binder.ty)
    (offset : Nat) (bindings : Subst) (state : Effects.State) (needleKey contextKey indexKey : String)
    (capturedNeedle : applySubst bindings (.var needleKey) =
      Representation.sourceVariableAtom Representation.registeredOperatorAtom needle)
    (capturedContext : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (capturedIndex : applySubst bindings (.var indexKey) = .grounded (.int offset))
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:bound-index", .var needleKey, .var contextKey, .var indexKey]) } names) target ∧
      decode target = some (Eval.finished state [ContextLookup.indexAnswer offset (boundIndex needle context)] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (ContextLookup.authored_bound_index_return theory needle needleFormed context contextFormed offset
      bindings state needleKey contextKey indexKey capturedNeedle capturedContext capturedIndex)

/-- Completed authored runs accept a resolved source type exactly when the
existing shared signature-formation judgment holds. -/
theorem authored_type_formation_admission_iff (theory : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table theory) (origin : TypeOp → Atom)
    (bindings : Subst) (state : Effects.State) (type : Ty)
    (resolved : TypeFormation.Resolved theory.signature type) (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = TypeSubstitution.typeAtom Representation.registeredOperatorAtom type) :
    (∃ fuel, Eval.run program fuel
      { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) } =
      .complete state [Effects.boolean true] [] []) ↔ SignatureFormation.TypeFormed theory.signature type := by
  have observation := completed_run_observation_iff program bindings state state _ _
    (TypeFormation.authored_type_formed_return theory table origin bindings state type resolved
      operatorsKey typeKey capturedOperators capturedType) state [Effects.boolean true] [] []
  simpa [Effects.boolean, SignatureFormation.typeFormedB_eq_true_iff] using observation

/-- Type admission is also reflected by the actual generated GSLT, rather
than only by the evaluator relation. Source resolution is a separate boundary. -/
theorem generated_type_formation_admission_iff (theory : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table theory) (origin : TypeOp → Atom)
    (bindings : Subst) (state : Effects.State) (type : Ty)
    (resolved : TypeFormation.Resolved theory.signature type) (operatorsKey typeKey : String)
    (capturedOperators : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table origin)
    (capturedType : applySubst bindings (.var typeKey) = TypeSubstitution.typeAtom Representation.registeredOperatorAtom type)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    (∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:type-formed", .var operatorsKey, .var typeKey]) } names) target ∧
      decode target = some (Eval.finished state [Effects.boolean true] [] [])) ↔
      SignatureFormation.TypeFormed theory.signature type := by
  have observation := generated_observation_iff program bindings state state _ _
    (TypeFormation.authored_type_formed_return theory table origin bindings state type resolved
      operatorsKey typeKey capturedOperators capturedType) names vacant covers state [Effects.boolean true] [] []
  simpa [Effects.boolean, SignatureFormation.typeFormedB_eq_true_iff] using observation

/-- The actual generated language constructs exactly the admitted primitive
signature, supplied commitments and empty proof history of initialization. -/
theorem authored_initial_state_generated (bindings : Subst) (state : Effects.State)
    (commitments : Atom) (commitmentsKey : String)
    (captured : applySubst bindings (.var commitmentsKey) = commitments)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:initial", .var commitmentsKey]) } names) target ∧
      decode target = some (Eval.finished state [Initialization.initialState commitments] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (Initialization.authored_initial_state_return bindings state commitments commitmentsKey captured)

/-- The retained equality-construction program reaches the independently
specified shared STT result through the generated configuration language. -/
theorem authored_equality_generated (constants : Const → Atom) (bindings : Subst) (state : Effects.State)
    (context : List Ty) (left right : DBTerm) (type : Ty)
    (leftChecked : left.inferType context = some type)
    (rightChecked : right.inferType context = some type)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var rightKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants context right)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:equation", .var leftKey, .var rightKey]) } names) target ∧
      decode target = some (Eval.finished state
        [.expression [.symbol "Some", Representation.termAtom Representation.registeredOperatorAtom constants context
          (CanonicalTerm.equalityDB type left right)]] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (Equality.authored_equation_return constants bindings state context left right type leftChecked rightChecked
      equalityIdentity leftKey rightKey leftCaptured rightCaptured)

/-- The same source operation refuses operands at distinct admitted types.
The generated execution retains that refusal and the original store. -/
theorem authored_wrong_equality_type_generated (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : Effects.State)
    (context : List Ty) (left right : DBTerm) (leftType rightType : Ty)
    (leftChecked : left.inferType context = some leftType)
    (rightChecked : right.inferType context = some rightType)
    (leftFormed : SignatureFormation.TypeFormed theory.signature leftType)
    (rightFormed : SignatureFormation.TypeFormed theory.signature rightType)
    (different : rightType ≠ leftType) (leftKey rightKey : String)
    (leftCaptured : applySubst bindings (.var leftKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants context left)
    (rightCaptured : applySubst bindings (.var rightKey) =
      Representation.termAtom Representation.registeredOperatorAtom constants context right)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:equation", .var leftKey, .var rightKey]) } names) target ∧
      decode target = some (Eval.finished state [.symbol "None"] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (Equality.authored_wrong_type_refused theory constants bindings state context left right leftType rightType
      leftChecked rightChecked leftFormed rightFormed different leftKey rightKey leftCaptured rightCaptured)

/-- Actual completed source executions accept exactly the instances of the
registered constant schema. A caller cannot supply the accepted table as an
assumption: it must occur as the result of executing the retained matcher. -/
theorem authored_matching_accepts_iff (world : DefinitionAdapters.TheoryContext)
    (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : SignatureFormation.TypeFormed world.signature schema)
    (occurrenceFormed : SignatureFormation.TypeFormed world.signature occurrence)
    (bindings : Subst) (state : Effects.State) (schemaKey instanceKey assignmentsKey : String)
    (schemaCaptured : applySubst bindings (.var schemaKey) =
      TypeSubstitution.typeAtom Representation.registeredOperatorAtom schema)
    (instanceCaptured : applySubst bindings (.var instanceKey) =
      TypeSubstitution.typeAtom Representation.registeredOperatorAtom occurrence)
    (assignmentsCaptured : applySubst bindings (.var assignmentsKey) = TypeMatching.assignmentsAtom TypeSubst.empty) :
    (∃ payload : Atom, (Eval.theory program).MultiStep
      { state, control := .evaluate bindings (.expression [.symbol "hol-light:type-match",
        .var schemaKey, .var instanceKey, .var assignmentsKey]) }
      (Eval.finished state [.expression [.symbol "Some", payload]] [] [])) ↔
        SignatureFormation.ConstantInstance world.signature constant occurrence := by
  have returned := TypeMatching.authored_match_return world schema occurrence schemaFormed occurrenceFormed
    TypeSubst.empty (by simp [HOLLight.TypeMatching.AssignmentsFormed, TypeSubst.empty, TypeSubst.lookup])
    bindings state schemaKey instanceKey assignmentsKey schemaCaptured instanceCaptured assignmentsCaptured
  rw [← HOLLight.TypeMatching.constant_admission_iff world.signature constant schema occurrence registered]
  constructor
  · rintro ⟨payload, path⟩
    have observed := (completed_observation_iff program bindings state state _ _ returned state
      [.expression [.symbol "Some", payload]] [] []).mp path
    have equal := List.singleton_inj.mp observed.2.1
    cases matched : HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty with
    | none => simp [matched, TypeMatching.answer, Lookup.answer] at equal
    | some after => exact ⟨after, rfl⟩
  · rintro ⟨after, matched⟩
    exact ⟨TypeMatching.assignmentsAtom after,
      by simpa [matched, TypeMatching.answer, Lookup.answer] using returned⟩

/-- The matcher is an authored path of the existing generated PeTTa GSLT,
with the complete source state and exact success/refusal observation. -/
theorem authored_matching_generated (world : DefinitionAdapters.TheoryContext)
    (schema occurrence : Ty)
    (schemaFormed : SignatureFormation.TypeFormed world.signature schema)
    (occurrenceFormed : SignatureFormation.TypeFormed world.signature occurrence)
    (assignments : TypeSubst)
    (assignmentsFormed : HOLLight.TypeMatching.AssignmentsFormed world.signature assignments)
    (bindings : Subst) (state : Effects.State) (schemaKey instanceKey assignmentsKey : String)
    (schemaCaptured : applySubst bindings (.var schemaKey) =
      TypeSubstitution.typeAtom Representation.registeredOperatorAtom schema)
    (instanceCaptured : applySubst bindings (.var instanceKey) =
      TypeSubstitution.typeAtom Representation.registeredOperatorAtom occurrence)
    (assignmentsCaptured : applySubst bindings (.var assignmentsKey) = TypeMatching.assignmentsAtom assignments)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:type-match", .var schemaKey, .var instanceKey, .var assignmentsKey]) } names) target ∧
      decode target = some (Eval.finished state
        [TypeMatching.answer (HOLLight.TypeMatching.matchType schema occurrence assignments)] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (TypeMatching.authored_match_return world schema occurrence schemaFormed occurrenceFormed assignments
      assignmentsFormed bindings state schemaKey instanceKey assignmentsKey schemaCaptured instanceCaptured assignmentsCaptured)

/-- General source reading, including arbitrary applications and nested
binders, runs through the existing generated configuration language. -/
theorem authored_read_generated (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (context : List SourceVar)
    (contextFormed : ∀ binder ∈ context, SignatureFormation.TypeFormed world.signature binder.ty)
    (annotations : SignatureFormation.AnnotationsFormed world.signature (source.toDB context))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : Effects.State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ cell, cell ∉ names → state.cells cell = none) :
    ∃ target : Pattern,
      (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
        ConfigurationLanguageDef.language).MultiStep
        (encode { state, control := .evaluate bindings (.expression
          [.symbol "hol-light:read-term", .var operatorsKey, .var constantsKey, .var contextKey, .var sourceKey]) } names) target ∧
      decode target = some (Eval.finished state [.expression [.symbol "Some",
        Representation.termAtom Representation.registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]] [] []) :=
  generated_return_of_pure_return program bindings state state _ _ names vacant covers
    (TermReading.authored_read_return world table origins constants source resolved context contextFormed annotations
      type typed bindings state operatorsKey constantsKey contextKey sourceKey
      operatorsCaptured constantsCaptured contextCaptured sourceCaptured)

end Mettapedia.Languages.HOLLight.MeTTa.Execution
