import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations
import Mettapedia.Languages.HOLLight.MeTTa.Execution
import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution
import Mettapedia.Languages.HOLLight.MeTTa.DeductionAntisymmetry
import Mettapedia.Languages.HOLLight.MeTTa.Beta
import Mettapedia.Languages.HOLLight.MeTTa.TypeInstantiation
import Mettapedia.Languages.HOLLight.MeTTa.TermInstantiationRule
import Mettapedia.Languages.HOLLight.MeTTa.ProofEvents
import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorizationControls
import Mettapedia.Languages.HOLLight.MeTTa.AxiomExecution

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

/-!
# Authored HOL operations on native typed configuration data

The actual source execution laws earn paths in the existing native explicit
state graph. Exact endpoints retain bindings, store, ordered answers and I/O.
Both endpoints have native Data formation and its constructor-algebra meaning.
The operational graph remains separate from dependent definitional equality.

This is a source/configuration bridge. It neither verifies the C translator
nor turns a represented HOL conclusion into a native dependent proof term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

/-- A completed observation retains the entire native configuration. Its
finite cell support is part of the encoding authorization at both ends. -/
def Returns (bindings : Subst) (before : Effects.State) (expression : Atom)
    (names : List String) (after : Effects.State) (answers input output : List Atom) : Prop :=
  ∃ finalNames,
    (NativePeTTaConfigurations.theory program).MultiStep
      (NativePeTTaConfigurations.encode { state := before, control := .evaluate bindings expression } names)
      (NativePeTTaConfigurations.encode (Eval.finished after answers input output) finalNames) ∧
    NamedSpaces.Store.EmptyTail after [] ∧
    (∀ name, name ∉ finalNames → after.cells name = none)

/-- The complete native state graph reflects actual source execution in both
directions. This law requires neither a predetermined answer nor termination. -/
theorem returns_iff_source_path (bindings : Subst) (before : Effects.State)
    (expression : Atom) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings before expression names after answers input output ↔
      (Eval.theory program).MultiStep
        { state := before, control := .evaluate bindings expression }
        (Eval.finished after answers input output) := by
  constructor
  · rintro ⟨finalNames, path, targetVacant, targetCovers⟩
    obtain ⟨decodedAfter, decoded, sourcePath⟩ := NativePeTTaConfigurations.path_reflects path
      { state := before, control := .evaluate bindings expression }
      (NativePeTTaConfigurations.decode_encode _ names vacant covers)
    rw [NativePeTTaConfigurations.decode_encode _ finalNames targetVacant targetCovers] at decoded
    have same := Option.some.inj decoded
    subst decodedAfter
    exact sourcePath
  · intro path
    exact NativePeTTaConfigurations.path_lifts path names vacant covers

/-- Once an actual authored operation has a proved return, its native paths
have exactly that completed observation. Reflection excludes other endpoints. -/
theorem completed_observation_iff (bindings : Subst) (before expected : Effects.State)
    (expression value : Atom) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (returned : Eval.PureReturns program bindings before expression expected value)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings before expression names after answers input output ↔
      after = expected ∧ answers = [value] ∧ input = [] ∧ output = [] :=
  (returns_iff_source_path bindings before expression names vacant covers after answers input output).trans
    (Execution.completed_observation_iff program bindings before expected expression value returned after answers input output)

/-- The bridge has the existing formation-sensitive judgment at its source
and result, rather than an untyped rewrite calibration object. -/
theorem endpoints_admitted (bindings : Subst) (before after : Effects.State)
    (expression : Atom) (names finalNames : List String) (answers input output : List Atom) :
    FormationSensitive.Judgment NativeWireData.rules .nil
      (NativePeTTaConfigurations.encode { state := before, control := .evaluate bindings expression } names)
      NativeWireData.dataType ∧
    FormationSensitive.Judgment NativeWireData.rules .nil
      (NativePeTTaConfigurations.encode (Eval.finished after answers input output) finalNames)
      NativeWireData.dataType :=
  ⟨NativePeTTaConfigurations.encode_admitted _ _, NativePeTTaConfigurations.encode_admitted _ _⟩

/-- A wrong completed answer cannot be earned by the same captured request,
even though that alleged answer can itself be represented as native Data. -/
theorem wrong_answer_refused (bindings : Subst) (before expected : Effects.State)
    (expression value wrong : Atom) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (returned : Eval.PureReturns program bindings before expression expected value)
    (different : wrong ≠ value) (after : Effects.State) :
    ¬ Returns bindings before expression names after [wrong] [] [] := by
  intro path
  have observation := (completed_observation_iff bindings before expected expression value names vacant covers returned
    after [wrong] [] []).mp path
  exact different (List.singleton_inj.mp observation.2.1)

/-- Native configuration execution realizes the shared reflexivity derivation
and its exact retained output. This earns a HOL derivation through the source
program, separately from constructing a native dependent proof inhabitant. -/
theorem authored_refl_shared_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : SignatureFormation.AnnotationsFormed world.signature source.canonical.term)
    (bindings : Subst) (state : Effects.State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "REFL", TermReading.sourceAtom source.source])
    (policy : AxiomPolicy) (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ out : Theorem, InferenceRequest.Semantics (.refl source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.axioms = ∅ ∧ out.sequent.hyp = ∅ ∧
      ∀ after answers input output,
        Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
          names after answers input output ↔
        after = state ∧ answers = [.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
          Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term,
          .symbol "HOL:Nil", .symbol "REFL"]]] ∧ input = [] ∧ output = [] := by
  obtain ⟨out, semantics, derivation, noAxioms, noHypotheses, returned⟩ :=
    InferenceExecution.authored_refl_derivation world table origins constants equalityIdentity source resolved
      annotations bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured policy
  refine ⟨out, semantics, derivation, noAxioms, noHypotheses, ?_⟩
  intro after answers input output
  exact completed_observation_iff bindings state state _ _ names vacant covers returned after answers input output

/-- The native typed state graph admits an assumption exactly at the shared
Boolean carrier. A formed non-Boolean term cannot earn a successful path. -/
theorem authored_assume_accepts_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : SignatureFormation.AnnotationsFormed world.signature source.canonical.term)
    (formed : SignatureFormation.TypeFormed world.signature source.ty)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (bindings : Subst) (state : Effects.State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ASSUME", TermReading.sourceAtom source.source])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    (∃ payload : Atom, Returns bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) names state
      [.expression [.symbol "Some", payload]] [] []) ↔ source.canonical.IsBool := by
  have reflected : (∃ payload : Atom, Returns bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) names state
      [.expression [.symbol "Some", payload]] [] []) ↔
      (∃ payload : Atom, (Eval.theory program).MultiStep
        { state, control := .evaluate bindings (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) }
        (Eval.finished state [.expression [.symbol "Some", payload]] [] [])) := by
    exact exists_congr fun payload => returns_iff_source_path bindings state _ names vacant covers state
      [.expression [.symbol "Some", payload]] [] []
  exact reflected.trans (InferenceExecution.authored_assume_accepts_iff world table origins constants source resolved
    annotations formed booleanFormed bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured)

/-- A Boolean assumption carries its shared derivation, exact hypothesis and
empty axiom provenance through native configuration execution. -/
theorem authored_assume_shared_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : SignatureFormation.AnnotationsFormed world.signature source.canonical.term)
    (formed : SignatureFormation.TypeFormed world.signature source.ty)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool) (isBool : source.canonical.IsBool)
    (bindings : Subst) (state : Effects.State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ASSUME", TermReading.sourceAtom source.source])
    (policy : AxiomPolicy) (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ out : Theorem, InferenceRequest.Semantics (.assume source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.axioms = ∅ ∧ out.sequent.hyp = {source.canonical} ∧
      ∀ after answers input output,
        Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
          names after answers input output ↔
        after = state ∧ answers = [.expression [.symbol "Some", .expression [.symbol "HOL:Thm",
          Premises.keys [Representation.termAtom Representation.registeredOperatorAtom constants [] source.canonical.term],
          Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term,
          .symbol "HOL:Nil", .symbol "ASSUME"]]] ∧ input = [] ∧ output = [] := by
  obtain ⟨out, semantics, derivation, noAxioms, hypothesis, returned⟩ :=
    InferenceExecution.authored_assume_derivation world table origins constants source resolved annotations
      formed booleanFormed isBool bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured policy
  refine ⟨out, semantics, derivation, noAxioms, hypothesis, ?_⟩
  intro after answers input output
  exact completed_observation_iff bindings state state _ _ names vacant covers returned after answers input output

/-- Representability as native Data grants no inference authority. An alleged
theorem passed as a request has exactly the refusal observation. -/
theorem authored_forged_request_observation_iff (bindings : Subst) (state : Effects.State)
    (source hypotheses conclusion dependencies origin : Atom) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression
      [.symbol "HOL:Thm", hypotheses, conclusion, dependencies, origin])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (InferenceExecution.authored_forged_request_refused bindings state source hypotheses conclusion dependencies origin
      stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- Application congruence uses both actual cache lookups and the authored
operation inside the native configuration graph. Its exact metadata readout
does not assert authorization of an arbitrary preloaded cache. -/
theorem authored_mk_comb_observation_iff (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : Effects.State) (positions : List Ty) (domain codomain : Ty)
    (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (functionLeftChecked : functionLeft.inferType positions = some (.function domain codomain))
    (functionRightChecked : functionRight.inferType positions = some (.function domain codomain))
    (argumentLeftChecked : argumentLeft.inferType positions = some domain)
    (argumentRightChecked : argumentRight.inferType positions = some domain)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some (Transitivity.theoremValue constants positions (.function domain codomain)
      functionLeft functionRight hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some (Transitivity.theoremValue constants positions domain
      argumentLeft argumentRight hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "MK_COMB", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
    after = state ∧ answers = [.expression [.symbol "Some", Transitivity.theoremValue constants positions codomain
      (.app functionLeft argumentLeft) (.app functionRight argumentRight)
      (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "MK_COMB")]] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (InferenceExecution.authored_infer_mk_comb_return constants equalityIdentity bindings state positions domain codomain
      functionLeft functionRight argumentLeft argumentRight functionLeftChecked functionRightChecked
      argumentLeftChecked argumentRightChecked hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations
      axioms receipts cache first second firstFound secondFound stateKey requestKey stateCaptured requestCaptured)
    after answers input output

/-- A missing first proof occurrence is refused in the native graph even
when the other lookup yields arbitrary represented data. -/
theorem authored_mk_comb_missing_observation_iff (bindings : Subst) (state : Effects.State)
    (operators declarations axioms receipts : Atom) (cache : List (Atom × Atom)) (first second : Atom)
    (missing : cache.lookup first = none) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "MK_COMB", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
    after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (InferenceExecution.authored_infer_mk_comb_missing_refused bindings state operators declarations axioms receipts
      cache first second missing stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- Instantiate the bridge with the actual dispatcher, actual cache lookups
and structural middle-term check. The native configuration readout is exact. -/
theorem authored_trans_observation_iff (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : Effects.State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants positions type left middle1 hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Transitivity.theoremValue constants positions type middle2 right hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "TRANS", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
    after = state ∧ answers = [if DBTerm.same middle1 middle2 then .expression [.symbol "Some",
      Transitivity.theoremValue constants positions type left right
        (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "TRANS")]
      else .symbol "None"] ∧ input = [] ∧ output = [] := by
  exact completed_observation_iff bindings state state _ _ names vacant covers
    (InferenceExecution.authored_infer_trans_return world constants identified equalityIdentity bindings state
      positions type left middle1 middle2 right leftChecked rightChecked firstFormed secondFormed
      hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations axioms receipts cache first second
      firstFound secondFound stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- The typed configuration graph accepts constant schema matches exactly
when the shared signature admits that occurrence. This is an actual source
computation, not acceptance of a caller-supplied success record. -/
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
    (assignmentsCaptured : applySubst bindings (.var assignmentsKey) = MeTTa.TypeMatching.assignmentsAtom TypeSubst.empty)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    (∃ payload : Atom, Returns bindings state (.expression [.symbol "hol-light:type-match",
      .var schemaKey, .var instanceKey, .var assignmentsKey]) names state
      [.expression [.symbol "Some", payload]] [] []) ↔
        SignatureFormation.ConstantInstance world.signature constant occurrence := by
  simp_rw [returns_iff_source_path bindings state _ names vacant covers]
  exact Execution.authored_matching_accepts_iff world constant schema occurrence registered schemaFormed occurrenceFormed
    bindings state schemaKey instanceKey assignmentsKey schemaCaptured instanceCaptured assignmentsCaptured

/-- A constant read recovers the exact registered identity and accepts precisely
the schema instances. It does not merely preserve the printed constant name. -/
theorem authored_constant_read_observation_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (context : List SourceVar) (constant : Const) (schema occurrence : Ty)
    (registered : world.signature.constants constant = some schema)
    (schemaFormed : SignatureFormation.TypeFormed world.signature schema)
    (occurrenceFormed : SignatureFormation.TypeFormed world.signature occurrence)
    (resolved : TypeFormation.Resolved world.signature occurrence)
    (bindings : Subst) (state : Effects.State) (operatorsKey constantsKey contextKey sourceKey : String)
    (operatorsCaptured : applySubst bindings (.var operatorsKey) = OperatorTable.tableAtom table.operators origins)
    (constantsCaptured : applySubst bindings (.var constantsKey) = DeclarationTable.tableAtom table constants)
    (contextCaptured : applySubst bindings (.var contextKey) = ContextLookup.contextAtom context)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom (.const constant occurrence))
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) names after answers input output ↔
    after = state ∧ answers =
      [if (HOLLight.TypeMatching.matchType schema occurrence TypeSubst.empty).isSome then
        .expression [.symbol "Some", Representation.termAtom Representation.registeredOperatorAtom constants
          (context.map Var.ty) (.const constant occurrence)] else .symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (TermReading.authored_constant_read_return world table origins constants context constant schema occurrence registered
      schemaFormed occurrenceFormed resolved bindings state operatorsKey constantsKey contextKey sourceKey
      operatorsCaptured constantsCaptured contextCaptured sourceCaptured) after answers input output

/-- Every admitted source term has the same exact positional readout in the
typed configuration graph, including nested binders and applications. -/
theorem authored_read_observation_iff (world : DefinitionAdapters.TheoryContext)
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
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:read-term", .var operatorsKey,
      .var constantsKey, .var contextKey, .var sourceKey]) names after answers input output ↔
      after = state ∧ answers = [.expression [.symbol "Some", Representation.termAtom
        Representation.registeredOperatorAtom constants (context.map Var.ty) (source.toDB context)]] ∧
        input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (TermReading.authored_read_return world table origins constants source resolved context contextFormed annotations
      type typed bindings state operatorsKey constantsKey contextKey sourceKey
      operatorsCaptured constantsCaptured contextCaptured sourceCaptured) after answers input output

/-- Equality modus ponens has exactly the guarded source observation in the
native typed configuration graph. Both premise occurrences and all metadata
remain visible, including when matching or carrier formation refuses a result. -/
theorem authored_eq_mp_observation_iff (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : Effects.State) (positions : List Ty) (rightType equalityType : Ty)
    (left right conclusion : DBTerm) (rightChecked : right.inferType positions = some rightType)
    (rightTypeFormed : SignatureFormation.TypeFormed world.signature rightType)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left)
    (conclusionFormed : SignatureFormation.AnnotationsFormed world.signature conclusion)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Representation.theoremAtom constants positions conclusion hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
    after = state ∧ answers = [if DBTerm.same left conclusion then
      if Ty.same rightType Ty.bool then EqualityModusPonens.result constants positions right hyps1 hyps2 deps1 deps2
      else .symbol "None"
      else .symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (InferenceExecution.authored_infer_eq_mp_return world constants identified equalityIdentity bindings state positions
      rightType equalityType left right conclusion rightChecked rightTypeFormed booleanFormed leftFormed conclusionFormed
      hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations axioms receipts cache first second firstFound secondFound
      stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- Among the represented and typed operands, a completed EQ_MP result exists
precisely when its second premise matches and its output is Boolean.
Representability alone cannot bypass either actual source guard. -/
theorem authored_eq_mp_accepts_iff (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : Effects.State) (positions : List Ty) (rightType equalityType : Ty)
    (left right conclusion : DBTerm) (rightChecked : right.inferType positions = some rightType)
    (rightTypeFormed : SignatureFormation.TypeFormed world.signature rightType)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (leftFormed : SignatureFormation.AnnotationsFormed world.signature left)
    (conclusionFormed : SignatureFormation.AnnotationsFormed world.signature conclusion)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Representation.theoremAtom constants positions conclusion hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    (∃ payload : Atom, Returns bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) names state
      [.expression [.symbol "Some", payload]] [] []) ↔ left = conclusion ∧ rightType = Ty.bool := by
  simp_rw [authored_eq_mp_observation_iff world constants identified equalityIdentity bindings state positions
    rightType equalityType left right conclusion rightChecked rightTypeFormed booleanFormed leftFormed conclusionFormed
    hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations axioms receipts cache first second firstFound secondFound
    stateKey requestKey stateCaptured requestCaptured names vacant covers]
  rw [← DBTerm.same_eq_true_iff left conclusion, ← Ty.same_eq_true_iff rightType Ty.bool]
  cases DBTerm.same left conclusion <;> cases Ty.same rightType Ty.bool <;>
    simp [EqualityModusPonens.result]

/-- The native graph retains source refusal of a missing equality premise;
finished states with a fabricated successful payload are excluded. -/
theorem authored_eq_mp_missing_observation_iff (bindings : Subst) (state : Effects.State)
    (operators declarations axioms receipts : Atom) (cache : List (Atom × Atom)) (first second : Atom)
    (missing : cache.lookup first = none) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
    after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (InferenceExecution.authored_infer_eq_mp_missing_refused bindings state operators declarations axioms receipts cache
      first second missing stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- Actual deduction dispatch has exactly its completed observation in the
native typed state graph. Discharge, dependency order and the origin remain
part of that observation; source-path reflection excludes another endpoint. -/
theorem authored_deduct_observation_iff (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : Effects.State) (positions : List Ty) (type : Ty) (left right : DBTerm)
    (leftTyped : left.inferType positions = some type) (rightTyped : right.inferType positions = some type)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts first second : Atom)
    (cache : List (Atom × Atom))
    (firstFound : cache.lookup first = some (Representation.theoremAtom constants positions left hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some (Representation.theoremAtom constants positions right hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [DeductionAntisymmetry.result constants positions type left right hyps1 hyps2 deps1 deps2] ∧
        input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (DeductionAntisymmetry.Dispatcher.authored_infer_deduct_return constants equalityIdentity bindings state positions type
      left right leftTyped rightTyped hyps1 hyps2 deps1 deps2 origin1 origin2 operators declarations axioms receipts first second
      cache firstFound secondFound stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- A missing first cache premise has the exact refusal observation in the
native state graph, independently of the other cached value. -/
theorem missing_deduct_premise_observation_iff (bindings : Subst) (state : Effects.State)
    (operators declarations axioms receipts first second : Atom) (cache : List (Atom × Atom))
    (missing : cache.lookup first = none) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (DeductionAntisymmetry.Dispatcher.authored_infer_deduct_missing_refused bindings state operators declarations axioms receipts
      first second cache missing stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- A source-restricted BETA request has exactly its executed named-body
result in the native typed configuration graph. State, hypotheses,
dependencies and the origin remain part of the observation. -/
theorem authored_beta_observation_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (body : SourceTerm) (type : Ty) (typed : body.inferType = some type)
    (resolved : TermReading.SourceResolved world.signature (Beta.redex needle body))
    (annotations : SignatureFormation.AnnotationsFormed world.signature ((Beta.redex needle body).toDB []))
    (bindings : Subst) (state : Effects.State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "BETA", TermReading.sourceAtom (Beta.redex needle body)])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [Beta.result constants needle body type] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (Beta.Dispatcher.authored_infer_beta_return world table origins constants equalityIdentity needle body type typed
      resolved annotations bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured)
    after answers input output

/-- Source type instantiation has its exact completed observation in the
native typed configuration graph, including merged hypothesis occurrences
and retained dependency occurrences. -/
theorem authored_inst_type_observation_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (hypotheses : List CanonicalTerm) (conclusion : CanonicalTerm) (dependencies : List Atom)
    (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] conclusion.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin))
    (bindings : Subst) (state : Effects.State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST_TYPE", TypeSubstitution.maplets Representation.registeredOperatorAtom entries, key])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [if TypeMapletValidation.admittedB world.signature entries then
        TypeInstantiation.Primitive.result constants entries hypotheses conclusion dependencies else .symbol "None"] ∧
        input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (TypeInstantiation.Dispatcher.authored_infer_inst_type_return world table origins constants entries resolved hypotheses
      conclusion dependencies origin axioms receipts key cache found bindings state stateKey requestKey
      stateCaptured requestCaptured) after answers input output

/-- A malformed resolved type maplet yields the exact native refusal
observation before obtaining any alleged cache premise. -/
theorem invalid_type_maplets_observation_iff (world : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table world) (origins : TypeOp → Atom) (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (invalid : ¬ ∀ entry ∈ entries, SignatureFormation.TypeFormed world.signature entry.1 ∧
      SignatureFormation.TypeFormed world.signature entry.2)
    (constants axioms receipts key : Atom) (cache : List (Atom × Atom))
    (bindings : Subst) (state : Effects.State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) =
      ProofLookup.sourceState (OperatorTable.tableAtom table origins) constants axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST_TYPE", TypeSubstitution.maplets Representation.registeredOperatorAtom entries, key])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (TypeInstantiation.Dispatcher.authored_infer_invalid_type_maplets_refused world table origins entries resolved invalid
      constants axioms receipts key cache bindings state stateKey requestKey stateCaptured requestCaptured)
    after answers input output

/-- Admitted simultaneous term substitution has the exact completed
observation in the native typed configuration graph. -/
theorem authored_inst_observation_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (hypotheses : List CanonicalTerm)
    (hypothesesFormed : ∀ item ∈ hypotheses, SignatureFormation.AnnotationsFormed world.signature item.term)
    (conclusion : CanonicalTerm) (conclusionFormed : SignatureFormation.AnnotationsFormed world.signature conclusion.term)
    (dependencies : List Atom) (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] conclusion.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin))
    (bindings : Subst) (state : Effects.State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom entries, key])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [TermInstantiationRule.Primitive.result constants entries admitted
        hypotheses conclusion dependencies] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (TermInstantiationRule.Dispatcher.authored_infer_inst_return world table origins constants entries admitted formed
      hypotheses hypothesesFormed conclusion conclusionFormed dependencies origin axioms receipts key cache found
      bindings state stateKey requestKey stateCaptured requestCaptured) after answers input output

/-- An ill-typed formed term maplet yields the exact native refusal
observation before obtaining any alleged cache premise. -/
theorem invalid_term_maplets_observation_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (entries : List TermMapletReading.Entry)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (invalid : ¬ SourceSubstitution.TermMapletsAdmissible (TermMapletReading.sourceEntries entries))
    (axioms receipts key : Atom) (cache : List (Atom × Atom))
    (bindings : Subst) (state : Effects.State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom entries, key])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey])
      names after answers input output ↔
      after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (TermInstantiationRule.Dispatcher.authored_infer_invalid_maplets_refused world table origins constants entries formed
      invalid axioms receipts key cache bindings state stateKey requestKey stateCaptured requestCaptured)
    after answers input output

/-- Actual theorem-cache publication retains its exact successful or refused
observation in the native typed configuration graph. This creates a source
state value; it is separate from an authoritative shared-world transaction. -/
theorem authored_publication_observation_iff (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (resultCaptured : applySubst bindings (.var resultName) =
      .expression [.symbol "Some", Publication.value hypotheses conclusion dependencies origin])
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName])
      names after answers input output ↔
      after = state ∧ answers = [Publication.result operators constants axioms key (Premises.request kind payload first second)
        hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (Publication.authored_publish_theorem_return operators constants axioms key hypotheses conclusion dependencies origin kind payload
      first second cache receipts bindings state stateKey keyName requestName resultName stateCaptured keyCaptured requestCaptured resultCaptured)
    after answers input output

/-- The complete actual inference event has the exact native observation,
including publication guards, command origin and ordered premise receipt. -/
theorem authored_inference_event_observation_iff (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (inferred : Eval.PureReturns program
      (ProofEvents.inferenceEnvironment operators constants axioms key kind payload first second cache receipts) state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value hypotheses conclusion dependencies origin]))
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
      names after answers input output ↔
      after = state ∧ answers = [Publication.result operators constants axioms key (Premises.request kind payload first second)
        hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (ProofEvents.authored_step_inference_return operators constants axioms key hypotheses conclusion dependencies origin kind payload first second
      cache receipts bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured inferred)
    after answers input output

/-- Duplicate receipt refusal has the exact native observation without an
inference-execution or theorem-validity premise. -/
theorem duplicate_inference_event_observation_iff (operators constants axioms key request : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (occupied : ReceiptKeys.presentB key receipts = true)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none)
    (after : Effects.State) (answers input output : List Atom) :
    Returns bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
      names after answers input output ↔ after = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  completed_observation_iff bindings state state _ _ names vacant covers
    (ProofEvents.authored_step_duplicate_refused operators constants axioms key request cache receipts occupied bindings state
      stateKey keyName requestName stateCaptured keyCaptured requestCaptured) after answers input output

/-- A complete actual REFL event earns a shared HOL derivation together with
its exact typed-configuration observation. This is not a general native
inhabitant of the represented HOL proposition. -/
theorem authored_refl_event_native_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : SignatureFormation.AnnotationsFormed world.signature source.canonical.term)
    (key axioms : Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : Effects.State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "REFL", TermReading.sourceAtom source.source]) (policy : AxiomPolicy)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ out : Theorem, InferenceRequest.Semantics (.refl source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧ out.axioms = ∅ ∧ out.sequent.hyp = ∅ ∧
      ∀ after answers input output,
        Returns bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
          names after answers input output ↔ after = state ∧
          answers = [Publication.result (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
            axioms key (.expression [.symbol "REFL", TermReading.sourceAtom source.source]) (.symbol "HOL:Nil")
            (Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term)
            (.symbol "HOL:Nil") [] cache receipts] ∧ input = [] ∧ output = [] := by
  obtain ⟨out, semantics, derived, dependencies, hypotheses, returned⟩ := ProofEvents.authored_refl_step_derivation world table
    origins constants equalityIdentity source resolved annotations key axioms cache receipts bindings state stateKey keyName requestName
    stateCaptured keyCaptured requestCaptured policy
  refine ⟨out, semantics, derived, dependencies, hypotheses, ?_⟩
  intro after answers input output
  exact completed_observation_iff bindings state state _ _ names vacant covers returned after answers input output

/-- A matching actual cache lookup earns its registered derivation together
with the exact native completed observation. Cache validity is retained from
the admitted insertion history, rather than inferred from a theorem label. -/
theorem authored_known_registered_derivation (policy : AxiomPolicy) (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy world cache)
    (key : Atom) (expected : CacheAuthorization.Record)
    (expectedFormed : DefinitionAdapters.TheoremFormed world.signature expected.fact)
    (found : (CacheAuthorization.entries constants cache).lookup key = some (expected.atom constants))
    (operators declarations axioms receipts : Atom) (bindings : Subst) (state : Effects.State)
    (stateKey proofKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts
      (CacheAuthorization.entries constants cache))
    (keyCaptured : applySubst bindings (.var proofKey) = key)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    DefinitionAdapters.TheoryDerives policy world expected.fact ∧
      ∀ after answers input output,
        Returns bindings state (.expression [.symbol "hol-light:known", .var stateKey, .var proofKey])
          names after answers input output ↔
          after = state ∧ answers = [.expression [.symbol "Some", expected.atom constants]] ∧ input = [] ∧ output = [] := by
  obtain ⟨derived, returned⟩ := CacheAuthorization.authored_known_derivation policy world constants identified cache valid
    key expected expectedFormed found operators declarations axioms receipts bindings state stateKey proofKey stateCaptured keyCaptured
  refine ⟨derived, ?_⟩
  intro after answers input output
  exact completed_observation_iff bindings state state _ _ names vacant covers returned after answers input output

/-- An instantiated source event and its subsequent lookup earn a registered
HOL derivation and an exact observation in the native typed graph. Neither
the initial proof cache nor the inferred theorem is assumed valid. -/
theorem authored_event_readback_native_derivation (state : Effects.State)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ record : CacheAuthorization.Record,
      DefinitionAdapters.TheoryDerives emptyAxiomPolicy CacheAuthorizationControls.world record.fact ∧
      CacheAuthorization.Valid emptyAxiomPolicy CacheAuthorizationControls.world [(CacheAuthorizationControls.key, record)] ∧
      ∀ after answers input output,
        Returns CacheAuthorizationControls.bindings state CacheAuthorizationControls.readBack names after answers input output ↔
          after = state ∧ answers = [.expression [.symbol "Some", record.atom CacheAuthorizationControls.constants]] ∧
            input = [] ∧ output = [] := by
  obtain ⟨record, derived, valid, returned⟩ := CacheAuthorizationControls.authored_event_and_readback state
  refine ⟨record, derived, valid, ?_⟩
  intro after answers input output
  exact completed_observation_iff CacheAuthorizationControls.bindings state state _ _ names vacant covers
    returned after answers input output

/-- The concrete two-event checker run earns both its registered derivation
and the exact native typed-path observation. Its returned state retains two
uses of one premise, rather than replacing them by endpoint support. -/
theorem authored_shared_reuse_native_derivation (state : Effects.State)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ record next : CacheAuthorization.Record, next.fact = record.fact ∧
      DefinitionAdapters.TheoryDerives emptyAxiomPolicy CacheAuthorizationControls.world next.fact ∧
      CacheAuthorization.Valid emptyAxiomPolicy CacheAuthorizationControls.world
        [(CacheAuthorizationControls.sharedKey, next), (CacheAuthorizationControls.key, record)] ∧
      ∀ after answers input output,
        Returns CacheAuthorizationControls.reuseBindings state CacheAuthorizationControls.reuse names after answers input output ↔
          after = state ∧ answers = [.expression [.symbol "Some", CacheAuthorizationControls.stateWithReuse record next]] ∧
            input = [] ∧ output = [] := by
  obtain ⟨record, next, same, derived, valid, returned⟩ := CacheAuthorizationControls.authored_event_and_shared_reuse state
  refine ⟨record, next, same, derived, valid, ?_⟩
  intro after answers input output
  exact completed_observation_iff CacheAuthorizationControls.reuseBindings state state _ _ names vacant covers
    returned after answers input output

/-- The authored axiom helper earns an exact native typed-state observation
and the registered derivation only for the selected object-theory commitment.
This is the helper execution, not the dispatcher event using a bound head. -/
theorem authored_axiom_registered_derivation (policy : AxiomPolicy) (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm) (same : source.canonical = expected.canonical)
    (isBool : source.canonical.IsBool)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : SignatureFormation.AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : SignatureFormation.AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : SignatureFormation.TypeFormed world.signature source.ty)
    (booleanFormed : SignatureFormation.TypeFormed world.signature Ty.bool)
    (label receipts : Atom) (commitments cache : List (Atom × Atom))
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (authorized : policy (AxiomExecution.dependency label source isBool).sequent)
    (bindings : Subst) (state : Effects.State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source.source)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    DefinitionAdapters.TheoryDerives policy world (AxiomExecution.record label source isBool).fact ∧
      ∀ after answers input output,
        Returns bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
          names after answers input output ↔
        after = state ∧ answers = [.expression [.symbol "Some", (AxiomExecution.record label source isBool).atom constants]] ∧
          input = [] ∧ output = [] := by
  obtain ⟨derived, returned⟩ := AxiomExecution.authored_axiom_derivation policy world table origins constants identified
    source expected same isBool sourceResolved expectedResolved sourceFormed expectedFormed sourceTypeFormed booleanFormed
    label receipts commitments cache found authorized bindings state stateKey labelKey sourceKey stateCaptured labelCaptured sourceCaptured
  refine ⟨derived, ?_⟩
  intro after answers input output
  exact completed_observation_iff bindings state state _ _ names vacant covers returned after answers input output

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLExecution
