import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionEquations
import Mettapedia.Languages.MeTTa.PeTTa.SequentialBindings
import Mettapedia.Languages.MeTTa.PeTTa.SourceData

/-!
# Sequential construction in the authored type-definition helper

The twelve initializers are the retained source syntax. Parameter collection,
lexical sorting, type construction and length execute their existing helpers;
the other initializers assemble data from the live environment. The resulting
declarations supply the existing equation and publication continuation.
The outer type-definition guards and complete authorized history remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionConstruction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Effects (State)
open Representation (registeredOperatorAtom termAtom)
open TypeSubstitution (typeAtom)

/-- Source arguments retain the complete input world and proof addresses. -/
structure Input where
  operators : Atom
  declarations : Atom
  axioms : Atom
  key : Atom
  dependencies : Atom
  premise : Atom
  typeName : String
  abstractionName : String
  representationName : String
  cache : List (Atom × Atom)
  receipts : List ReceiptKeys.Entry

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:extend-type"))[0]'(by decide)

private def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

def sourceBody : Atom := equation.body

def sourcePairs : List (String × Atom) :=
  [("parameters", call "hol-light:sorted-names" [call "hol-light:term-type-vars" [.var "predicate"]]),
   ("newtype", call "Tyapp" [.var "name", call "hol-light:type-parameters" [.var "parameters"]]),
   ("abstype", call "hol-light:fun" [.var "representation", .var "newtype"]),
   ("reptype", call "hol-light:fun" [.var "newtype", .var "representation"]),
   ("abs", call "HOL:C" [call "HOL:Abstraction" [.var "absname", .var "name", .var "predicate"], .var "abstype"]),
   ("rep", call "HOL:C" [call "HOL:Representation" [.var "repname", .var "name", .var "predicate"], .var "reptype"]),
   ("newOperators", call "HOL:Cons" [call "HOL:Entry" [.var "name",
     call "HOL:TypeOperator" [call "hol-light:length" [.var "parameters"],
       call "HOL:DefinedType" [.var "name", .var "predicate"]]], .var "operators"]),
   ("newConstants", call "HOL:Cons" [call "HOL:Entry" [.var "absname",
     call "HOL:Constant" [.var "abstype", call "HOL:Abstraction" [.var "absname", .var "name", .var "predicate"]]],
     call "HOL:Cons" [call "HOL:Entry" [.var "repname", call "HOL:Constant" [.var "reptype",
       call "HOL:Representation" [.var "repname", .var "name", .var "predicate"]]], .var "constants"]]),
   ("extended", call "HOL:State" [.var "newOperators", .var "newConstants", .var "axioms", .var "cache", .var "receipts"]),
   ("a", call "HOL:Free" [.grounded (.string "a"), .var "newtype"]),
   ("r", call "HOL:Free" [.grounded (.string "r"), .var "representation"]),
   ("request", call "TYPE_DEFINITION" [.var "name", .var "absname", .var "repname", .var "premise"])]

theorem source_shape : sourceBody = call "let*"
    [.expression (SequentialBindings.bindingSyntax sourcePairs), TypeDefinitionEquations.sourceBody] := by decide

def operator (input : Input) (predicate : CheckedSourceTerm) (texts : List String) : TypeOp :=
  .mk (sourceOperatorName (Name.global input.typeName)) (.defined predicate.source (texts.map Name.global))

def carrier (input : Input) (predicate : CheckedSourceTerm) (texts : List String) : Ty :=
  .op (operator input predicate texts) ((texts.map Name.global).map Ty.var)

def abstraction (input : Input) (predicate : CheckedSourceTerm) (texts : List String) : Const :=
  .mk (Name.global input.abstractionName) (.abstraction (operator input predicate texts))

def representation (input : Input) (predicate : CheckedSourceTerm) (texts : List String) : Const :=
  .mk (Name.global input.representationName) (.representation (operator input predicate texts))

def abstractionIdentity (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) : Atom :=
  call "HOL:Abstraction" [.grounded (.string input.abstractionName), .grounded (.string input.typeName),
    termAtom registeredOperatorAtom before [] predicate.canonical.term]

def representationIdentity (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) : Atom :=
  call "HOL:Representation" [.grounded (.string input.representationName), .grounded (.string input.typeName),
    termAtom registeredOperatorAtom before [] predicate.canonical.term]

def identities (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (texts : List String) : Const → Atom :=
  DeclarationTable.extendIdentity
    (DeclarationTable.extendIdentity before (abstraction input predicate texts) (abstractionIdentity input before predicate))
    (representation input predicate texts) (representationIdentity input before predicate)

def newOperators (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (texts : List String) : Atom :=
  call "HOL:Cons" [call "HOL:Entry" [.grounded (.string input.typeName),
    call "HOL:TypeOperator" [.grounded (.int texts.length), call "HOL:DefinedType"
      [.grounded (.string input.typeName), termAtom registeredOperatorAtom before [] predicate.canonical.term]]], input.operators]

def newConstants (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) : Atom :=
  call "HOL:Cons" [call "HOL:Entry" [.grounded (.string input.abstractionName), call "HOL:Constant"
    [typeAtom registeredOperatorAtom (.function represented (carrier input predicate texts)), abstractionIdentity input before predicate]],
    call "HOL:Cons" [call "HOL:Entry" [.grounded (.string input.representationName), call "HOL:Constant"
      [typeAtom registeredOperatorAtom (.function (carrier input predicate texts) represented), representationIdentity input before predicate]],
      input.declarations]]

def environment (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (represented : Ty) : Subst :=
  [("dependencies", input.dependencies), ("representation", typeAtom registeredOperatorAtom represented),
   ("predicate", termAtom registeredOperatorAtom before [] predicate.canonical.term), ("premise", input.premise),
   ("repname", .grounded (.string input.representationName)), ("absname", .grounded (.string input.abstractionName)),
   ("name", .grounded (.string input.typeName)), ("key", input.key), ("receipts", ReceiptKeys.table input.receipts),
   ("cache", Lookup.table input.cache), ("axioms", input.axioms), ("constants", input.declarations), ("operators", input.operators)]

def values (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (represented : Ty) (texts : List String) :
    List (String × Atom) :=
  [("parameters", Premises.keys (StdLib.stringAtoms texts)),
   ("newtype", typeAtom registeredOperatorAtom (carrier input predicate texts)),
   ("abstype", typeAtom registeredOperatorAtom (.function represented (carrier input predicate texts))),
   ("reptype", typeAtom registeredOperatorAtom (.function (carrier input predicate texts) represented)),
   ("abs", call "HOL:C" [abstractionIdentity input before predicate,
     typeAtom registeredOperatorAtom (.function represented (carrier input predicate texts))]),
   ("rep", call "HOL:C" [representationIdentity input before predicate,
     typeAtom registeredOperatorAtom (.function (carrier input predicate texts) represented)]),
   ("newOperators", newOperators input before predicate texts),
   ("newConstants", newConstants input before predicate represented texts),
   ("extended", ProofLookup.sourceState (newOperators input before predicate texts)
     (newConstants input before predicate represented texts) input.axioms (ReceiptKeys.table input.receipts) input.cache),
   ("a", termAtom registeredOperatorAtom before [] (TypeDefinitionEquations.carrierVariable (carrier input predicate texts))),
   ("r", termAtom registeredOperatorAtom before [] (TypeDefinitionEquations.representationVariable represented)),
   ("request", TypeDefinitionFormation.command input.typeName input.abstractionName input.representationName input.premise)]

def stage (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (represented : Ty)
    (texts : List String) (index : Nat) : Subst :=
  ((values input before predicate represented texts).take index).reverse ++ environment input before predicate represented

theorem operator_spelling (input : Input) (predicate : CheckedSourceTerm) (texts : List String) :
    registeredOperatorAtom (operator input predicate texts) = .grounded (.string input.typeName) := by
  simp only [registeredOperatorAtom, operator, operatorName, sourceOperatorName_roundtrip, TypeSubstitution.nameAtom, Name.global]
  rfl

theorem abstraction_identity (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (texts : List String) :
    identities input before predicate texts (abstraction input predicate texts) = abstractionIdentity input before predicate := by
  simp [identities, DeclarationTable.extendIdentity, Const.same_eq_true_iff, abstraction, representation]

theorem representation_identity (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (texts : List String) :
    identities input before predicate texts (representation input predicate texts) = representationIdentity input before predicate := by
  simp [identities, DeclarationTable.extendIdentity, Const.same_eq_true_iff]

theorem primitive_equality_retained (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (texts : List String) :
    identities input before predicate texts Const.equality = before Const.equality := by
  simp [identities, DeclarationTable.extendIdentity, Const.same_eq_true_iff, abstraction, representation, Const.equality]

theorem predicate_identity_retained (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (texts : List String) (context : TheoryContext)
    (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names) :
    termAtom registeredOperatorAtom (identities input before predicate texts) [] predicate.canonical.term =
      termAtom registeredOperatorAtom before [] predicate.canonical.term := by
  unfold identities
  have repUnregistered := context.constant_unregistered (representation input predicate texts)
    (by simpa only [constantName, representation] using repFresh)
  have absUnregistered := context.constant_unregistered (abstraction input predicate texts)
    (by simpa only [constantName, abstraction] using absFresh)
  rw [CacheAuthorization.term_atom_fresh_identity context _
    repUnregistered _ _ _ formed [],
    CacheAuthorization.term_atom_fresh_identity context _
    absUnregistered _ _ _ formed []]

local macro "source_tree" : tactic => `(tactic|
  repeat' first
  | exact SourceData.Tree.capture _
  | exact SourceData.Tree.grounded _
  | exact SourceData.Tree.symbol _
  | (apply SourceData.Tree.constructor _ _ (by decide) (by decide)
     intro argument member
     simp only [List.mem_cons, List.mem_nil_iff] at member
     repeat' first | (rcases member with same | member; try subst argument) | cases member))

attribute [local simp] call sourcePairs stage values environment newOperators newConstants
  abstractionIdentity representationIdentity ProofLookup.sourceState TypeDefinitionFormation.command
  TypeDefinitionEquations.carrierVariable TypeDefinitionEquations.representationVariable
  termAtom Representation.variableAtom typeAtom TypeSubstitution.nameAtom Name.global
  applySubst applySubst.applySubstList Subst.lookup

private theorem parameters_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (raw : List String) (state : State)
    (collected : TypeVariables.termAtoms [] predicate.canonical.term = StdLib.stringAtoms raw) :
    BoundCalls.CorePath.PureReturns program (stage input before predicate represented (NameSorting.sorted raw) 0) state
      (sourcePairs[0]'(by decide)).2 state
      ((values input before predicate represented (NameSorting.sorted raw))[0]'(by simp [values])).2 := by
  dsimp [sourcePairs, call, values]
  apply NameSorting.authored_sorted_certificate
  have path := TypeVariables.authored_term_type_vars_certificate registeredOperatorAtom before []
    predicate.canonical.term predicate.ty predicate.canonical.checked
    (stage input before predicate represented (NameSorting.sorted raw) 0) state "predicate" (by simp)
  simpa [collected] using path

private theorem carrier_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (state : State) :
    BoundCalls.CorePath.PureReturns program (stage input before predicate represented texts 1) state
      (sourcePairs[1]'(by decide)).2 state
      ((values input before predicate represented texts)[1]'(by simp [values])).2 := by
  have parameters := TypeParameterOrdering.Parameters.authored_certificate
    (stage input before predicate represented texts 1) state texts (.var "parameters")
    (by simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 1) state "parameters")
  have name := BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 1) state "name"
  have path := BoundCalls.CorePath.binary_constructor_returns program (stage input before predicate represented texts 1)
    state state state "Tyapp" (.var "name") (.expression [.symbol "hol-light:type-parameters", .var "parameters"])
    (.grounded (.string input.typeName)) (Premises.keys (TypeParameterOrdering.Parameters.atoms texts))
    (by decide) (by decide) (by simpa using name) parameters
  simpa [carrier, operator_spelling, TypeParameterOrdering.Parameters.atoms, List.map_map, Function.comp_def] using path

private theorem abstraction_type_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (state : State) :
    BoundCalls.CorePath.PureReturns program (stage input before predicate represented texts 2) state
      (sourcePairs[2]'(by decide)).2 state
      ((values input before predicate represented texts)[2]'(by simp [values])).2 := by
  apply TermJudgment.authored_function_certificate
  · simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 2) state "representation"
  · simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 2) state "newtype"

private theorem representation_type_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (state : State) :
    BoundCalls.CorePath.PureReturns program (stage input before predicate represented texts 3) state
      (sourcePairs[3]'(by decide)).2 state
      ((values input before predicate represented texts)[3]'(by simp [values])).2 := by
  apply TermJudgment.authored_function_certificate
  · simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 3) state "newtype"
  · simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 3) state "representation"

local macro "construct_data_initializer" index:num "with" bindings:term "at" state:term : tactic => `(tactic|
  (have tree : SourceData.Tree program (sourcePairs[$index]'(by decide)).2 := by
      dsimp [sourcePairs, call]
      source_tree
   simpa using SourceData.returns program $bindings $state _ tree))

private theorem data_initializer_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (state : State) (index : Nat) (bound : index < 12)
    (data : index ∈ [4, 5, 7, 8, 9, 10, 11]) :
    BoundCalls.CorePath.PureReturns program (stage input before predicate represented texts index) state
      (sourcePairs[index]'(by change index < 12; exact bound)).2 state
      ((values input before predicate represented texts)[index]'(by change index < 12; exact bound)).2 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at data
  rcases data with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · construct_data_initializer 4 with (stage input before predicate represented texts 4) at state
  · construct_data_initializer 5 with (stage input before predicate represented texts 5) at state
  · construct_data_initializer 7 with (stage input before predicate represented texts 7) at state
  · construct_data_initializer 8 with (stage input before predicate represented texts 8) at state
  · construct_data_initializer 9 with (stage input before predicate represented texts 9) at state
  · construct_data_initializer 10 with (stage input before predicate represented texts 10) at state
  · construct_data_initializer 11 with (stage input before predicate represented texts 11) at state

private theorem operator_initializer_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) (state : State) :
    BoundCalls.CorePath.PureReturns program (stage input before predicate represented texts 6) state
      (sourcePairs[6]'(by decide)).2 state
      ((values input before predicate represented texts)[6]'(by simp [values])).2 := by
  dsimp [sourcePairs, values, newOperators, call]
  apply BoundCalls.CorePath.binary_constructor_returns program _ state state state "HOL:Cons" _ _ _ _ (by decide) (by decide)
  · apply BoundCalls.CorePath.binary_constructor_returns program _ state state state "HOL:Entry" _ _ _ _ (by decide) (by decide)
    · simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 6) state "name"
    · apply BoundCalls.CorePath.binary_constructor_returns program _ state state state "HOL:TypeOperator" _ _ _ _ (by decide) (by decide)
      · have length := ListOperations.Length.authored_length_certificate
          (stage input before predicate represented texts 6) state (StdLib.stringAtoms texts) "parameters" (by simp)
        simpa [StdLib.stringAtoms] using length
      · have tree : SourceData.Tree program
            (call "HOL:DefinedType" [.var "name", .var "predicate"]) := by
          dsimp [call]
          source_tree
        simpa using SourceData.returns program (stage input before predicate represented texts 6) state _ tree
  · simpa using BoundCalls.CorePath.variable_returns program (stage input before predicate represented texts 6) state "operators"

/-- Every initializer executes in its preceding live environment. The list
of resulting bindings is constructed by these paths, not assumed. -/
theorem initializers_execute (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (raw : List String) (state : State)
    (collected : TypeVariables.termAtoms [] predicate.canonical.term = StdLib.stringAtoms raw) :
    SequentialBindings.Path program state (environment input before predicate represented) sourcePairs
      (stage input before predicate represented (NameSorting.sorted raw) 12) := by
  change SequentialBindings.Path program state (stage input before predicate represented (NameSorting.sorted raw) 0)
    sourcePairs (stage input before predicate represented (NameSorting.sorted raw) 12)
  dsimp only [sourcePairs]
  apply SequentialBindings.Path.cons ((parameters_execute input before predicate represented raw state collected).extended) (by simp)
  apply SequentialBindings.Path.cons ((carrier_execute input before predicate represented (NameSorting.sorted raw) state).extended) (by simp)
  apply SequentialBindings.Path.cons ((abstraction_type_execute input before predicate represented (NameSorting.sorted raw) state).extended) (by simp)
  apply SequentialBindings.Path.cons ((representation_type_execute input before predicate represented (NameSorting.sorted raw) state).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 4 (by decide) (by decide)).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 5 (by decide) (by decide)).extended) (by simp)
  apply SequentialBindings.Path.cons ((operator_initializer_execute input before predicate represented (NameSorting.sorted raw) state).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 7 (by decide) (by decide)).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 8 (by decide) (by decide)).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 9 (by decide) (by decide)).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 10 (by decide) (by decide)).extended) (by simp)
  apply SequentialBindings.Path.cons ((data_initializer_execute input before predicate represented (NameSorting.sorted raw) state 11 (by decide) (by decide)).extended) (by simp)
  exact SequentialBindings.Path.nil _

def result (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm)
    (represented : Ty) (texts : List String) : Atom :=
  TypeDefinitionPublication.finalResult (newOperators input before predicate texts)
    (newConstants input before predicate represented texts) input.axioms input.key
    (termAtom registeredOperatorAtom (identities input before predicate texts) []
      (TypeDefinitionEquations.firstLaw (abstraction input predicate texts) (representation input predicate texts)
        represented (carrier input predicate texts)))
    (termAtom registeredOperatorAtom (identities input before predicate texts) []
      (TypeDefinitionEquations.secondLaw (abstraction input predicate texts) (representation input predicate texts)
        represented (carrier input predicate texts) predicate.canonical.term))
    input.dependencies input.typeName input.abstractionName input.representationName input.premise input.cache input.receipts

private theorem body_returns_with_collector (input : Input) (before : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (raw : List String) (state : State)
    (collected : TypeVariables.termAtoms [] predicate.canonical.term = StdLib.stringAtoms raw)
    (typed : predicate.ty = .function represented Ty.bool)
    (context : TheoryContext) (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names)
    (equalityIdentity : before Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (receiptFresh : ReceiptKeys.presentB input.key input.receipts = false)
    (cacheFresh : input.cache.lookup input.key = none) :
    BoundCalls.PureReturns program (environment input before predicate represented) state sourceBody state
      (result input before predicate represented (NameSorting.sorted raw)) := by
  let texts := NameSorting.sorted raw
  have predicateRetained := predicate_identity_retained input before predicate texts context formed absFresh repFresh
  rw [source_shape]
  apply SequentialBindings.source_returns (initializers_execute input before predicate represented raw state collected)
  unfold result
  apply TypeDefinitionEquations.authored_equations_publish
  · have sameType : predicate.canonical.ty = predicate.ty := rfl
    simpa only [sameType, typed] using predicate.canonical.checked
  · rw [primitive_equality_retained]
    exact equalityIdentity
  · simp
  · simp
  · simp
  · simp
  · simpa [texts] using predicateRetained.symm
  · simp [TypeDefinitionEquations.abstractionTerm, abstraction_identity]
  · simp [TypeDefinitionEquations.representationTerm, representation_identity]
  · simp
  · simp
  · intro name member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  · exact receiptFresh
  · exact cacheFresh

/-- The complete retained helper constructs declarations, computes all three
equations and executes both publications. Its parameters are earned by the
actual annotation collector and lexical sort. Old signature formation and
fresh names ensure that registering the two identities cannot alter the
predicate. This theorem does not bypass the enclosing event's guards. -/
theorem authored_helper_returns (input : Input) (before : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (state : State)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (typed : predicate.ty = .function represented Ty.bool)
    (context : TheoryContext) (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names)
    (equalityIdentity : before Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (receiptFresh : ReceiptKeys.presentB input.key input.receipts = false)
    (cacheFresh : input.cache.lookup input.key = none) :
    ∃ texts, texts.map Name.global = sortedParameters predicate.source ∧
      BoundCalls.PureReturns program (environment input before predicate represented) state sourceBody state
        (result input before predicate represented texts) := by
  obtain ⟨raw, collected, distinct, support⟩ :=
    TypeParameterOrdering.collector_string_list predicate.canonical.term global
  exact ⟨NameSorting.sorted raw,
    sortedParameters_of_global_strings predicate.source raw distinct support,
    body_returns_with_collector input before predicate represented raw state collected typed context formed
      absFresh repFresh equalityIdentity receiptFresh cacheFresh⟩

def sourceNames : List String :=
  ["state", "key", "name", "absname", "repname", "premise", "predicate", "representation", "dependencies"]

def sourceArguments (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (represented : Ty) : List Atom :=
  [ProofLookup.sourceState input.operators input.declarations input.axioms (ReceiptKeys.table input.receipts) input.cache,
   input.key, .grounded (.string input.typeName), .grounded (.string input.abstractionName),
   .grounded (.string input.representationName), input.premise,
   termAtom registeredOperatorAtom before [] predicate.canonical.term,
   typeAtom registeredOperatorAtom represented, input.dependencies]

theorem source_clause (input : Input) (before : Const → Atom) (predicate : CheckedSourceTerm) (represented : Ty) :
    Eval.clauses program "hol-light:extend-type" (sourceArguments input before predicate represented) =
      [.evaluate (environment input before predicate represented) sourceBody] := by
  rw [Eval.clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:extend-type") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments =
      [.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms", .var "cache", .var "receipts"],
       .var "key", .var "name", .var "absname", .var "repname", .var "premise", .var "predicate", .var "representation",
       .var "dependencies"] := by decide
  simp [sourceArguments, sourceBody, List.filterMap, formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

/-- Source dispatch itself selects the retained helper before executing its
constructed body. The caller's captured values may contain data with program
heads; those values are not evaluated a second time during dispatch. -/
theorem authored_helper_call_returns (input : Input) (before : Const → Atom)
    (predicate : CheckedSourceTerm) (represented : Ty) (bindings : Subst) (state : State)
    (captured : sourceNames.map (fun name => applySubst bindings (.var name)) =
      sourceArguments input before predicate represented)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (typed : predicate.ty = .function represented Ty.bool)
    (context : TheoryContext) (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names)
    (equalityIdentity : before Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (receiptFresh : ReceiptKeys.presentB input.key input.receipts = false)
    (cacheFresh : input.cache.lookup input.key = none) :
    ∃ texts, texts.map Name.global = sortedParameters predicate.source ∧
      BoundCalls.PureReturns program bindings state
        (.expression (.symbol "hol-light:extend-type" :: sourceNames.map Atom.var)) state
        (result input before predicate represented texts) := by
  obtain ⟨texts, ordered, returned⟩ := authored_helper_returns input before predicate represented state global typed
    context formed absFresh repFresh equalityIdentity receiptFresh cacheFresh
  refine ⟨texts, ordered, BoundCalls.authored_variable_call_returns program bindings
    (environment input before predicate represented) state state "hol-light:extend-type" sourceNames sourceBody _
    (by decide) (by decide) (by decide) ?_ returned (by decide)⟩
  rw [captured]
  exact source_clause input before predicate represented

/-- The two formulas constructed by the actual helper have exactly the
existing registered source gate's pointwise meaning. The source operator
spelling is converted once; constant names retain their original identities.
Successful admission is checked by that existing gate, not by theorem names. -/
theorem registered_output_correspondence (input : Input) (predicate : CheckedSourceTerm) (texts : List String)
    (existence : Theorem) (witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate.canonical witness existence.sequent.concl)
    (boolean : existence.sequent.concl.IsBool) (context : TheoryContext)
    (witnesses : SignatureFormation.InstanceWitnesses) (output : SourceTypeDefinitionResult)
    (admitted : admitSourceTypeInTheory context witnesses
      (TypeDefinitionAdmission.request input.typeName input.abstractionName input.representationName texts predicate existence) =
        some output) :
    output.output.abstractionRepresentationTheorem.sequent.concl.term =
      TypeDefinitionEquations.firstLaw (abstraction input predicate texts) (representation input predicate texts)
        witness.ty (carrier input predicate texts) ∧
    output.output.representationAbstractionTheorem.sequent.concl.term =
      TypeDefinitionEquations.secondLaw (abstraction input predicate texts) (representation input predicate texts)
        witness.ty (carrier input predicate texts) predicate.canonical.term := by
  exact TypeDefinitionEquations.admitted_output_formulas context witnesses
    (TypeDefinitionAdmission.request input.typeName input.abstractionName input.representationName texts predicate existence)
    predicate.canonical witness application boolean output admitted

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionConstruction
