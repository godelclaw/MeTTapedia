import Mettapedia.Languages.MM0.HOLKernelSourceBindingReadback
import Mettapedia.Languages.MM0.HOLKernelSetOperationContextReadback
import Mettapedia.Languages.MM0.HOLKernelInferenceReadback
import Mettapedia.Languages.MM0.HOLKernelProofReadbackRenaming

/-!
# Source readings of maintained HOL compiler environments

The reading records the native parameter encoding, the actual variable-name
assignment and the decoded formation/logical judgments. It derives canonical
term readback and admission of all compiled typing premises. The concrete
initial environment and extension by a logical assumption preserve the reading
and the independently admitted hypothesis receipts. Initial receipts use only
the parameter prefix and source binder bank, so their admitted readback also
weakens at a fresh name beyond that bank.

Extension by a bound variable preserves the syntax reading at the compiler's
actual fresh name and working-bank depth. Its proof uses native occurrence
independence, variable bounds and reader renaming. Preservation of the complete
hypothesis receipts under this bound-variable extension has a separate
proof-admission theorem, derived from the actual rebinding and weakening
receipts; it is not a field of the syntax reading.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback HOLKernelProofEnvironment
open HOLKernelTermAssignments HOLKernelProofAllocation
open HOLKernelSetOperationProofReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}
variable {layout : HOLKernelProofAllocation.Layout}
variable {encoding : Encoding signature layout
  (HOLKernelSetOperationInterpretation.initialContext signature.ids) Unit Symbol}
variable {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {depth : Nat}

abbrev NativeContext := HOLKernelProofEnvironment.NativeContext signature layout
  (HOLKernelSetOperationInterpretation.initialContext signature.ids)

structure Reading
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := [])
      encoding gamma assumptions depth) (names : Names gamma) where
  base : encoding.base = HOLKernelSetOperationInterpretation.typeCode
  constant : ∀ {type} (symbol : Symbol type), encoding.constant symbol = HOLKernelSetOperationInterpretation.symbolCode symbol
  assignment : ∀ {type} (index : Var gamma type), environment.assignment index = .var (names.nameOf index)
  names_in_scope : InScope 7 names depth
  formation : Judgment Symbol gamma
  logical : Judgment Symbol gamma
  formation_read : readJudgmentWith
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    signature.symbol names (expandEquivalence signature.symbol abbreviation.reference environment.scope.formation) = some formation
  logical_read : readJudgmentWith
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    signature.symbol names (expandEquivalence signature.symbol abbreviation.reference environment.scope.logical) = some logical

variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
variable {profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
variable {environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := [])
  encoding gamma assumptions depth} {names : Names gamma}

theorem Reading.encode_eq (reading : Reading abbreviation profile environment names)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    environment.encode source = HOLKernelSetOperationReadback.encode signature.symbol names depth source := by
  have constants : (fun {type} (symbol : Symbol type) => encoding.constant symbol) =
      (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode symbol) := by
    funext type symbol
    exact reading.constant symbol
  have assignments : (fun {type} (index : Var gamma type) => environment.assignment index) = (fun {type} (index : Var gamma type) => Preterm.var (names.nameOf index)) := by
    funext type index
    exact reading.assignment index
  unfold Environment.encode
  rw [reading.base, constants, assignments, HOLKernelTermAssignments.encode_positions]
  rfl

theorem Reading.term_read (reading : Reading abbreviation profile environment names)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 names
      (environment.encode source) = some ⟨type, source⟩ := by
  rw [reading.encode_eq]
  exact logical_reader_encode profile source names depth reading.names_in_scope

theorem Reading.logical_formula (reading : Reading abbreviation profile environment names) :
    readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names environment.scope.logical = some reading.logical.formula := by
  simp only [readFormulaIn, reading.logical_read, Option.map_some]

theorem Reading.formation_formula (reading : Reading abbreviation profile environment names) :
    readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names environment.scope.formation = some reading.formation.formula := by
  simp only [readFormulaIn, reading.formation_read, Option.map_some]


theorem expand_entails (first second : Preterm)
    (distinct : signature.symbol .im ≠ abbreviation.reference) :
    expandEquivalence signature.symbol abbreviation.reference (HOLKernelJudgment.entails signature.symbol first second) =
      HOLKernelJudgment.entails signature.symbol
        (expandEquivalence signature.symbol abbreviation.reference first)
        (expandEquivalence signature.symbol abbreviation.reference second) := by
  simp [HOLKernelJudgment.entails, applySymbol, Preterm.applyArgs, expandEquivalence, distinct]

theorem Reading.assertion_read (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (formula : Formula Symbol gamma) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelJudgment.holds signature.symbol (environment.encode formula))) = some (.assertion formula) := by
  rw [reading.encode_eq, expandEquivalence_holds,
    expandEquivalence_encodeTerm _ _ distinct]
  simp [readJudgmentWith_holds _ signature.symbol_injective,
    logical_reader_encode profile formula names depth reading.names_in_scope, expect_same]

theorem Reading.type_assertion_read (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelJudgment.hasType signature.symbol (environment.encode source)
          (encodeType signature.symbol encoding.base type))) = some (.typing source) := by
  rw [reading.encode_eq, reading.base]
  have typedReading := logical_read_typing profile source names depth reading.names_in_scope
  have expands : expandEquivalence signature.symbol abbreviation.reference
      (HOLKernelJudgment.hasType signature.symbol
        (HOLKernelSetOperationReadback.encode signature.symbol names depth source)
        (encodeType signature.symbol HOLKernelSetOperationInterpretation.typeCode type)) =
      HOLKernelJudgment.hasType signature.symbol
        (HOLKernelSetOperationReadback.encode signature.symbol names depth source)
        (encodeType signature.symbol HOLKernelSetOperationInterpretation.typeCode type) := by
    simp [HOLKernelJudgment.hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      expandEquivalence_encodeTerm _ _ distinct, expandEquivalence_encodeType _ _ distinct]
  rw [expands, typedReading]


theorem Reading.typing_read_in (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (native : Preterm) (antecedent : Judgment Symbol gamma)
    (antecedentRead : readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names (expandEquivalence signature.symbol abbreviation.reference native) = some antecedent)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelTypingRules.typed signature.symbol native (environment.encode source)
          (encodeType signature.symbol encoding.base type))) = some (.consequence antecedent (.typing source)) := by
  rw [HOLKernelTypingRules.typed, expand_entails _ _ (distinct .im),
    readJudgmentWith_entails _ signature.symbol_injective, antecedentRead, reading.type_assertion_read distinct source]
  rfl

theorem Reading.typing_read (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelTypingRules.typed signature.symbol environment.scope.logical (environment.encode source)
          (encodeType signature.symbol encoding.base type))) =
      some (.consequence reading.logical (.typing source)) :=
  reading.typing_read_in distinct _ _ reading.logical_read source

theorem Reading.typed_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {type : Ty Unit} (source : Term Symbol gamma type)
    (fits : source.binderDepth ≤ layout.width) {frame : Nat} (active : frame < layout.frames)
    (before : depth + layout.width ≤ layout.workDepth frame) :
    Nonempty (AdmittedProof abbreviation theorems
      (HOLKernelProofEnvironment.NativeContext signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt 1 names
      (environment.typed structural typing source fits active before).val (.imp reading.logical.formula .top)) :=
  ⟨AdmittedStep.formation (environment.typed structural typing source fits active before).property.eval
    (reading.typing_read distinct source)⟩

def Reading.assume (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (formula : Formula Symbol gamma) (fits : formula.binderDepth < layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame) :
    Reading abbreviation profile (environment.assume structural formula fits active before) names where
  base := reading.base
  constant := reading.constant
  assignment := reading.assignment
  names_in_scope := reading.names_in_scope
  formation := reading.formation
  logical := .conjunction reading.logical (.assertion formula)
  formation_read := reading.formation_read
  logical_read := by
    change readJudgmentWith _ signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical
          (HOLKernelJudgment.holds signature.symbol (environment.encode formula)))) = _
    rw [expandEquivalence_conjunction _ _ (distinct .an),
      readJudgmentWith_conjunction _ signature.symbol_injective,
      reading.logical_read, reading.assertion_read distinct formula]
    rfl


theorem Reading.assertion_formula (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (formula : Formula Symbol gamma) :
    readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names (HOLKernelJudgment.holds signature.symbol (environment.encode formula)) = some formula := by
  simp only [readFormulaIn, reading.assertion_read distinct formula, Option.map_some, Judgment.formula]

def Reading.AssumptionsAdmitted (reading : Reading abbreviation profile environment names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule) : Prop :=
  ∀ occurrence : Fin assumptions.length, ∃ fuel,
    Nonempty (AdmittedProof abbreviation theorems
      (HOLKernelProofEnvironment.NativeContext signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel names (environment.assumptionProof occurrence).val
      (.imp reading.logical.formula (assumptions.get occurrence)))

theorem Reading.assume_assumptions_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (admitted : reading.AssumptionsAdmitted ruleAt bindingAt)
    (formula : Formula Symbol gamma) (fits : formula.binderDepth < layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame) :
    (reading.assume distinct structural formula fits active before).AssumptionsAdmitted ruleAt bindingAt := by
  intro occurrence
  rcases occurrence with ⟨index, smaller⟩
  cases index with
  | zero =>
      refine ⟨1, ?_⟩
      exact HOLKernelStructuralReadback.right_admitted signature abbreviation (distinct .im) (distinct .an) structural
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
        7 names ruleAt bindingAt (selected .anr) environment.scope.logical
        (HOLKernelJudgment.holds signature.symbol (environment.encode formula))
        environment.scope.logicalSorted
        (HOLKernelJudgment.holds_sorted signature _
          (environment.encoded_sorted formula (Nat.le_of_lt fits) active before))
        reading.logical.formula formula reading.logical_formula (reading.assertion_formula distinct formula)
  | succ index =>
      let position : Fin assumptions.length := ⟨index, by simpa using smaller⟩
      obtain ⟨fuel, ⟨old⟩⟩ := admitted position
      refine ⟨max 1 fuel + 1, ?_⟩
      exact HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an) structural
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
        7 names ruleAt bindingAt selected environment.scope.logical
        (HOLKernelJudgment.holds signature.symbol (environment.encode formula))
        (HOLKernelJudgment.holds signature.symbol (environment.encode (assumptions.get position)))
        environment.scope.logicalSorted
        (HOLKernelJudgment.holds_sorted signature _
          (environment.encoded_sorted formula (Nat.le_of_lt fits) active before))
        (HOLKernelJudgment.holds_sorted signature _
          (environment.encoded_sorted (assumptions.get position)
            (Nat.le_of_lt (environment.assumptionBounds _ (List.get_mem _ _))) active before))
        (environment.assumptionProof position) reading.logical.formula formula (assumptions.get position)
        reading.logical_formula (reading.assertion_formula distinct formula)
        (reading.assertion_formula distinct (assumptions.get position)) old


def materialEncoding (signature : Signature sorts terms) (layout : HOLKernelProofAllocation.Layout) :
    Encoding signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids) Unit Symbol :=
  Encoding.fromInitial signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids)
    (HOLKernelSetOperationInterpretation.initialContext_formed signature)
    HOLKernelSetOperationInterpretation.typeCode
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode symbol)
    (HOLKernelSetOperationInterpretation.typeCode_sorted signature)
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode_sorted signature symbol)

def initialEnvironment (signature : Signature sorts terms) (layout : HOLKernelProofAllocation.Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width) :
    Environment (definitions := definitions) (theorems := theorems) (hypotheses := [])
      (materialEncoding signature layout) [] assumptions 0 :=
  Environment.fromInitial signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids)
    (HOLKernelSetOperationInterpretation.initialContext_formed signature) structural
    HOLKernelSetOperationInterpretation.typeCode
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode symbol)
    (HOLKernelSetOperationInterpretation.typeCode_sorted signature)
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode_sorted signature symbol)
    [] HOLKernelSetOperationInterpretation.noAssignment (by intro type index; nomatch index)
    (HOLKernelSetOperationInterpretation.formation signature.symbol)
    (HOLKernelSetOperationInterpretation.formation_sorted signature)
    (by intro type index; nomatch index)
    (HOLKernelSetOperationInterpretation.constantTyping signature structural) assumptions bounds

theorem initial_proofs_varsBelow (signature : Signature sorts terms) (layout : HOLKernelProofAllocation.Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width) :
    (initialEnvironment (definitions := definitions) signature layout structural assumptions bounds).ProofsVarsBelow
      (7 + layout.width) := by
  have bounded := Environment.fromInitial_proofsVarsBelow (definitions := definitions) (hypotheses := []) signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids)
    (HOLKernelSetOperationInterpretation.initialContext_formed signature) structural
    HOLKernelSetOperationInterpretation.typeCode
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode symbol)
    (HOLKernelSetOperationInterpretation.typeCode_sorted signature)
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode_sorted signature symbol)
    [] HOLKernelSetOperationInterpretation.noAssignment (by intro type index; nomatch index)
    (HOLKernelSetOperationInterpretation.formation signature.symbol)
    (HOLKernelSetOperationInterpretation.formation_sorted signature)
    (by intro type index; nomatch index)
    (HOLKernelSetOperationInterpretation.constantTyping signature structural) assumptions bounds

  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bounded.projection
  · intro type index
    nomatch index
  · exact bounded.constantTyping
  · exact bounded.assumptionProof


def initialReading
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (layout : HOLKernelProofAllocation.Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width) :
    Reading abbreviation profile (initialEnvironment signature layout structural assumptions bounds) BinderNames.nil where
  base := rfl
  constant := by intro type symbol; rfl
  assignment := by intro type index; nomatch index
  names_in_scope := ⟨by simp [BinderNames.toList], by simp [BinderNames.toList]⟩
  formation := formationReading
  logical := sourceContext assumptions
  formation_read := by
    change readJudgmentWith _ signature.symbol BinderNames.nil
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelSetOperationInterpretation.formation signature.symbol)) = _
    rw [expandEquivalence_formation _ _ distinct]
    exact formation_read profile
  logical_read := read_sourceAntecedent profile abbreviation distinct assumptions


theorem initial_assumptions_admitted
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (layout : HOLKernelProofAllocation.Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width) :
    (initialReading abbreviation profile distinct layout structural assumptions bounds).AssumptionsAdmitted ruleAt bindingAt := by
  intro occurrence
  let env := initialEnvironment (definitions := definitions) signature layout structural assumptions bounds
  let reading := initialReading abbreviation profile distinct layout structural assumptions bounds
  let target := layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object
  let native := fun formula : ClosedFormula Symbol => HOLKernelJudgment.holds signature.symbol
    (HOLKernelSetOperationInterpretation.term signature.symbol formula)
  have formed : Preterm.HasType terms target
      (HOLKernelSetOperationInterpretation.formation signature.symbol) [] signature.ids.wff :=
    (HOLKernelSetOperationInterpretation.formation_sorted signature).weakenContext
      (List.replicate layout.limit (.bound signature.ids.object))
  have sorted : ∀ formula ∈ assumptions, Preterm.HasType terms target (native formula) [] signature.ids.wff := by
    intro formula member
    exact HOLKernelJudgment.holds_sorted signature target
      (term_sorted_in_layout signature layout formula (Nat.le_of_lt (bounds formula member)))
  have baseRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 BinderNames.nil (HOLKernelSetOperationInterpretation.formation signature.symbol) = some formationReading.formula :=
    reading.formation_formula
  have readings : ∀ formula ∈ assumptions,
      readFormulaIn abbreviation
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
        7 BinderNames.nil (native formula) = some formula := by
    intro formula _
    exact reading.assertion_formula distinct formula
  obtain ⟨fuel, ⟨tree⟩⟩ := HOLKernelStructuralReadback.hypothesis_admitted
    signature abbreviation (distinct .im) (distinct .an) structural
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 BinderNames.nil ruleAt bindingAt selected native id
    (HOLKernelSetOperationInterpretation.formation signature.symbol) formed
    formationReading.formula baseRead assumptions sorted readings occurrence
  refine ⟨fuel, ?_⟩
  have mappedSorted : ∀ value ∈ assumptions.map native, Preterm.HasType terms target value [] signature.ids.wff := by
    intro value member
    obtain ⟨formula, mem, rfl⟩ := List.mem_map.mp member
    exact sorted formula mem
  have shape : (env.assumptionProof occurrence).val =
      (HOLKernelAssumptions.hypothesis (definitions := definitions) (hypotheses := []) signature structural
        (HOLKernelSetOperationInterpretation.formation signature.symbol) formed
        (assumptions.map native) mappedSorted
        ⟨occurrence.val, by rw [List.length_map]; exact occurrence.isLt⟩).val := by
    rfl
  change Nonempty (AdmittedProof abbreviation theorems target
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 ruleAt bindingAt fuel BinderNames.nil (env.assumptionProof occurrence).val
    (.imp (sourceContext assumptions).formula (assumptions.get occurrence)))
  rw [shape, sourceContext_formula]
  exact ⟨tree⟩


def Reading.bind (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (domain : Ty Unit) {frame : Nat} (active : frame < layout.frames)
    (before : depth + layout.width ≤ layout.workDepth frame) :
    Reading abbreviation profile (environment.bind abbreviation profile structural typing rules binding domain active before)
      (BinderNames.cons (type := domain)
        (HOLKernelProofAllocation.Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)
          (layout.workDepth frame)) names) := by
  let root := HOLKernelProofAllocation.Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)
    (layout.workDepth frame)
  let nextNames : Names (domain :: gamma) := BinderNames.cons root names
  let rho : Rename Unit gamma (domain :: gamma) := fun index => Var.vs index
  have rootEq : root = 7 + layout.workDepth frame := rfl
  have nextScope : InScope 7 nextNames (layout.workDepth frame + 1) := by
    refine ⟨List.nodup_cons.mpr ⟨?_, reading.names_in_scope.1⟩, ?_⟩
    · intro member
      have upper := (reading.names_in_scope.2 root member).2
      omega
    · intro name member
      simp only [nextNames, BinderNames.toList, List.mem_cons] at member
      rcases member with rfl | old
      · constructor <;> omega
      · have limits := reading.names_in_scope.2 name old
        constructor <;> omega
  have related : NamesRel root rho names nextNames := NamesRel.weaken names domain root (Nat.le_refl _)
  have formBound : Preterm.VarsBelow root environment.scope.formation := by
    rw [rootEq]
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.formation_varsBelow (layout.workDepth frame) (by omega)
  have logicBound : Preterm.VarsBelow root environment.scope.logical := by
    rw [rootEq]
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.logical_varsBelow (layout.workDepth frame) before
  have formRead := logical_judgment_rename profile HOLKernelSetOperationReadback.readConstant 7 root
    names nextNames rho related (expandEquivalence signature.symbol abbreviation.reference environment.scope.formation)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root environment.scope.formation formBound)
  rw [reading.formation_read] at formRead
  have logicRead := logical_judgment_rename profile HOLKernelSetOperationReadback.readConstant 7 root
    names nextNames rho related (expandEquivalence signature.symbol abbreviation.reference environment.scope.logical)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root environment.scope.logical logicBound)
  rw [reading.logical_read] at logicRead
  have variableRead : readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelJudgment.hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain))) =
      some (.typing (Term.var (.vz : Var (domain :: gamma) domain))) := by
    rw [reading.base]
    have typed := logical_read_typing profile (Term.var (.vz : Var (domain :: gamma) domain))
      nextNames (layout.workDepth frame + 1) nextScope
    simpa [HOLKernelSetOperationReadback.encode, encodeTerm,
      HOLKernelJudgment.hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
      expandEquivalence_encodeType _ _ distinct, nextNames, BinderNames.nameOf] using typed
  refine {
    base := reading.base
    constant := reading.constant
    assignment := ?_
    names_in_scope := nextScope
    formation := .conjunction (reading.formation.rename rho) (.typing (.var .vz))
    logical := .conjunction (reading.logical.rename rho) (.typing (.var .vz))
    formation_read := ?_
    logical_read := ?_ }
  · intro type index
    cases index with
    | vz => rfl
    | vs index => exact reading.assignment index
  · change readJudgmentWith _ signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelJudgment.conjunction signature.symbol environment.scope.formation
          (HOLKernelJudgment.hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)))) = _
    rw [expandEquivalence_conjunction _ _ (distinct .an), readJudgmentWith_conjunction _ signature.symbol_injective,
      formRead, variableRead]
    rfl
  · change readJudgmentWith _ signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical
          (HOLKernelJudgment.hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)))) = _
    rw [expandEquivalence_conjunction _ _ (distinct .an), readJudgmentWith_conjunction _ signature.symbol_injective,
      logicRead, variableRead]
    rfl

#print axioms Reading.bind
#print axioms HOLKernelProofEnvironment.Environment.logical_varsBelow

#print axioms initial_assumptions_admitted

#print axioms initialReading

#print axioms Reading.assume_assumptions_admitted

#print axioms Reading.typed_admitted
#print axioms Reading.assume

#print axioms Reading.encode_eq
#print axioms Reading.term_read
theorem initial_assumptions_varsBelow (signature : Signature sorts terms)
    (layout : HOLKernelProofAllocation.Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width)
    (occurrence : Fin assumptions.length) :
    ((initialEnvironment (definitions := definitions) signature layout structural assumptions bounds).assumptionProof occurrence).val.VarsBelow
      (7 + layout.width) :=
  (initial_proofs_varsBelow signature layout structural assumptions bounds).assumptionProof occurrence

#print axioms initial_assumptions_varsBelow

open HOLKernelProofAllocation

theorem Reading.formation_typing_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {type : Ty Unit} (source : Term Symbol gamma type)
    (proof : HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := HOLKernelProofEnvironment.NativeContext signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids))
      (hypotheses := [])
      (HOLKernelTypingRules.typed signature.symbol environment.scope.formation (environment.encode source)
        (encodeType signature.symbol encoding.base type))) :
    Nonempty (AdmittedProof abbreviation theorems
      (HOLKernelProofEnvironment.NativeContext signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt 1 names proof.val (.imp reading.formation.formula .top)) :=
  ⟨AdmittedStep.formation proof.property.eval
    (reading.typing_read_in distinct _ _ reading.formation_read source)⟩

/-- Independent admission of the actual native projection from logical
assumptions to the retained formation context. -/
def Reading.ProjectionAdmitted (reading : Reading abbreviation profile environment names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule) : Prop :=
  ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
    (HOLKernelProofEnvironment.NativeContext signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids))
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 ruleAt bindingAt fuel names environment.scope.projection.val
    (.imp reading.logical.formula reading.formation.formula))

theorem initial_projection_admitted
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (layout : HOLKernelProofAllocation.Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width) :
    (initialReading abbreviation profile distinct layout structural assumptions bounds).ProjectionAdmitted ruleAt bindingAt := by
  let reading := initialReading abbreviation profile distinct layout structural assumptions bounds
  let target := layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object
  let native := fun formula : ClosedFormula Symbol => HOLKernelJudgment.holds signature.symbol
    (HOLKernelSetOperationInterpretation.term signature.symbol formula)
  have formed : Preterm.HasType terms target (HOLKernelSetOperationInterpretation.formation signature.symbol) [] signature.ids.wff :=
    (HOLKernelSetOperationInterpretation.formation_sorted signature).weakenContext
      (List.replicate layout.limit (.bound signature.ids.object))
  have sorted : ∀ formula ∈ assumptions, Preterm.HasType terms target (native formula) [] signature.ids.wff := by
    intro formula member
    exact HOLKernelJudgment.holds_sorted signature target
      (term_sorted_in_layout signature layout formula (Nat.le_of_lt (bounds formula member)))
  have readings : ∀ formula ∈ assumptions,
      readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
        7 BinderNames.nil (native formula) = some formula := by
    intro formula _
    exact reading.assertion_formula distinct formula
  obtain ⟨fuel, ⟨tree⟩⟩ := HOLKernelStructuralReadback.formationProjection_admitted signature abbreviation (distinct .im)
    (distinct .an) structural (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 BinderNames.nil ruleAt bindingAt selected native id (HOLKernelSetOperationInterpretation.formation signature.symbol) formed
    reading.formation.formula reading.formation_formula assumptions sorted readings
  refine ⟨fuel, ?_⟩
  change Nonempty (AdmittedProof abbreviation theorems target _ 7 ruleAt bindingAt fuel BinderNames.nil
    (initialEnvironment (definitions := definitions) signature layout structural assumptions bounds).scope.projection.val
    (.imp (sourceContext assumptions).formula formationReading.formula))
  rw [sourceContext_formula]
  exact ⟨tree⟩

theorem Reading.assume_projection_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (admitted : reading.ProjectionAdmitted ruleAt bindingAt)
    (formula : Formula Symbol gamma) (fits : formula.binderDepth < layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame) :
    (reading.assume distinct structural formula fits active before).ProjectionAdmitted ruleAt bindingAt := by
  obtain ⟨fuel, ⟨tree⟩⟩ := admitted
  refine ⟨max 1 fuel + 1, ?_⟩
  exact HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an) structural
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 names ruleAt bindingAt selected environment.scope.logical
    (HOLKernelJudgment.holds signature.symbol (environment.encode formula)) environment.scope.formation
    environment.scope.logicalSorted
    (HOLKernelJudgment.holds_sorted signature _ (environment.encoded_sorted formula (Nat.le_of_lt fits) active before))
    environment.scope.formationSorted environment.scope.projection reading.logical.formula formula reading.formation.formula
    reading.logical_formula (reading.assertion_formula distinct formula) reading.formation_formula tree


theorem weaken_frame_admitted
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {fuel : Nat} {witness : ProofWitness} {formula : Formula Symbol gamma}
    (admitted : AdmittedProof abbreviation theorems
      (layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel names witness formula)
    (lower : Nat) (within : lower ≤ layout.limit)
    (bounded : witness.VarsBelow (7 + lower))
    (domain : Ty Unit) (fresh : Nat) (later : 7 + lower ≤ fresh) :
    Nonempty (AdmittedProof abbreviation theorems
      (layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel (BinderNames.cons (type := domain) fresh names) witness (weaken (σ := domain) formula)) := by
  apply admitted.logical_weaken_of_varsBelow profile abbreviation HOLKernelSetOperationReadback.readConstant
    7 ruleAt bindingAt (7 + lower) _ bounded domain fresh later
  simpa only [HOLKernelProofAllocation.Layout.target, Context.appendBounds, List.length_append,
    List.length_replicate, HOLKernelSetOperationInterpretation.initialContext_length] using Nat.add_le_add_left within 7


theorem Reading.weaken_assumptions_admitted (reading : Reading abbreviation profile environment names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (admitted : reading.AssumptionsAdmitted ruleAt bindingAt)
    (lower : Nat) (within : lower ≤ layout.limit)
    (bounded : environment.ProofsVarsBelow (7 + lower))
    (domain : Ty Unit) (fresh : Nat) (later : 7 + lower ≤ fresh)
    (occurrence : Fin assumptions.length) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
      (layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel (BinderNames.cons (type := domain) fresh names)
      (environment.assumptionProof occurrence).val
      (weaken (σ := domain) (.imp reading.logical.formula (assumptions.get occurrence)))) := by
  obtain ⟨fuel, ⟨tree⟩⟩ := admitted occurrence
  exact ⟨fuel, weaken_frame_admitted ruleAt bindingAt tree lower within (bounded.assumptionProof occurrence)
    domain fresh later⟩

#print axioms Reading.weaken_assumptions_admitted

theorem initial_assumptions_weaken_admitted
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (layout : Layout)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (assumptions : List (ClosedFormula Symbol))
    (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width)
    (occurrence : Fin assumptions.length) (domain : Ty Unit) (fresh : Nat) (later : 7 + layout.width ≤ fresh) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
      (layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel (BinderNames.cons (type := domain) fresh BinderNames.nil)
      ((initialEnvironment (definitions := definitions) signature layout structural assumptions bounds).assumptionProof occurrence).val
      (weaken (σ := domain) (.imp (sourceContext assumptions).formula (assumptions.get occurrence)))) := by
  have within : layout.width ≤ layout.limit := by
    simp only [HOLKernelProofAllocation.Layout.limit, HOLKernelProofAllocation.Layout.workDepth]
    omega
  exact (initialReading abbreviation profile distinct layout structural assumptions bounds).weaken_assumptions_admitted
    ruleAt bindingAt
    (initial_assumptions_admitted abbreviation profile distinct layout structural ruleAt bindingAt selected assumptions bounds)
    layout.width within (initial_proofs_varsBelow signature layout structural assumptions bounds)
    domain fresh later occurrence

#print axioms initial_assumptions_weaken_admitted

theorem Reading.bind_projection_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (admitted : reading.ProjectionAdmitted ruleAt bindingAt)
    (domain : Ty Unit) {frame : Nat} (active : frame < layout.frames)
    (before : depth + layout.width ≤ layout.workDepth frame)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame)) :
    (reading.bind distinct structural typing rules binding domain active before).ProjectionAdmitted ruleAt bindingAt := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let root := HOLKernelProofAllocation.Layout.names initial (layout.workDepth frame)
  let nextNames : Names (domain :: gamma) := BinderNames.cons root names
  let next := reading.bind distinct structural typing rules binding domain active before
  let rho : Rename Unit gamma (domain :: gamma) := fun index => Var.vs index
  let extra := HOLKernelJudgment.hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)
  have related : NamesRel (7 + layout.workDepth frame) rho names nextNames :=
    NamesRel.weaken names domain root (by rfl)
  have formBound : Preterm.VarsBelow (7 + layout.workDepth frame) environment.scope.formation := by
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.formation_varsBelow (layout.workDepth frame) (by omega)
  have logicBound : Preterm.VarsBelow (7 + layout.workDepth frame) environment.scope.logical := by
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.logical_varsBelow (layout.workDepth frame) before
  have formRead := logical_formula_rename profile abbreviation HOLKernelSetOperationReadback.readConstant 7
    (7 + layout.workDepth frame) names nextNames rho related environment.scope.formation formBound
  rw [reading.formation_formula] at formRead
  have logicRead := logical_formula_rename profile abbreviation HOLKernelSetOperationReadback.readConstant 7
    (7 + layout.workDepth frame) names nextNames rho related environment.scope.logical logicBound
  rw [reading.logical_formula] at logicRead
  have bare := next.type_assertion_read distinct (Term.var (.vz : Var (domain :: gamma) domain))
  have extraRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 nextNames extra = some .top := by
    change readJudgmentWith _ signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference extra) = some (.typing (Term.var (.vz : Var (domain :: gamma) domain))) at bare
    simp only [readFormulaIn, bare, Option.map_some, Judgment.formula]
  have rootDeclared : (layout.target initial signature.ids.object)[root]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using layout.workSlots initial signature.ids.object active 0 (by omega)
  have rootSorted : Preterm.HasType terms (layout.target initial signature.ids.object) (.var root) [] signature.ids.object := .var rootDeclared
  have extraSorted := HOLKernelJudgment.hasType_sorted signature _ rootSorted
    (encodeType_sorted signature _ encoding.base encoding.baseSorted domain)
  have within : layout.workDepth frame ≤ layout.limit := layout.workDepth_mono (Nat.le_of_lt active)
  obtain ⟨fuel, ⟨oldTree⟩⟩ := admitted
  obtain ⟨moved⟩ := weaken_frame_admitted ruleAt bindingAt oldTree (layout.workDepth frame) within bounded.projection
    domain root (by rfl)
  let leftPart := HOLKernelStructuralRules.weaken signature structural environment.scope.logical extra environment.scope.formation
    environment.scope.logicalSorted extraSorted environment.scope.formationSorted environment.scope.projection
  let rightPart := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := []) signature structural
    environment.scope.logical extra environment.scope.logicalSorted extraSorted
  obtain ⟨leftTree⟩ := HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an)
    structural (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 nextNames ruleAt bindingAt selected environment.scope.logical extra environment.scope.formation
    environment.scope.logicalSorted extraSorted environment.scope.formationSorted environment.scope.projection
    (weaken (σ := domain) reading.logical.formula) .top (weaken (σ := domain) reading.formation.formula)
    logicRead extraRead formRead moved
  obtain ⟨rightTree⟩ := HOLKernelStructuralReadback.right_admitted signature abbreviation (distinct .im) (distinct .an)
    structural (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 nextNames ruleAt bindingAt (selected .anr) environment.scope.logical extra environment.scope.logicalSorted extraSorted
    (weaken (σ := domain) reading.logical.formula) .top logicRead extraRead
  have joinedRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 nextNames (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical extra) =
      some (.and (weaken (σ := domain) reading.logical.formula) .top) := by
    simp only [HOLKernelStructuralReadback.read_conjunction abbreviation signature.symbol_injective (distinct .an),
      logicRead, extraRead, Option.bind_some, Option.map_some]
    rfl
  obtain ⟨joined⟩ := HOLKernelStructuralReadback.pair_admitted signature abbreviation (distinct .im) (distinct .an)
    structural (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 nextNames ruleAt bindingAt (selected .ian)
    (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical extra) environment.scope.formation extra
    (HOLKernelJudgment.conjunction_sorted signature _ environment.scope.logicalSorted extraSorted)
    environment.scope.formationSorted extraSorted leftPart rightPart
    (.and (weaken (σ := domain) reading.logical.formula) .top) (weaken (σ := domain) reading.formation.formula) .top
    joinedRead formRead extraRead leftTree rightTree
  refine ⟨max (max 1 fuel + 1) 1 + 1, ?_⟩
  have logicalEq : (reading.bind distinct structural typing rules binding domain active before).logical.formula =
      .and (weaken (σ := domain) reading.logical.formula) .top := by
    change Term.and (reading.logical.rename rho).formula .top = _
    rw [Judgment.rename_formula]
    rfl
  have formationEq : (reading.bind distinct structural typing rules binding domain active before).formation.formula =
      .and (weaken (σ := domain) reading.formation.formula) .top := by
    change Term.and (reading.formation.rename rho).formula .top = _
    rw [Judgment.rename_formula]
    rfl
  change Nonempty (AdmittedProof abbreviation theorems _ _ 7 ruleAt bindingAt _ _ _
    (.imp (reading.bind distinct structural typing rules binding domain active before).logical.formula
      (reading.bind distinct structural typing rules binding domain active before).formation.formula))
  rw [logicalEq, formationEq]
  exact ⟨joined⟩

#print axioms Reading.bind_projection_admitted


open HOLKernelTermAssignments

theorem Reading.bind_assumptions_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming)
    (admitted : reading.AssumptionsAdmitted ruleAt bindingAt)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (domain : Ty Unit) {frame : Nat} (active : frame < layout.frames)
    (before : depth + layout.width ≤ layout.workDepth frame)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame)) :
    (reading.bind distinct structural typing rules binding domain active before).AssumptionsAdmitted ruleAt bindingAt := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let root := Layout.names initial (layout.workDepth frame)
  let nextNames : Names (domain :: gamma) := BinderNames.cons root names
  let rho : Rename Unit gamma (domain :: gamma) := fun index => Var.vs index
  let next := reading.bind distinct structural typing rules binding domain active before
  have weakenEq (formula : Formula Symbol gamma) : weaken (σ := domain) formula = Mettapedia.Logic.HOL.rename rho formula := by
    exact rename_ext (fun {_} index => rfl) formula
  have rootEq : root = 7 + layout.workDepth frame := rfl
  have within : layout.workDepth frame ≤ layout.limit := layout.workDepth_mono (Nat.le_of_lt active)
  have related : NamesRel root rho names nextNames := NamesRel.weaken names domain root (Nat.le_refl _)
  have formBound : Preterm.VarsBelow root environment.scope.formation := by
    rw [rootEq]
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.formation_varsBelow (layout.workDepth frame) (by omega)
  have logicBound : Preterm.VarsBelow root environment.scope.logical := by
    rw [rootEq]
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.logical_varsBelow (layout.workDepth frame) before
  have formRead := logical_judgment_rename profile HOLKernelSetOperationReadback.readConstant 7 root
    names nextNames rho related (expandEquivalence signature.symbol abbreviation.reference environment.scope.formation)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root environment.scope.formation formBound)
  rw [reading.formation_read] at formRead
  have logicRead := logical_judgment_rename profile HOLKernelSetOperationReadback.readConstant 7 root
    names nextNames rho related (expandEquivalence signature.symbol abbreviation.reference environment.scope.logical)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root environment.scope.logical logicBound)
  rw [reading.logical_read] at logicRead
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  obtain ⟨movedProjection⟩ := weaken_frame_admitted ruleAt bindingAt projectionTree
    (layout.workDepth frame) within bounded.projection domain root (by rfl)
  have projectionInFrame : AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt projectionFuel nextNames environment.scope.projection.val
      (.imp (reading.logical.rename rho).formula (reading.formation.rename rho).formula) := by
    rw [weakenEq] at movedProjection
    simpa only [Judgment.rename_formula, Mettapedia.Logic.HOL.rename] using movedProjection
  have rootRead : HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 nextNames
      (.var root) = some ⟨domain, Term.var .vz⟩ := by
    simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  have assignmentEq : ∀ {type} (index : Var gamma type),
      environment.assignment index = .var (nextNames.nameOf (rho index)) := by
    intro type index
    exact reading.assignment index
  have bindersAbove : ∀ level, 7 ≤ Layout.names initial level := by intro level; change 7 ≤ 7 + level; omega
  intro occurrence
  let position : Fin assumptions.length := ⟨occurrence.val, by simpa [weakenHyps] using occurrence.isLt⟩
  let source := assumptions.get position
  have sourceBound : source.binderDepth < layout.width := environment.assumptionBounds _ (List.get_mem _ _)
  let windows := environment.windows active before
  have fit : source.binderDepth + 1 ≤ windows.width := by change source.binderDepth + 1 ≤ layout.width; omega
  have sourceNames : ∀ offset < source.binderDepth,
      Layout.names initial (windows.sourceDepth + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · change 7 + (depth + offset) = 7 + layout.workDepth frame at same
      omega
    · have upper := (reading.names_in_scope.2 _ member).2
      change 7 + (depth + offset) < 7 + depth at upper
      omega
  have targetNames : ∀ offset < source.binderDepth,
      Layout.names initial (windows.workDepth + 1 + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · change 7 + (layout.workDepth frame + 1 + offset) = 7 + layout.workDepth frame at same
      omega
    · have upper := (reading.names_in_scope.2 _ member).2
      change 7 + (layout.workDepth frame + 1 + offset) < 7 + depth at upper
      omega
  have temporaryNames : ∀ offset < source.binderDepth,
      Layout.names initial (windows.temporaryDepth + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · change 7 + (layout.temporaryDepth frame + offset) = 7 + layout.workDepth frame at same
      simp only [Layout.temporaryDepth] at same
      omega
    · have upper := (reading.names_in_scope.2 _ member).2
      change 7 + (layout.temporaryDepth frame + offset) < 7 + depth at upper
      simp only [Layout.temporaryDepth] at upper
      omega
  obtain ⟨premiseFuel, ⟨premiseTree⟩⟩ := reading.weaken_assumptions_admitted ruleAt bindingAt admitted
    (layout.workDepth frame) within bounded domain root (by rfl) position
  have premiseInFrame : AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt premiseFuel nextNames (environment.assumptionProof position).val
      (.imp (reading.logical.rename rho).formula (Mettapedia.Logic.HOL.rename rho source)) := by
    rw [weakenEq] at premiseTree
    simpa only [Judgment.rename_formula, Mettapedia.Logic.HOL.rename] using premiseTree
  let lifted := HOLKernelSourceBinding.weakenAssumption (domain := domain) signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    source environment.assignment environment.scope windows fit environment.assignmentSorted environment.variableTyping
    environment.constantTyping (environment.assumptionProof position)
  obtain ⟨fuel, ⟨liftedTree⟩⟩ := HOLKernelSourceBindingReadback.weakenAssumption_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant (fun {_} symbol => HOLKernelSetOperationInterpretation.symbolIndex symbol) 7
    (fun symbol => HOLKernelSetOperationReadback.readConstant_symbol symbol)
    (fun symbol => HOLKernelSetOperationReadback.symbolIndex_bound symbol)
    encoding.base encoding.constant reading.base
    (by intro type symbol; cases symbol <;> exact reading.constant _)
    (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) bindersAbove bindersAbove encoding.baseIndependent encoding.baseIndependent
    source environment.assignment environment.scope windows fit environment.assignmentSorted environment.variableTyping
    environment.constantTyping (environment.assumptionProof position) rho nextNames next.names_in_scope.1
    (fun name member => (next.names_in_scope.2 name member).1) assignmentEq sourceNames targetNames temporaryNames
    (reading.logical.rename rho) (reading.formation.rename rho) logicRead formRead (Term.var .vz) rootRead
    ruleAt bindingAt selected structuralSelected bindingSelected projectionInFrame premiseInFrame
  have same : (weakenHyps (σ := domain) assumptions).get occurrence = weaken (σ := domain) (assumptions.get position) := by
    change (assumptions.map (weaken (σ := domain)))[occurrence.val] = _
    simp only [List.getElem_map]
    rfl
  let extra := HOLKernelJudgment.hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)
  let claim := fun expression : Formula Symbol (domain :: gamma) =>
    HOLKernelJudgment.entails signature.symbol (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical extra)
      (HOLKernelJudgment.holds signature.symbol (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
        (Assignment.extend (.var root) environment.assignment) (layout.workDepth frame + 1) expression))
  change ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 ruleAt bindingAt fuel nextNames
    (Eq.mpr (congrArg (fun expression => HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := layout.target initial signature.ids.object) (hypotheses := []) (claim expression)) same) lifted).val
    (.imp next.logical.formula ((weakenHyps (σ := domain) assumptions).get occurrence)))
  rw [HOLKernelStructuralRules.CheckedProof.val_mpr claim same lifted, same]
  have logicalEq : next.logical.formula = .and (reading.logical.rename rho).formula .top := rfl
  rw [logicalEq]
  let receipt : ProofWitness := lifted.val
  change ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 ruleAt bindingAt fuel nextNames receipt
    (.imp (.and (reading.logical.rename rho).formula .top) (weaken (σ := domain) (assumptions.get position))))
  rw [weakenEq]
  exact ⟨fuel, ⟨liftedTree⟩⟩

#print axioms Reading.bind_assumptions_admitted
/-- Moving the encoded term to a later allocated name window preserves its exact source reading. -/
theorem Reading.term_read_at (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type) (atDepth : Nat) (afterSource : depth ≤ atDepth) :
    HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol encoding.base encoding.constant
          (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
          environment.assignment atDepth source)) = some ⟨type, source⟩ := by
  have result := HOLKernelAlphaReadback.encoded_read abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant Rename.id names environment.assignment reading.assignment
    (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
    (Layout.names_injective _) (by intro level; change 7 ≤ 7 + level; omega)
    source atDepth reading.names_in_scope.1 (fun name member => (reading.names_in_scope.2 name member).1)
    (by
      intro offset _ type index
      apply BinderNames.ne_nameOf_of_not_mem
      intro member
      have upper := (reading.names_in_scope.2 _ member).2
      change 7 + (atDepth + offset) < 7 + depth at upper
      omega)
  simpa only [rename_id] using result

#print axioms Reading.term_read_at

/-- Rebinding an allocated term preserves independent receipt admission, using the retained formation projection. -/
theorem Reading.rebind_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type)
    (windows : HOLKernelSourceBinding.RebindingWindows (NativeContext (signature := signature) (layout := layout))
      signature.ids.object environment.scope.formation
      (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
      (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)))
    (fits : source.binderDepth ≤ windows.width)
    (sourceAfter : depth ≤ windows.sourceDepth) (workAfter : depth ≤ windows.workDepth)
    (temporaryAfter : depth ≤ windows.temporaryDepth)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ruleAt (structural.index .syl) = some (.structural .syl))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel names
      (HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
        encoding.base encoding.constant
        (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
        (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
        encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
        encoding.baseIndependent encoding.baseIndependent source environment.assignment environment.scope windows fits
        environment.assignmentSorted environment.variableTyping environment.constantTyping).val
      (.imp reading.logical.formula (.eq source source))) := by
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, depth ≤ location → ∀ offset,
      Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (location + offset) ∉ names.toList := by
    intro location afterSource offset member
    have upper := (reading.names_in_scope.2 _ member).2
    change 7 + (location + offset) < 7 + depth at upper
    omega
  have result := HOLKernelSourceBindingReadback.rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant
    (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
    (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
    encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    encoding.baseIndependent encoding.baseIndependent source environment.assignment environment.scope windows fits
    environment.assignmentSorted environment.variableTyping environment.constantTyping Rename.id names reading.names_in_scope.1
    (fun name member => (reading.names_in_scope.2 name member).1) reading.assignment
    (fun offset _ {_} index => BinderNames.ne_nameOf_of_not_mem names (fresh _ sourceAfter offset) index)
    (fun offset _ {_} index => BinderNames.ne_nameOf_of_not_mem names (fresh _ workAfter offset) index)
    (fun offset _ {_} index => BinderNames.ne_nameOf_of_not_mem names (fresh _ temporaryAfter offset) index) reading.logical reading.formation reading.logical_read reading.formation_read
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
  simpa only [rename_id] using result

#print axioms Reading.rebind_admitted


end Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback

