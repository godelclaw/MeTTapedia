import Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback

/-!
# Contextual readings of maintained HOL compiler environments

A native compiler environment may be read in another typed context along a
source-variable renaming. The reading retains the actual parameter encoding,
variable assignment and decoded formation/logical judgments. Its source-position
bound is derived from native sorting and occurrence independence.

Successful readings commute with lookup-preserving maps. Source assumptions and
bound-variable extensions preserve the reading and independently admitted
ordered hypotheses/projection receipts. Additional reader variables preserve
those receipts only under their actual native scope bounds. The temporary
argument-frame lemma retains the source binder window and the next work-bank
bound needed by contextual compiler induction. No arbitrary proof-tree
transport or complete compiler-image theorem is asserted here.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback HOLKernelProofEnvironment
open HOLKernelTermAssignments HOLKernelProofAllocation HOLKernelJudgment
open HOLKernelSetOperationProofReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms} {layout : Layout}
variable {encoding : Encoding signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids) Unit Symbol}
variable {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {depth : Nat}

/-- An actual compiler environment read along a typed source renaming. The
source-variable image precedes the source binder bank; the reader may contain
additional variables. -/
structure ContextualReading
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := []) encoding gamma assumptions depth)
    {target : Ctx Unit} (rho : Rename Unit gamma target) (names : Names target) where
  base : encoding.base = HOLKernelSetOperationInterpretation.typeCode
  constant : ∀ {type} (symbol : Symbol type), encoding.constant symbol = HOLKernelSetOperationInterpretation.symbolCode symbol
  assignment : ∀ {type} (index : Var gamma type), environment.assignment index = .var (names.nameOf (rho index))
  names_distinct : names.toList.Nodup
  names_above : ∀ name ∈ names.toList, 7 ≤ name
  formation : Judgment Symbol target
  logical : Judgment Symbol target
  formation_read : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    signature.symbol names (expandEquivalence signature.symbol abbreviation.reference environment.scope.formation) = some formation
  logical_read : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    signature.symbol names (expandEquivalence signature.symbol abbreviation.reference environment.scope.logical) = some logical

variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
variable {profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
variable {environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := []) encoding gamma assumptions depth}
variable {target : Ctx Unit} {rho : Rename Unit gamma target} {names : Names target}

def Reading.contextual {sourceNames : Names gamma} (reading : Reading abbreviation profile environment sourceNames) :
    ContextualReading abbreviation profile environment Rename.id sourceNames where
  base := reading.base
  constant := reading.constant
  assignment := reading.assignment
  names_distinct := reading.names_in_scope.1
  names_above := fun name member => (reading.names_in_scope.2 name member).1
  formation := reading.formation
  logical := reading.logical
  formation_read := reading.formation_read
  logical_read := reading.logical_read

def ContextualReading.rename (reading : ContextualReading abbreviation profile environment rho names)
    {delta : Ctx Unit} (sigma : Rename Unit target delta) (nextNames : Names delta)
    (nextDistinct : nextNames.toList.Nodup) (nextAbove : ∀ name ∈ nextNames.toList, 7 ≤ name)
    (preserved : LookupPreserving HOLKernelSetOperationReadback.readConstant sigma names nextNames) :
    ContextualReading abbreviation profile environment (fun index => sigma (rho index)) nextNames where
  base := reading.base
  constant := reading.constant
  assignment := by
    intro type index
    rw [preserved.nameOf reading.names_distinct (rho index)]
    exact reading.assignment index
  names_distinct := nextDistinct
  names_above := nextAbove
  formation := reading.formation.rename sigma
  logical := reading.logical.rename sigma
  formation_read := logical_judgment_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names nextNames sigma preserved _ reading.formation reading.formation_read
  logical_read := logical_judgment_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names nextNames sigma preserved _ reading.logical reading.logical_read

/-- The source-position bound follows from the actual native assignment's
sorting and occurrence-independence invariant. -/
theorem ContextualReading.source_before (reading : ContextualReading abbreviation profile environment rho names)
    {type : Ty Unit} (index : Var gamma type) : names.nameOf (rho index) < 7 + depth := by
  have bounded := environment.assignment_varsBelow depth (Nat.le_refl _) index
  rw [reading.assignment] at bounded
  simpa only [Preterm.VarsBelow, HOLKernelSetOperationInterpretation.initialContext_length] using bounded

theorem ContextualReading.term_read_at (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type) (level : Nat) (later : depth ≤ level) :
    HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 names
      (expandEquivalence signature.symbol abbreviation.reference
        (encodeWithAssignment signature.symbol encoding.base encoding.constant
          (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) environment.assignment level source)) =
      some ⟨type, HOL.rename rho source⟩ :=
  HOLKernelAlphaReadback.encoded_read abbreviation profile distinct HOLKernelSetOperationReadback.readConstant
    HOLKernelSetOperationInterpretation.symbolIndex 7 HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant rho names environment.assignment reading.assignment
    (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) (Layout.names_injective _)
    (by intro position; change 7 ≤ 7 + position; omega) source level reading.names_distinct reading.names_above
    (by
      intro offset _ type index same
      have below := reading.source_before index
      change 7 + (level + offset) = names.nameOf (rho index) at same
      omega)

theorem ContextualReading.term_read (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type) :
    HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 names
      (expandEquivalence signature.symbol abbreviation.reference (environment.encode source)) = some ⟨type, HOL.rename rho source⟩ :=
  reading.term_read_at distinct source depth (Nat.le_refl _)

theorem ContextualReading.logical_formula (reading : ContextualReading abbreviation profile environment rho names) :
    readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names environment.scope.logical = some reading.logical.formula := by
  simp only [readFormulaIn, reading.logical_read, Option.map_some]

theorem ContextualReading.formation_formula (reading : ContextualReading abbreviation profile environment rho names) :
    readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 names environment.scope.formation = some reading.formation.formula := by
  simp only [readFormulaIn, reading.formation_read, Option.map_some]

theorem ContextualReading.type_read (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference) (type : Ty Unit) :
    readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol encoding.base type)) = some type := by
  rw [reading.base]
  change readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol (fun _ : Unit => .var 0) type)) = some type
  rw [expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
  exact readType_encode signature.symbol signature.symbol_injective type

theorem ContextualReading.assertion_read (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference) (formula : Formula Symbol gamma) :
    readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference (holds signature.symbol (environment.encode formula))) =
      some (.assertion (HOL.rename rho formula)) := by
  have decoded := reading.term_read distinct formula
  simp [holds, applySymbol, Preterm.applyArgs, expandEquivalence, readJudgmentWith,
    readHead_reference signature.symbol signature.symbol_injective, decoded, expect_same]

theorem ContextualReading.assertion_formula (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference) (formula : Formula Symbol gamma) :
    readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 names
      (holds signature.symbol (environment.encode formula)) = some (HOL.rename rho formula) := by
  simp only [readFormulaIn, reading.assertion_read distinct formula, Option.map_some, Judgment.formula]

theorem ContextualReading.typing_read (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference) {type : Ty Unit} (source : Term Symbol gamma type) :
    readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelTypingRules.typed signature.symbol environment.scope.logical (environment.encode source) (encodeType signature.symbol encoding.base type))) =
      some (.consequence reading.logical (.typing (HOL.rename rho source))) :=
  HOLKernelCongruenceReadback.typing_read signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    names _ _ _ reading.logical (HOL.rename rho source) reading.logical_read (reading.type_read distinct type) (reading.term_read distinct source)

theorem ContextualReading.typed_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    {type : Ty Unit} (source : Term Symbol gamma type)
    (fits : source.binderDepth ≤ layout.width) {frame : Nat} (active : frame < layout.frames)
    (before : depth + layout.width ≤ layout.workDepth frame) :
    Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt 1 names
      (environment.typed structural typing source fits active before).val (.imp reading.logical.formula .top)) :=
  ⟨AdmittedStep.formation (environment.typed structural typing source fits active before).property.eval (reading.typing_read distinct source)⟩

def ContextualReading.assume (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (formula : Formula Symbol gamma) (fits : formula.binderDepth < layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame) :
    ContextualReading abbreviation profile (environment.assume structural formula fits active before) rho names where
  base := reading.base
  constant := reading.constant
  assignment := reading.assignment
  names_distinct := reading.names_distinct
  names_above := reading.names_above
  formation := reading.formation
  logical := .conjunction reading.logical (.assertion (HOL.rename rho formula))
  formation_read := reading.formation_read
  logical_read := by
    change readJudgmentWith _ signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference (conjunction signature.symbol environment.scope.logical
        (holds signature.symbol (environment.encode formula)))) = _
    rw [expandEquivalence_conjunction _ _ (distinct .an), readJudgmentWith_conjunction _ signature.symbol_injective,
      reading.logical_read, reading.assertion_read distinct formula]
    rfl

#print axioms Reading.contextual
#print axioms ContextualReading.rename
#print axioms ContextualReading.source_before
#print axioms ContextualReading.term_read_at
#print axioms ContextualReading.term_read
#print axioms ContextualReading.logical_formula
#print axioms ContextualReading.formation_formula
#print axioms ContextualReading.type_read
#print axioms ContextualReading.assertion_read
#print axioms ContextualReading.assertion_formula
#print axioms ContextualReading.typing_read
#print axioms ContextualReading.typed_admitted
#print axioms ContextualReading.assume

def ContextualReading.weaken (reading : ContextualReading abbreviation profile environment rho names)
    (domain : Ty Unit) (name : Nat) (above : 7 ≤ name) (absent : names.lookup? name = none)
    (dictionaryFresh : HOLKernelSetOperationReadback.readConstant name = none) :
    ContextualReading abbreviation profile environment (fun index => Var.vs (rho index)) (BinderNames.cons (type := domain) name names) :=
  reading.rename (Rename.weaken (σ := domain)) (BinderNames.cons name names)
    (List.nodup_cons.mpr ⟨BinderNames.not_mem_of_lookup?_eq_none names _ absent, reading.names_distinct⟩)
    (by
      intro position member
      rcases List.mem_cons.mp member with rfl | old
      · exact above
      · exact reading.names_above _ old)
    (LookupPreserving.weaken HOLKernelSetOperationReadback.readConstant names domain name absent dictionaryFresh)

def ContextualReading.bind (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (domain : Ty Unit) {frame : Nat} (active : frame < layout.frames)
    (before : depth + layout.width ≤ layout.workDepth frame)
    (scope : InScope 7 names (layout.workDepth frame)) :
    ContextualReading abbreviation profile (environment.bind abbreviation profile structural typing rules binding domain active before)
      (Rename.lift rho)
      (BinderNames.cons (type := domain)
        (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (layout.workDepth frame)) names) := by
  let root := Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (layout.workDepth frame)
  let nextNames : Names (domain :: target) := BinderNames.cons root names
  have rootEq : root = 7 + layout.workDepth frame := rfl
  have absent : names.lookup? root = none := by
    rw [rootEq]
    exact scope.fresh
  have dictionaryFresh : HOLKernelSetOperationReadback.readConstant root = none := by
    rw [rootEq, Nat.add_comm]
    rfl
  have preserved : LookupPreserving HOLKernelSetOperationReadback.readConstant (Rename.weaken (σ := domain)) names nextNames :=
    LookupPreserving.weaken HOLKernelSetOperationReadback.readConstant names domain root absent dictionaryFresh
  have formRead := logical_judgment_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names nextNames
    (Rename.weaken (σ := domain)) preserved _ reading.formation reading.formation_read
  have logicRead := logical_judgment_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names nextNames
    (Rename.weaken (σ := domain)) preserved _ reading.logical reading.logical_read
  have variableRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol nextNames (expandEquivalence signature.symbol abbreviation.reference
        (hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain))) =
      some (.typing (Term.var (.vz : Var (domain :: target) domain))) := by
    have ty := reading.type_read distinct domain
    have variableRead : HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 nextNames (.var root) =
        some ⟨domain, Term.var (.vz : Var (domain :: target) domain)⟩ := by
      simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
    simp [hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
      readHead_reference signature.symbol signature.symbol_injective, readTypingWith, ty, variableRead, expect_same]
  refine {
    base := reading.base
    constant := reading.constant
    assignment := ?_
    names_distinct := List.nodup_cons.mpr ⟨BinderNames.not_mem_of_lookup?_eq_none names _ absent, reading.names_distinct⟩
    names_above := ?_
    formation := .conjunction (reading.formation.rename (Rename.weaken (σ := domain))) (.typing (.var .vz))
    logical := .conjunction (reading.logical.rename (Rename.weaken (σ := domain))) (.typing (.var .vz))
    formation_read := ?_
    logical_read := ?_ }
  · intro type index
    cases index with
    | vz => rfl
    | vs index => exact reading.assignment index
  · intro name member
    rcases List.mem_cons.mp member with rfl | old
    · change 7 ≤ 7 + layout.workDepth frame; omega
    · exact reading.names_above _ old
  · change readJudgmentWith _ signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference
        (conjunction signature.symbol environment.scope.formation (hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)))) = _
    rw [expandEquivalence_conjunction _ _ (distinct .an), readJudgmentWith_conjunction _ signature.symbol_injective, formRead, variableRead]
    rfl
  · change readJudgmentWith _ signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference
        (conjunction signature.symbol environment.scope.logical (hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)))) = _
    rw [expandEquivalence_conjunction _ _ (distinct .an), readJudgmentWith_conjunction _ signature.symbol_injective, logicRead, variableRead]
    rfl

def ContextualReading.ProjectionAdmitted (reading : ContextualReading abbreviation profile environment rho names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule) : Prop :=
  ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
    environment.scope.projection.val (.imp reading.logical.formula reading.formation.formula))

def ContextualReading.AssumptionsAdmitted (reading : ContextualReading abbreviation profile environment rho names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule) : Prop :=
  ∀ occurrence : Fin assumptions.length, ∃ fuel,
    Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (environment.assumptionProof occurrence).val (.imp reading.logical.formula (HOL.rename rho (assumptions.get occurrence))))

theorem Reading.contextual_projection {sourceNames : Names gamma} (reading : Reading abbreviation profile environment sourceNames)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (admitted : reading.ProjectionAdmitted ruleAt bindingAt) : reading.contextual.ProjectionAdmitted ruleAt bindingAt := admitted

theorem Reading.contextual_assumptions {sourceNames : Names gamma} (reading : Reading abbreviation profile environment sourceNames)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (admitted : reading.AssumptionsAdmitted ruleAt bindingAt) : reading.contextual.AssumptionsAdmitted ruleAt bindingAt := by
  intro occurrence
  simpa only [Reading.contextual, NativeContext, rename_id] using admitted occurrence

theorem ContextualReading.assume_assumptions_admitted (reading : ContextualReading abbreviation profile environment rho names)
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
        reading.logical.formula (HOL.rename rho formula) reading.logical_formula (reading.assertion_formula distinct formula)
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
        (environment.assumptionProof position) reading.logical.formula (HOL.rename rho formula) (HOL.rename rho (assumptions.get position))
        reading.logical_formula (reading.assertion_formula distinct formula)
        (reading.assertion_formula distinct (assumptions.get position)) old


theorem ContextualReading.assume_projection_admitted (reading : ContextualReading abbreviation profile environment rho names)
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
    environment.scope.formationSorted environment.scope.projection reading.logical.formula (HOL.rename rho formula) reading.formation.formula
    reading.logical_formula (reading.assertion_formula distinct formula) reading.formation_formula tree


#print axioms ContextualReading.weaken
#print axioms ContextualReading.bind
#print axioms Reading.contextual_projection
#print axioms Reading.contextual_assumptions
#print axioms ContextualReading.assume_assumptions_admitted
#print axioms ContextualReading.assume_projection_admitted

theorem ContextualReading.type_assertion_read (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference) {type : Ty Unit} (source : Term Symbol gamma type) :
    readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference
        (hasType signature.symbol (environment.encode source) (encodeType signature.symbol encoding.base type))) =
      some (.typing (HOL.rename rho source)) := by
  have termRead := reading.term_read distinct source
  have typeRead := reading.type_read distinct type
  simp [hasType, applySymbol, Preterm.applyArgs, expandEquivalence, distinct, readJudgmentWith,
    readHead_reference signature.symbol signature.symbol_injective, readTypingWith, typeRead, termRead, expect_same]

theorem ContextualReading.weaken_projection_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (admitted : reading.ProjectionAdmitted ruleAt bindingAt)
    (lower : Nat) (within : lower ≤ layout.limit)
    (bounded : environment.scope.projection.val.VarsBelow (7 + lower))
    (domain : Ty Unit) (name : Nat) (later : 7 + lower ≤ name)
    (absent : names.lookup? name = none) (dictionaryFresh : HOLKernelSetOperationReadback.readConstant name = none) :
    (reading.weaken domain name (by omega) absent dictionaryFresh).ProjectionAdmitted ruleAt bindingAt := by
  obtain ⟨fuel, ⟨tree⟩⟩ := admitted
  obtain ⟨moved⟩ := tree.logical_weaken_of_varsBelow profile abbreviation HOLKernelSetOperationReadback.readConstant 7 ruleAt bindingAt
    (7 + lower) (by
      simpa only [NativeContext, HOLKernelProofEnvironment.NativeContext, Layout.target, Context.appendBounds,
        List.length_append, List.length_replicate, HOLKernelSetOperationInterpretation.initialContext_length] using Nat.add_le_add_left within 7)
    bounded domain name later
  refine ⟨fuel, ⟨?_⟩⟩
  simpa only [ContextualReading.weaken, ContextualReading.rename, Judgment.rename_formula, HOL.rename, HOL.weaken] using moved

theorem ContextualReading.weaken_assumptions_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (admitted : reading.AssumptionsAdmitted ruleAt bindingAt)
    (lower : Nat) (within : lower ≤ layout.limit)
    (bounded : environment.ProofsVarsBelow (7 + lower))
    (domain : Ty Unit) (name : Nat) (later : 7 + lower ≤ name)
    (absent : names.lookup? name = none) (dictionaryFresh : HOLKernelSetOperationReadback.readConstant name = none) :
    (reading.weaken domain name (by omega) absent dictionaryFresh).AssumptionsAdmitted ruleAt bindingAt := by
  intro occurrence
  obtain ⟨fuel, ⟨tree⟩⟩ := admitted occurrence
  obtain ⟨moved⟩ := tree.logical_weaken_of_varsBelow profile abbreviation HOLKernelSetOperationReadback.readConstant 7 ruleAt bindingAt
    (7 + lower) (by
      simpa only [NativeContext, HOLKernelProofEnvironment.NativeContext, Layout.target, Context.appendBounds,
        List.length_append, List.length_replicate, HOLKernelSetOperationInterpretation.initialContext_length] using Nat.add_le_add_left within 7)
    (bounded.assumptionProof occurrence) domain name later
  refine ⟨fuel, ⟨?_⟩⟩
  simpa only [ContextualReading.weaken, ContextualReading.rename, Judgment.rename_formula, HOL.rename, HOL.weaken, rename_comp, Rename.weaken] using moved

#print axioms ContextualReading.type_assertion_read
#print axioms ContextualReading.weaken_projection_admitted
#print axioms ContextualReading.weaken_assumptions_admitted
theorem ContextualReading.bind_projection_admitted (reading : ContextualReading abbreviation profile environment rho names)
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
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    (scope : InScope 7 names (layout.workDepth frame)) :
    (reading.bind distinct structural typing rules binding domain active before scope).ProjectionAdmitted ruleAt bindingAt := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let root := HOLKernelProofAllocation.Layout.names initial (layout.workDepth frame)
  let nextNames : Names (domain :: target) := BinderNames.cons root names
  let next := reading.bind distinct structural typing rules binding domain active before scope
  let shift : Rename Unit target (domain :: target) := fun index => Var.vs index
  let extra := HOLKernelJudgment.hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)
  have related : NamesRel (7 + layout.workDepth frame) shift names nextNames :=
    NamesRel.weaken names domain root (by rfl)
  have formBound : Preterm.VarsBelow (7 + layout.workDepth frame) environment.scope.formation := by
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.formation_varsBelow (layout.workDepth frame) (by omega)
  have logicBound : Preterm.VarsBelow (7 + layout.workDepth frame) environment.scope.logical := by
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.logical_varsBelow (layout.workDepth frame) before
  have formRead := logical_formula_rename profile abbreviation HOLKernelSetOperationReadback.readConstant 7
    (7 + layout.workDepth frame) names nextNames shift related environment.scope.formation formBound
  rw [reading.formation_formula] at formRead
  have logicRead := logical_formula_rename profile abbreviation HOLKernelSetOperationReadback.readConstant 7
    (7 + layout.workDepth frame) names nextNames shift related environment.scope.logical logicBound
  rw [reading.logical_formula] at logicRead
  have bare := next.type_assertion_read distinct (Term.var .vz)
  have extraRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 nextNames extra = some .top := by
    change readJudgmentWith _ signature.symbol nextNames
      (expandEquivalence signature.symbol abbreviation.reference extra) = some (.typing (Term.var (.vz : Var (domain :: target) domain))) at bare
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
    (HOL.weaken (σ := domain) reading.logical.formula) .top (HOL.weaken (σ := domain) reading.formation.formula)
    logicRead extraRead formRead moved
  obtain ⟨rightTree⟩ := HOLKernelStructuralReadback.right_admitted signature abbreviation (distinct .im) (distinct .an)
    structural (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 nextNames ruleAt bindingAt (selected .anr) environment.scope.logical extra environment.scope.logicalSorted extraSorted
    (HOL.weaken (σ := domain) reading.logical.formula) .top logicRead extraRead
  have joinedRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 nextNames (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical extra) =
      some (.and (HOL.weaken (σ := domain) reading.logical.formula) .top) := by
    simp only [HOLKernelStructuralReadback.read_conjunction abbreviation signature.symbol_injective (distinct .an),
      logicRead, extraRead, Option.bind_some, Option.map_some]
    rfl
  obtain ⟨joined⟩ := HOLKernelStructuralReadback.pair_admitted signature abbreviation (distinct .im) (distinct .an)
    structural (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 nextNames ruleAt bindingAt (selected .ian)
    (HOLKernelJudgment.conjunction signature.symbol environment.scope.logical extra) environment.scope.formation extra
    (HOLKernelJudgment.conjunction_sorted signature _ environment.scope.logicalSorted extraSorted)
    environment.scope.formationSorted extraSorted leftPart rightPart
    (.and (HOL.weaken (σ := domain) reading.logical.formula) .top) (HOL.weaken (σ := domain) reading.formation.formula) .top
    joinedRead formRead extraRead leftTree rightTree
  refine ⟨max (max 1 fuel + 1) 1 + 1, ?_⟩
  have logicalEq : (reading.bind distinct structural typing rules binding domain active before scope).logical.formula =
      .and (HOL.weaken (σ := domain) reading.logical.formula) .top := by
    change Term.and (reading.logical.rename shift).formula .top = _
    rw [Judgment.rename_formula]
    rfl
  have formationEq : (reading.bind distinct structural typing rules binding domain active before scope).formation.formula =
      .and (HOL.weaken (σ := domain) reading.formation.formula) .top := by
    change Term.and (reading.formation.rename shift).formula .top = _
    rw [Judgment.rename_formula]
    rfl
  change Nonempty (AdmittedProof abbreviation theorems _ _ 7 ruleAt bindingAt _ _ _
    (.imp (reading.bind distinct structural typing rules binding domain active before scope).logical.formula
      (reading.bind distinct structural typing rules binding domain active before scope).formation.formula))
  rw [logicalEq, formationEq]
  exact ⟨joined⟩

#print axioms ContextualReading.bind_projection_admitted
theorem ContextualReading.bind_assumptions_admitted (reading : ContextualReading abbreviation profile environment rho names)
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
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList) :
    (reading.bind distinct structural typing rules binding domain active before scope).AssumptionsAdmitted ruleAt bindingAt := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let root := Layout.names initial (layout.workDepth frame)
  let nextNames : Names (domain :: target) := BinderNames.cons root names
  let shift : Rename Unit target (domain :: target) := fun index => Var.vs index
  let next := reading.bind distinct structural typing rules binding domain active before scope
  let liftedRho : Rename Unit gamma (domain :: target) := fun index => Var.vs (rho index)
  have weakenEq (formula : Formula Symbol target) : HOL.weaken (σ := domain) formula = Mettapedia.Logic.HOL.rename shift formula := by
    exact rename_ext (fun {_} index => rfl) formula
  have rootEq : root = 7 + layout.workDepth frame := rfl
  have within : layout.workDepth frame ≤ layout.limit := layout.workDepth_mono (Nat.le_of_lt active)
  have related : NamesRel root shift names nextNames := NamesRel.weaken names domain root (Nat.le_refl _)
  have formBound : Preterm.VarsBelow root environment.scope.formation := by
    rw [rootEq]
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.formation_varsBelow (layout.workDepth frame) (by omega)
  have logicBound : Preterm.VarsBelow root environment.scope.logical := by
    rw [rootEq]
    simpa only [HOLKernelSetOperationInterpretation.initialContext_length] using
      environment.logical_varsBelow (layout.workDepth frame) before
  have formRead := logical_judgment_rename profile HOLKernelSetOperationReadback.readConstant 7 root
    names nextNames shift related (expandEquivalence signature.symbol abbreviation.reference environment.scope.formation)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root environment.scope.formation formBound)
  rw [reading.formation_read] at formRead
  have logicRead := logical_judgment_rename profile HOLKernelSetOperationReadback.readConstant 7 root
    names nextNames shift related (expandEquivalence signature.symbol abbreviation.reference environment.scope.logical)
    (expandEquivalence_varsBelow signature.symbol abbreviation.reference root environment.scope.logical logicBound)
  rw [reading.logical_read] at logicRead
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  obtain ⟨movedProjection⟩ := weaken_frame_admitted ruleAt bindingAt projectionTree
    (layout.workDepth frame) within bounded.projection domain root (by rfl)
  have projectionInFrame : AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt projectionFuel nextNames environment.scope.projection.val
      (.imp (reading.logical.rename shift).formula (reading.formation.rename shift).formula) := by
    rw [weakenEq] at movedProjection
    simpa only [Judgment.rename_formula, Mettapedia.Logic.HOL.rename] using movedProjection
  have rootRead : HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7 nextNames
      (.var root) = some ⟨domain, Term.var .vz⟩ := by
    simp [HOLKernelLogicalFunctionReadback.reader, readTermWith, readVariable, nextNames]
  have assignmentEq : ∀ {type} (index : Var gamma type),
      environment.assignment index = .var (nextNames.nameOf (liftedRho index)) := by
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
    · exact sourceWindow offset (by omega) member
  have targetNames : ∀ offset < source.binderDepth,
      Layout.names initial (windows.workDepth + 1 + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · change 7 + (layout.workDepth frame + 1 + offset) = 7 + layout.workDepth frame at same
      omega
    · have upper := (scope.2 _ member).2
      change 7 + (layout.workDepth frame + 1 + offset) < 7 + layout.workDepth frame at upper
      omega
  have temporaryNames : ∀ offset < source.binderDepth,
      Layout.names initial (windows.temporaryDepth + offset) ∉ nextNames.toList := by
    intro offset less member
    rcases List.mem_cons.mp member with same | member
    · change 7 + (layout.temporaryDepth frame + offset) = 7 + layout.workDepth frame at same
      simp only [Layout.temporaryDepth] at same
      omega
    · have upper := (scope.2 _ member).2
      change 7 + (layout.temporaryDepth frame + offset) < 7 + layout.workDepth frame at upper
      simp only [Layout.temporaryDepth] at upper
      omega
  obtain ⟨premiseFuel, ⟨oldPremise⟩⟩ := admitted position
  obtain ⟨premiseTree⟩ := weaken_frame_admitted ruleAt bindingAt oldPremise
    (layout.workDepth frame) within (bounded.assumptionProof position) domain root (by rfl)
  have premiseInFrame : AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt premiseFuel nextNames (environment.assumptionProof position).val
      (.imp (reading.logical.rename shift).formula (HOL.rename liftedRho source)) := by
    have shape : HOL.weaken (σ := domain) (.imp reading.logical.formula (HOL.rename rho source)) =
        Term.imp (reading.logical.rename shift).formula (HOL.rename liftedRho source) := by
      rw [Judgment.rename_formula]
      simp only [HOL.weaken, HOL.rename, rename_comp]
      rfl
    rw [shape] at premiseTree
    exact premiseTree
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
    environment.constantTyping (environment.assumptionProof position) liftedRho nextNames next.names_distinct
    next.names_above assignmentEq sourceNames targetNames temporaryNames
    (reading.logical.rename shift) (reading.formation.rename shift) logicRead formRead (Term.var .vz) rootRead
    ruleAt bindingAt selected structuralSelected bindingSelected projectionInFrame premiseInFrame
  have same : (weakenHyps (σ := domain) assumptions).get occurrence = HOL.weaken (σ := domain) (assumptions.get position) := by
    change (assumptions.map (HOL.weaken (σ := domain)))[occurrence.val] = _
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
    (.imp next.logical.formula (HOL.rename (Rename.lift rho) ((weakenHyps (σ := domain) assumptions).get occurrence))))
  rw [HOLKernelStructuralRules.CheckedProof.val_mpr claim same lifted, same]
  have logicalEq : next.logical.formula = .and (reading.logical.rename shift).formula .top := rfl
  rw [logicalEq]
  let receipt : ProofWitness := lifted.val
  change ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (layout.target initial signature.ids.object)
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
    7 ruleAt bindingAt fuel nextNames receipt
    (.imp (.and (reading.logical.rename shift).formula .top) (HOL.rename (Rename.lift rho) (HOL.weaken (σ := domain) (assumptions.get position)))))
  have renamedSource : HOL.rename (Rename.lift rho) (HOL.weaken (σ := domain) source) = HOL.rename liftedRho source := by
    simp only [HOL.weaken, rename_comp]
    exact rename_ext (by intro type index; rfl) source
  rw [renamedSource]
  exact ⟨fuel, ⟨liftedTree⟩⟩


#print axioms ContextualReading.bind_assumptions_admitted
/-- A temporary argument frame fits below the next work bank and remains outside
all names in the unchanged source binder window. -/
theorem argument_frame_scope (layout : Layout) (sourceDepth frame : Nat)
    {gamma : Ctx Unit} (names : Names gamma) (domain : Ty Unit)
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceBefore : sourceDepth + layout.width ≤ layout.workDepth frame)
    (sourceFresh : ∀ offset < layout.width, 7 + (sourceDepth + offset) ∉ names.toList) :
    let extended := BinderNames.cons (type := domain) (7 + layout.temporaryDepth frame) names
    InScope 7 extended (layout.workDepth (frame + 1)) ∧
      (∀ offset < layout.width, 7 + (sourceDepth + offset) ∉ extended.toList) ∧
      NamesRel (7 + layout.workDepth frame) (Rename.weaken (σ := domain)) names extended := by
  dsimp only
  have later : layout.workDepth frame ≤ layout.temporaryDepth frame := by
    simp only [Layout.temporaryDepth]
    omega
  have next : layout.temporaryDepth frame < layout.workDepth (frame + 1) := by
    rw [layout.next_workDepth]
    omega
  have absent : 7 + layout.temporaryDepth frame ∉ names.toList := by
    intro member
    have upper := (scope.2 _ member).2
    omega
  refine ⟨⟨List.nodup_cons.mpr ⟨absent, scope.1⟩, ?_⟩, ?_, ?_⟩
  · intro name member
    rcases List.mem_cons.mp member with rfl | old
    · constructor <;> omega
    · have bound := scope.2 name old
      constructor <;> omega
  · intro offset less member
    rcases List.mem_cons.mp member with same | old
    · omega
    · exact sourceFresh offset less old
  · exact NamesRel.weaken names domain (7 + layout.temporaryDepth frame) (by omega)

#print axioms argument_frame_scope

end Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
