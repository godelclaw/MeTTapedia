import Mettapedia.Languages.MM0.HOLKernelProofAllocation
import Mettapedia.Languages.MM0.HOLKernelSourceBinding
import Mettapedia.Languages.MM0.HOLKernelAssumptions

/-!
# Contextual environments for retained HOL proof compilation

The source assignment, native term typings, formation/logical projection and
ordered assumption proofs share one fixed allocated native context. Formation
and variable images are independent from the source depth onward. Logical
assumptions may use names in the source bank and are independent beyond it.

These local invariants construct the term and binder interfaces used by a
proof fold. The environment contains no whole-proof compilation assertion.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofEnvironment
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed)
open HOLKernelStructuralRules (CheckedProof)
open HOLKernelProofAllocation
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {hypotheses : List Preterm}

abbrev NativeContext (signature : Signature sorts terms) (layout : Layout) (initial : Context) : Context :=
  layout.target initial signature.ids.object

structure Encoding (signature : Signature sorts terms) (layout : Layout) (initial : Context)
    (Base : Type u) (Const : Ty Base → Type v) where
  base : Base → Preterm
  constant : ∀ {type}, Const type → Preterm
  baseSorted : ∀ index, Preterm.HasType terms (NativeContext signature layout initial) (base index) [] signature.ids.type
  constantSorted : ∀ {type} (symbol : Const type),
    Preterm.HasType terms (NativeContext signature layout initial) (constant symbol) [] signature.ids.object
  baseIndependent : ∀ offset index,
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset) (base index)
  constantIndependent : ∀ offset {type} (symbol : Const type),
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset) (constant symbol)

def Encoding.fromInitial (signature : Signature sorts terms) (layout : Layout) (initial : Context)
    (formed : Context.WellFormed sorts initial) (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseSorted : ∀ index, Preterm.HasType terms initial (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms initial (constant symbol) [] signature.ids.object) :
    Encoding signature layout initial Base Const where
  base := base
  constant := constant
  baseSorted := fun index => (baseSorted index).weakenContext (List.replicate layout.limit (.bound signature.ids.object))
  constantSorted := by intro type symbol; exact (constantSorted symbol).weakenContext (List.replicate layout.limit (.bound signature.ids.object))
  baseIndependent := fun offset index => layout.old_expression_independent (baseSorted index) formed signature.ids.object offset
  constantIndependent := by intro offset type symbol; exact layout.old_expression_independent (constantSorted symbol) formed signature.ids.object offset

structure Environment {signature : Signature sorts terms} {layout : Layout} {initial : Context}
    (encoding : Encoding signature layout initial Base Const) (gamma : Ctx Base)
    (assumptions : List (Formula Const gamma)) (sourceDepth : Nat) where
  assignment : Assignment gamma
  assignmentSorted : ∀ {type} (index : Var gamma type),
    Preterm.HasType terms (NativeContext signature layout initial) (assignment index) [] signature.ids.object
  scope : HOLKernelStructuralRules.ProofContext terms definitions theorems (NativeContext signature layout initial)
    hypotheses signature.symbol signature.ids.wff
  variableTyping : ∀ {type} (index : Var gamma type),
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol encoding.base type))
  constantTyping : ∀ {type} (symbol : Const type),
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (typed signature.symbol scope.formation (encoding.constant symbol) (encodeType signature.symbol encoding.base type))
  assignmentIndependent : ∀ offset, sourceDepth ≤ offset → ∀ {type} (index : Var gamma type),
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset) (assignment index)
  formationIndependent : ∀ offset, sourceDepth ≤ offset →
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset) scope.formation
  logicalIndependent : ∀ offset, sourceDepth + layout.width ≤ offset →
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset) scope.logical
  assumptionBounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width
  assumptionProof : ∀ occurrence : Fin assumptions.length,
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
          assignment sourceDepth (assumptions.get occurrence))))

namespace Environment
variable {signature : Signature sorts terms} {layout : Layout} {initial : Context}
variable {encoding : Encoding signature layout initial Base Const} {gamma : Ctx Base}
variable {assumptions : List (Formula Const gamma)} {sourceDepth : Nat}

def encode (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth) {type : Ty Base} (source : Term Const gamma type) : Preterm :=
  encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial) environment.assignment sourceDepth source

theorem encoded_sorted (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth) {type : Ty Base} (source : Term Const gamma type)
    (fits : source.binderDepth ≤ layout.width) {frame : Nat} (active : frame < layout.frames)
    (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    Preterm.HasType terms (NativeContext signature layout initial) (environment.encode source) [] signature.ids.object :=
  encode_sorted signature _ encoding.base encoding.constant (Layout.names initial) encoding.baseSorted encoding.constantSorted
    source environment.assignment sourceDepth environment.assignmentSorted
    (fun offset smaller => layout.sourceSlots initial signature.ids.object active before offset (Nat.lt_of_lt_of_le smaller fits))

theorem encoded_independent (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth) {type : Ty Base} (source : Term Const gamma type)
    (fits : source.binderDepth ≤ layout.width) {frame : Nat} (active : frame < layout.frames)
    (before : sourceDepth + layout.width ≤ layout.workDepth frame) (offset : Nat)
    (later : sourceDepth + layout.width ≤ offset) :
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset) (environment.encode source) := by
  apply encode_independent _ (Layout.names initial offset) signature.symbol encoding.base encoding.constant (Layout.names initial)
    (encoding.baseIndependent offset) (encoding.constantIndependent offset) source environment.assignment sourceDepth
    (environment.assignmentIndependent offset (by omega))
  intro used smaller
  apply HOLKernelTypeSupport.boundVariable_independent _ _ _ signature.ids.object
    (layout.sourceSlots initial signature.ids.object active before used (Nat.lt_of_lt_of_le smaller fits))
  intro same
  have equal := Layout.names_injective initial same
  omega

def typedInFormation (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    {type : Ty Base} (source : Term Const gamma type) (fits : source.binderDepth ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (typed signature.symbol environment.scope.formation (environment.encode source) (encodeType signature.symbol encoding.base type)) :=
  HOLKernelTermTyping.compileWithAssignment signature structural typing encoding.base encoding.constant (Layout.names initial)
    encoding.baseSorted encoding.constantSorted (Layout.names_injective initial) encoding.baseIndependent source environment.assignment
    sourceDepth environment.scope.formation environment.scope.formationSorted environment.assignmentSorted
    (fun offset smaller => layout.sourceSlots initial signature.ids.object active before offset (Nat.lt_of_lt_of_le smaller fits))
    (fun offset _ => environment.formationIndependent (sourceDepth + offset) (by omega))
    environment.variableTyping environment.constantTyping

def typed (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    {type : Ty Base} (source : Term Const gamma type) (fits : source.binderDepth ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (HOLKernelTypingRules.typed signature.symbol environment.scope.logical (environment.encode source) (encodeType signature.symbol encoding.base type)) :=
  environment.scope.promote signature structural _
    (hasType_sorted signature _ (environment.encoded_sorted source fits active before)
      (encodeType_sorted signature _ encoding.base encoding.baseSorted type))
    (environment.typedInFormation structural typing source fits active before)

def windows (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth) {frame : Nat} (active : frame < layout.frames)
    (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    HOLKernelSourceBinding.RebindingWindows (NativeContext signature layout initial) signature.ids.object
      environment.scope.formation (Layout.names initial) (Layout.names initial) where
  width := layout.width
  sourceDepth := sourceDepth
  workDepth := layout.workDepth frame
  temporaryDepth := layout.temporaryDepth frame
  sourceSlots := layout.sourceSlots initial signature.ids.object active before
  workSlots := fun offset smaller => layout.workSlots initial signature.ids.object active offset (by omega)
  temporarySlots := fun offset smaller => layout.temporarySlots initial signature.ids.object active offset (by omega)
  sourceFresh := fun offset _ => environment.formationIndependent _ (by omega)
  workFresh := fun offset _ => environment.formationIndependent _ (by omega)
  temporaryFresh := by
    intro offset smaller
    apply environment.formationIndependent
    simp only [Layout.temporaryDepth]
    omega
  sourceDisjoint := by
    intro first firstSmall second secondSmall same
    exact layout.source_before_temporary before firstSmall (Layout.names_injective initial same)
  workDisjoint := by
    intro first firstSmall second secondSmall same
    exact layout.work_temporary_apart frame (by omega) (Layout.names_injective initial same)
private theorem holdsIndependent (observer : Nat) (value : Preterm)
    (independent : ¬ Preterm.HasVar (NativeContext signature layout initial) observer value) :
    ¬ Preterm.HasVar (NativeContext signature layout initial) observer (holds signature.symbol value) := by
  apply HOLKernelTypeSupport.applySymbol_independent _ observer signature.symbol .thm [value]
  intro expression member
  have same : expression = value := by simpa using member
  simpa only [same] using independent

private theorem conjunctionIndependent (observer : Nat) (first second : Preterm)
    (firstIndependent : ¬ Preterm.HasVar (NativeContext signature layout initial) observer first)
    (secondIndependent : ¬ Preterm.HasVar (NativeContext signature layout initial) observer second) :
    ¬ Preterm.HasVar (NativeContext signature layout initial) observer (conjunction signature.symbol first second) := by
  apply HOLKernelTypeSupport.applySymbol_independent _ observer signature.symbol .an [first, second]
  intro expression member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

private theorem antecedentIndependent (observer : Nat) (formation : Preterm)
    (independent : ¬ Preterm.HasVar (NativeContext signature layout initial) observer formation) :
    ∀ (assumptions : List Preterm),
      (∀ value ∈ assumptions, ¬ Preterm.HasVar (NativeContext signature layout initial) observer value) →
      ¬ Preterm.HasVar (NativeContext signature layout initial) observer
        (HOLKernelAssumptions.antecedent signature.symbol formation assumptions)
  | [], _ => independent
  | first :: rest, each => conjunctionIndependent observer _ _
      (antecedentIndependent observer formation independent rest
        (fun value member => each value (List.mem_cons_of_mem _ member)))
      (each first List.mem_cons_self)

def assume (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (formula : Formula Const gamma) (fits : formula.binderDepth < layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma (formula :: assumptions) sourceDepth := by
  let extra := holds signature.symbol (environment.encode formula)
  have extraSorted := holds_sorted signature _ (environment.encoded_sorted formula (Nat.le_of_lt fits) active before)
  refine {
    assignment := environment.assignment
    assignmentSorted := environment.assignmentSorted
    scope := environment.scope.under signature structural extra extraSorted
    variableTyping := environment.variableTyping
    constantTyping := environment.constantTyping
    assignmentIndependent := environment.assignmentIndependent
    formationIndependent := environment.formationIndependent
    logicalIndependent := ?_
    assumptionBounds := ?_
    assumptionProof := ?_ }
  · intro offset later
    exact conjunctionIndependent _ _ _ (environment.logicalIndependent offset later)
      (holdsIndependent _ _ (environment.encoded_independent formula (Nat.le_of_lt fits) active before offset later))
  · intro source member
    rcases List.mem_cons.mp member with rfl | member
    · exact fits
    · exact environment.assumptionBounds source member
  · intro occurrence
    rcases occurrence with ⟨index, smaller⟩
    cases index with
    | zero => exact HOLKernelStructuralRules.right signature structural environment.scope.logical extra environment.scope.logicalSorted extraSorted
    | succ index =>
        let position : Fin assumptions.length := ⟨index, by simpa using smaller⟩
        exact HOLKernelStructuralRules.weaken signature structural environment.scope.logical extra _ environment.scope.logicalSorted extraSorted
          (holds_sorted signature _ (environment.encoded_sorted (assumptions.get position)
            (Nat.le_of_lt (environment.assumptionBounds _ (List.get_mem _ _))) active before)) (environment.assumptionProof position)

def bind (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
    encoding gamma assumptions sourceDepth)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (domain : Ty Base) {frame : Nat} (active : frame < layout.frames)
    (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding (domain :: gamma) (weakenHyps (σ := domain) assumptions) (layout.workDepth frame + 1) := by
  let root := Layout.names initial (layout.workDepth frame)
  have rootBound : (NativeContext signature layout initial)[root]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using layout.workSlots initial signature.ids.object active 0 (by omega)
  have rootSorted : Preterm.HasType terms (NativeContext signature layout initial) (.var root) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) rootBound
  have domainSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted domain
  let extra := hasType signature.symbol (.var root) (encodeType signature.symbol encoding.base domain)
  have extraSorted := hasType_sorted signature _ rootSorted domainSorted
  let scope := environment.scope.extend signature structural extra extraSorted
  let assignment : Assignment (domain :: gamma) := Assignment.extend (.var root) environment.assignment
  have independentRoot (offset : Nat) (later : layout.workDepth frame + 1 ≤ offset) : Layout.names initial offset ≠ root := by
    intro same
    have equal := Layout.names_injective initial same
    omega
  refine {
    assignment := assignment
    assignmentSorted := Assignment.extend_sorted signature _ _ environment.assignment rootSorted environment.assignmentSorted
    scope := scope
    variableTyping := ?_
    constantTyping := HOLKernelTermTyping.weakenConstants signature structural encoding.base encoding.constant
      environment.scope.formation extra environment.scope.formationSorted extraSorted encoding.baseSorted encoding.constantSorted environment.constantTyping
    assignmentIndependent := ?_
    formationIndependent := ?_
    logicalIndependent := ?_
    assumptionBounds := ?_
    assumptionProof := ?_ }
  · intro type index
    cases index with
    | vz => exact HOLKernelStructuralRules.right signature structural environment.scope.formation extra environment.scope.formationSorted extraSorted
    | vs index =>
        exact (HOLKernelTermTyping.weakenVariables signature structural encoding.base environment.assignment
          environment.scope.formation extra environment.scope.formationSorted extraSorted encoding.baseSorted environment.assignmentSorted environment.variableTyping) index
  · intro offset later type index
    cases index with
    | vz => exact HOLKernelTypeSupport.boundVariable_independent _ _ _ signature.ids.object rootBound (independentRoot offset later)
    | vs index => exact environment.assignmentIndependent offset (by omega) index
  · intro offset later
    exact HOLKernelTypeSupport.contextExtension_independent _ _ root signature.ids.object signature.symbol _ _ rootBound
      (independentRoot offset later) (environment.formationIndependent offset (by omega))
      (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent offset) domain)
  · intro offset later
    exact HOLKernelTypeSupport.contextExtension_independent _ _ root signature.ids.object signature.symbol _ _ rootBound
      (independentRoot offset (by omega)) (environment.logicalIndependent offset (by omega))
      (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent offset) domain)
  · intro formula member
    have mapped : formula ∈ assumptions.map (weaken (σ := domain)) := member
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp mapped
    subst formula
    simpa only [weaken, Term.binderDepth_rename] using environment.assumptionBounds old oldMember
  · intro occurrence
    let position : Fin assumptions.length := ⟨occurrence.val, by simpa [weakenHyps] using occurrence.isLt⟩
    have same : (weakenHyps (σ := domain) assumptions).get occurrence = weaken (σ := domain) (assumptions.get position) := by
      change (assumptions.map (weaken (σ := domain)))[occurrence.val] = _
      simp only [List.getElem_map]
      rfl
    rw [same]
    exact HOLKernelSourceBinding.weakenAssumption signature abbreviation profile structural typing rules binding
      encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
      (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
      (assumptions.get position) environment.assignment environment.scope (environment.windows active before)
      (by change (assumptions.get position).binderDepth + 1 ≤ layout.width
          have bound := environment.assumptionBounds _ (List.get_mem assumptions position); omega)
      environment.assignmentSorted environment.variableTyping environment.constantTyping (environment.assumptionProof position)

def fromInitial (signature : Signature sorts terms) (layout : Layout) (initial : Context)
    (formed : Context.WellFormed sorts initial)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseSorted : ∀ index, Preterm.HasType terms initial (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms initial (constant symbol) [] signature.ids.object)
    (gamma : Ctx Base) (assignment : Assignment gamma)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms initial (assignment index) [] signature.ids.object)
    (formation : Preterm) (formationSorted : Preterm.HasType terms initial formation [] signature.ids.wff)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := initial) (hypotheses := hypotheses)
        (HOLKernelTypingRules.typed signature.symbol formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := initial) (hypotheses := hypotheses)
        (HOLKernelTypingRules.typed signature.symbol formation (constant symbol) (encodeType signature.symbol base type)))
    (assumptions : List (Formula Const gamma)) (bounds : ∀ formula ∈ assumptions, formula.binderDepth < layout.width) :
    Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      (Encoding.fromInitial signature layout initial formed base constant baseSorted constantSorted) gamma assumptions 0 := by
  let encoding : Encoding signature layout initial Base Const :=
    Encoding.fromInitial signature layout initial formed base constant baseSorted constantSorted
  let extra : Context := List.replicate layout.limit (.bound signature.ids.object)
  have fixedFormation := formationSorted.weakenContext extra
  have fixedAssignment : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms (NativeContext signature layout initial) (assignment index) [] signature.ids.object :=
    fun {_} index => (assignmentSorted index).weakenContext extra
  let nativeAssumptions := assumptions.map (fun formula => holds signature.symbol
    (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial) assignment 0 formula))
  have sorted : ∀ value ∈ nativeAssumptions, Preterm.HasType terms (NativeContext signature layout initial) value [] signature.ids.wff := by
    intro value member
    have mapped : value ∈ assumptions.map (fun formula => holds signature.symbol
      (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial) assignment 0 formula)) := member
    obtain ⟨formula, sourceMember, rfl⟩ := List.mem_map.mp mapped
    exact holds_sorted signature _ (encode_sorted signature _ encoding.base encoding.constant (Layout.names initial)
      encoding.baseSorted encoding.constantSorted formula assignment 0 fixedAssignment
      (by intro offset smaller; apply layout.slot; apply layout.source_slot_lt
          simpa only [Nat.zero_add] using Nat.lt_trans smaller (bounds formula sourceMember)))
  let scope := HOLKernelAssumptions.proofContext (definitions := definitions) (hypotheses := hypotheses)
    signature structural formation fixedFormation nativeAssumptions sorted
  refine {
    assignment := assignment
    assignmentSorted := fixedAssignment
    scope := scope
    variableTyping := ?_
    constantTyping := ?_
    assignmentIndependent := ?_
    formationIndependent := ?_
    logicalIndependent := ?_
    assumptionBounds := bounds
    assumptionProof := ?_ }
  · intro type index
    exact ⟨(variableTyping index).val, (variableTyping index).property.weakenContext extra⟩
  · intro type symbol
    exact ⟨(constantTyping symbol).val, (constantTyping symbol).property.weakenContext extra⟩
  · intro offset _ type index
    exact layout.old_expression_independent (assignmentSorted index) formed signature.ids.object offset
  · intro offset _
    exact layout.old_expression_independent formationSorted formed signature.ids.object offset
  · intro offset later
    apply antecedentIndependent (Layout.names initial offset) formation
      (layout.old_expression_independent formationSorted formed signature.ids.object offset) nativeAssumptions
    intro value member
    have mapped : value ∈ assumptions.map (fun formula => holds signature.symbol
      (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial) assignment 0 formula)) := member
    obtain ⟨formula, sourceMember, rfl⟩ := List.mem_map.mp mapped
    apply holdsIndependent
    apply encode_independent _ (Layout.names initial offset) signature.symbol encoding.base encoding.constant (Layout.names initial)
      (encoding.baseIndependent offset) (encoding.constantIndependent offset) formula assignment 0
      (fun {_} index => layout.old_expression_independent (assignmentSorted index) formed signature.ids.object offset)
    intro used smaller
    apply HOLKernelTypeSupport.boundVariable_independent _ _ _ signature.ids.object
      (layout.slot initial signature.ids.object (0 + used) (layout.source_slot_lt (by have bound := bounds formula sourceMember; omega)))
    intro same
    have equal := Layout.names_injective initial same
    have bound := bounds formula sourceMember
    omega
  · intro occurrence
    let position : Fin nativeAssumptions.length := ⟨occurrence.val, by simp [nativeAssumptions]⟩
    have same : nativeAssumptions.get position = holds signature.symbol
        (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial) assignment 0 (assumptions.get occurrence)) := by
      change (assumptions.map _)[position.val] = _
      simp only [List.getElem_map]
      rfl
    have proof := HOLKernelAssumptions.hypothesis (definitions := definitions) (hypotheses := hypotheses)
      signature structural formation fixedFormation nativeAssumptions sorted position
    change CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol (HOLKernelAssumptions.antecedent signature.symbol formation nativeAssumptions)
        (holds signature.symbol (encodeWithAssignment signature.symbol encoding.base encoding.constant
          (Layout.names initial) assignment 0 (assumptions.get occurrence))))
    rw [← same]
    exact proof

end Environment

#print axioms Encoding.fromInitial
#print axioms Environment.encoded_independent
#print axioms Environment.typedInFormation
#print axioms Environment.typed
#print axioms Environment.windows
#print axioms Environment.assume
#print axioms Environment.bind
#print axioms Environment.fromInitial
end Mettapedia.Languages.MM0.HOLKernelProofEnvironment
