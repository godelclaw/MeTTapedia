import Mettapedia.Languages.MM0.HOLKernelSourceInstantiation
import Mettapedia.Languages.MM0.Kernel.ContextExtension

/-!
# Allocated native contexts for source HOL beta receipts

An admitted native context is extended with three finite bound-name windows.
The source encoding, working encoding and auxiliary alpha encoding use those
windows in order. Existing typing and proof witnesses transport unchanged.
The resulting beta proof has exact source endpoints in the allocated source
window; callers supply no window, freshness or argument-readback witnesses.

This constructs one source inference rule. Complete proof-context allocation,
the other retained proof constructors and native byte refinement are separate.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelFreshInstantiation
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed)
open HOLKernelInferenceRules (equality)
open HOLKernelTypeSupport
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

def binderFamily (context : Context) (offset : Nat) : Nat := context.length + offset

def windowWidth {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result) : Nat :=
  body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1

def nativeContext (context : Context) (object : Nat) {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result) : Context :=
  context.appendBounds object (3 * windowWidth argument body)

theorem nativeContext_wellFormed (signature : Signature sorts terms)
    (formed : Context.WellFormed sorts context) {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result) :
    Context.WellFormed sorts (nativeContext context signature.ids.object argument body) :=
  Context.appendBounds_wellFormed formed signature.objectDeclared rfl _

def canonicalBeta (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (formed : Context.WellFormed sorts context)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := nativeContext context signature.ids.object argument body) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base result)
          (encodeWithAssignment signature.symbol base constant (binderFamily context) assignment 0 (.app (.lam body) argument))
          (encodeWithAssignment signature.symbol base constant (binderFamily context) assignment 0 (instantiate argument body))))) := by
  let width := windowWidth argument body
  let extra : Context := List.replicate (3 * width) (.bound signature.ids.object)
  let target := nativeContext context signature.ids.object argument body
  have widthPositive : 0 < width := by dsimp [width, windowWidth]; omega
  have imageHeight : argument.binderDepth < width := by
    have bounded : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) :=
      Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
    dsimp [width, windowWidth]
    omega
  have familyInjective : Function.Injective (binderFamily context) := by
    intro first second same
    dsimp [binderFamily] at same
    omega
  have allSlots (offset : Nat) (smaller : offset < 3 * width) :
      target[binderFamily context offset]? = some (.bound signature.ids.object) :=
    Context.appendBounds_lookup context signature.ids.object (3 * width) offset smaller
  have baseFresh : ∀ offset index, ¬ Preterm.HasVar target (binderFamily context offset) (base index) :=
    fun offset index => (baseSorted index).independent_appendedBound formed signature.ids.object (3 * width) offset
  have constantFresh : ∀ offset {type} (symbol : Const type),
      ¬ Preterm.HasVar target (binderFamily context offset) (constant symbol) := by
    intro offset type symbol
    exact (constantSorted symbol).independent_appendedBound formed signature.ids.object (3 * width) offset
  have assignmentFresh : ∀ offset {type} (index : Var gamma type),
      ¬ Preterm.HasVar target (binderFamily context offset) (assignment index) := by
    intro offset type index
    exact (assignmentSorted index).independent_appendedBound formed signature.ids.object (3 * width) offset
  have fresh (offset : Nat) : ¬ Preterm.HasVar target (binderFamily context offset) antecedent :=
    antecedentSorted.independent_appendedBound formed signature.ids.object (3 * width) offset
  have extendedBase : ∀ index, Preterm.HasType terms target (base index) [] signature.ids.type :=
    fun index => (baseSorted index).weakenContext extra
  have extendedConstant : ∀ {type} (symbol : Const type),
      Preterm.HasType terms target (constant symbol) [] signature.ids.object := by
    intro type symbol
    exact (constantSorted symbol).weakenContext extra
  have extendedAssignment : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms target (assignment index) [] signature.ids.object := by
    intro type index
    exact (assignmentSorted index).weakenContext extra
  have extendedVariables : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := target) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)) := by
    intro type index
    exact ⟨(variableTyping index).val, (variableTyping index).property.weakenContext extra⟩
  have extendedConstants : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := target) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)) := by
    intro type symbol
    exact ⟨(constantTyping symbol).val, (constantTyping symbol).property.weakenContext extra⟩
  let argumentCode := encodeWithAssignment signature.symbol base constant (binderFamily context) assignment 0 argument
  have argumentIndependent (observer : Nat) (beyond : argument.binderDepth ≤ observer) :
      ¬ Preterm.HasVar target (binderFamily context observer) argumentCode := by
    apply encode_independent target (binderFamily context observer) signature.symbol base constant (binderFamily context)
      (baseFresh observer) (constantFresh observer) argument assignment 0 (assignmentFresh observer)
    intro offset smaller
    apply boundVariable_independent target (binderFamily context observer)
      (binderFamily context (0 + offset)) signature.ids.object
    · exact allSlots _ (by omega)
    · dsimp [binderFamily]
      omega
  have root : target[binderFamily context width]? = some (.bound signature.ids.object) := allSlots width (by omega)
  have equationIndependent (observer : Nat) (apart : observer ≠ width)
      (beyond : argument.binderDepth ≤ observer) :
      ¬ Preterm.HasVar target (binderFamily context observer)
        (conjunction signature.symbol antecedent (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binderFamily context width)) argumentCode))) := by
    apply substitutionContext_independent target (binderFamily context observer) (binderFamily context width)
      signature.symbol antecedent _ argumentCode
    · exact fresh observer
    · exact encodeType_independent target _ signature.symbol base (baseFresh observer) domain
    · exact boundVariable_independent target _ _ signature.ids.object root (by dsimp [binderFamily]; omega)
    · exact argumentIndependent observer beyond
  exact HOLKernelSourceInstantiation.canonicalBeta signature profile structural typing rules binding
    base constant (binderFamily context) (binderFamily context) extendedBase extendedConstant
    familyInjective familyInjective baseFresh baseFresh argument body assignment 0 width (2 * width)
    antecedent (antecedentSorted.weakenContext extra) extendedAssignment
    (by intro offset smaller; exact allSlots (0 + offset) (by change offset < width at smaller; omega))
    (by intro offset smaller; exact allSlots (width + offset) (by change offset < width at smaller; omega))
    (by intro offset smaller; exact allSlots (2 * width + offset) (by change offset < width at smaller; omega))
    (fun offset _ => fresh (0 + offset)) (fun offset _ => fresh (width + offset))
    (fun offset _ => fresh (2 * width + offset))
    (by intro first firstSmaller second secondSmaller; change first < width at firstSmaller
        change second < width at secondSmaller; dsimp [binderFamily]; omega)
    (by intro first firstSmaller second secondSmaller; change first < width at firstSmaller
        change second < width at secondSmaller; dsimp [binderFamily]; omega)
    (by intro offset smaller; apply equationIndependent <;> omega)
    (by intro offset smaller; apply equationIndependent <;> omega)
    extendedVariables extendedConstants

#print axioms nativeContext_wellFormed
#print axioms canonicalBeta
end Mettapedia.Languages.MM0.HOLKernelFreshInstantiation
