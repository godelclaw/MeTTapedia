import Mettapedia.Languages.MM0.HOLKernelTypingProofs
import Mettapedia.Languages.MM0.HOLKernelTypeSupport
import Mettapedia.Languages.MM0.HOLKernelTermAssignments

/-!
# Constructive HOL term typing in the maintained MM0 kernel theory

The assignment compiler covers every intrinsic HOL term constructor with
native preterms at its variable leaves. The position compiler specializes
that construction through the proved encoding comparison. Inputs retain
typing proofs for the free variables and declared constants, exact native
sorting, and fresh bound slots. A binding case extends the logical context,
weakens the existing variable and constant proofs, and uses the maintained
abstraction or quantifier typing theorem. No typing proof for a compound
source term is supplied as an assumption.

The finite slot bound is the source's object-binder depth. Complete occurrence
independence of the logical context is required only in that finite window.
Base-type code independence is retained separately. It is separate from ordinary native sorting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelTermTyping

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTypingRules HOLKernelTypingProofs
open HOLKernelStructuralRules (CheckedProof)
open HOLKernelTypeSupport HOLKernelTermAssignments

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

def weakenVariables (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (base : Base → Preterm) {gamma : Ctx Base} (assignment : Assignment gamma)
    (antecedent extra : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (proofs : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type))) :
    ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol (conjunction signature.symbol antecedent extra)
          (assignment index) (encodeType signature.symbol base type)) := by
  intro type index
  exact HOLKernelStructuralRules.weaken signature structural antecedent extra _
    antecedentSorted extraSorted (hasType_sorted signature context (assignmentSorted index)
      (encodeType_sorted signature context base baseSorted type)) (proofs index)

def weakenConstants (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (antecedent extra : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (proofs : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) :
    ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol (conjunction signature.symbol antecedent extra)
          (constant symbol) (encodeType signature.symbol base type)) := by
  intro type symbol
  exact HOLKernelStructuralRules.weaken signature structural antecedent extra _
    antecedentSorted extraSorted (hasType_sorted signature context (constantSorted symbol)
      (encodeType_sorted signature context base baseSorted type)) (proofs symbol)

def compileWithAssignment (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (depth : Nat) (antecedent : Preterm),
      Preterm.HasType terms context antecedent [] signature.ids.wff →
      (∀ {type} (index : Var gamma type),
        Preterm.HasType terms context (assignment index) [] signature.ids.object) →
      (∀ offset < source.binderDepth,
        context[binders (depth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent) →
      (∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent ((assignment index)) (encodeType signature.symbol base type))) →
      (∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) →
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent
          (encodeWithAssignment signature.symbol base constant binders assignment depth source)
          (encodeType signature.symbol base type)) := by
  match source with
  | .var index =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      exact variableProof index
  | .const symbol =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      exact constantProof symbol
  | .top =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      exact truthTyping signature typing antecedent antecedentSorted
  | .bot =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      exact falsityTyping signature typing antecedent antecedentSorted
  | .app first second | .and first second | .or first second | .imp first second =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      have firstSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstSorted := encode_sorted signature context base constant binders baseSorted
        constantSorted first assignment depth assignmentSorted firstSlots
      have secondSorted := encode_sorted signature context base constant binders baseSorted
        constantSorted second assignment depth assignmentSorted secondSlots
      have firstProof := compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
          bindersInjective baseIndependent first assignment depth antecedent antecedentSorted assignmentSorted firstSlots firstIndependent variableProof constantProof
      have secondProof := compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
          bindersInjective baseIndependent second assignment depth antecedent antecedentSorted assignmentSorted secondSlots secondIndependent variableProof constantProof
      first
      | exact applicationTyping signature typing antecedent _ _ _ _ antecedentSorted
          (encodeType_sorted signature context base baseSorted _) (encodeType_sorted signature context base baseSorted _)
          firstSorted secondSorted firstProof secondProof
      | exact conjunctionTyping signature typing antecedent _ _ antecedentSorted firstSorted secondSorted firstProof secondProof
      | exact disjunctionTyping signature typing antecedent _ _ antecedentSorted firstSorted secondSorted firstProof secondProof
      | exact implicationTyping signature typing antecedent _ _ antecedentSorted firstSorted secondSorted firstProof secondProof
  | .not body =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      exact negationTyping signature typing antecedent _ antecedentSorted
        (encode_sorted signature context base constant binders baseSorted constantSorted body
          assignment depth assignmentSorted boundSlots)
        (compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
          bindersInjective baseIndependent body assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof)
  | .eq (τ := type) first second =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      have firstSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      exact equalityTyping signature typing (encodeType signature.symbol base type) antecedent _ _
        (encodeType_sorted signature context base baseSorted type) antecedentSorted
        (encode_sorted signature context base constant binders baseSorted constantSorted first
          assignment depth assignmentSorted firstSlots)
        (encode_sorted signature context base constant binders baseSorted constantSorted second
          assignment depth assignmentSorted secondSlots)
        (compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
          bindersInjective baseIndependent first assignment depth antecedent antecedentSorted assignmentSorted firstSlots firstIndependent variableProof constantProof)
        (compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
          bindersInjective baseIndependent second assignment depth antecedent antecedentSorted assignmentSorted secondSlots secondIndependent variableProof constantProof)
  | .lam (σ := domain) body | .all (σ := domain) body | .ex (σ := domain) body =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
      have head : context[binders depth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using boundSlots 0 (Nat.zero_lt_succ _)
      have bodySlots : ∀ offset < body.binderDepth,
          context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := boundSlots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have extendedAssignmentsSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (binders depth)) assignment index) [] signature.ids.object := by
        intro type index
        cases index with
        | vz => exact Preterm.HasType.var (binder := .bound signature.ids.object) head
        | vs index => exact assignmentSorted index
      have domainSorted := encodeType_sorted signature context base baseSorted domain
      have boundSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
        Preterm.HasType.var (binder := .bound signature.ids.object) head
      let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
      have extraSorted := hasType_sorted signature context boundSorted domainSorted
      let extended := conjunction signature.symbol antecedent extra
      have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
      have extendedIndependent : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
        · intro same
          have impossible := bindersInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
      have extendedVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol extended ((Assignment.extend (.var (binders depth)) assignment index))
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact HOLKernelStructuralRules.right signature structural _ _ antecedentSorted extraSorted
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent extra
              antecedentSorted extraSorted baseSorted assignmentSorted variableProof) index
      have extendedConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent extra
          antecedentSorted extraSorted baseSorted constantSorted constantProof
      have bodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body
        (Assignment.extend (.var (binders depth)) assignment) (depth + 1) extendedAssignmentsSorted bodySlots
      have bodyProof := compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
        bindersInjective baseIndependent body (Assignment.extend (.var (binders depth)) assignment) (depth + 1) extended
        extendedSorted extendedAssignmentsSorted bodySlots extendedIndependent extendedVariables extendedConstants
      have antecedentIndependent : ¬ Preterm.HasVar context (binders depth) antecedent := by
        simpa only [Nat.add_zero] using independent 0 (Nat.zero_lt_succ _)
      have domainIndependent := encodeType_independent context (binders depth) signature.symbol base
        (baseIndependent depth) domain
      first
      | exact abstractionTyping signature typing antecedent _ _ _ (binders depth) antecedentSorted
          domainSorted (encodeType_sorted signature context base baseSorted _) head bodySorted
          antecedentIndependent domainIndependent
          (encodeType_independent context (binders depth) signature.symbol base (baseIndependent depth) _) bodyProof
      | exact universalTyping signature typing _ antecedent _ (binders depth) domainSorted antecedentSorted
          head bodySorted domainIndependent antecedentIndependent bodyProof
      | exact existentialTyping signature typing _ antecedent _ (binders depth) domainSorted antecedentSorted
          head bodySorted domainIndependent antecedentIndependent bodyProof

termination_by structural source




def compile (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (positions : Positions gamma) (depth : Nat) (antecedent : Preterm),
      Preterm.HasType terms context antecedent [] signature.ids.wff →
      (∀ {type} (index : Var gamma type),
        (context[positions index]?).map Binder.sort = some signature.ids.object) →
      (∀ offset < source.binderDepth,
        context[binders (depth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent) →
      (∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (.var (positions index)) (encodeType signature.symbol base type))) →
      (∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) →
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent
          (encodeTerm signature.symbol base constant binders positions depth source)
          (encodeType signature.symbol base type)) := by
  intro positions depth antecedent antecedentSorted positionsSorted boundSlots independent variableProof constantProof
  have assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (.var (positions index)) [] signature.ids.object := by
    intro type index
    simpa only [encodeTerm] using
      (encodeTerm_sorted signature context base constant binders baseSorted constantSorted
        (.var index : Term Const gamma type) positions depth positionsSorted (by simp [Term.binderDepth]))
  let interpreted := compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
    bindersInjective baseIndependent source (fun index => .var (positions index)) depth antecedent
    antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
  simpa only [HOLKernelTermAssignments.encode_positions] using interpreted


def substitutionTyping (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma delta : Ctx Base} (substitution : Subst Const gamma delta)
    (assignment : Assignment delta) (depth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var delta type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < Subst.maxBinderDepth substitution,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < Subst.maxBinderDepth substitution,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (variableTyping : ∀ {type} (index : Var delta type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) :
    ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent
          (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
          (encodeType signature.symbol base type)) := by
  intro type index
  exact compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
    bindersInjective baseIndependent (substitution index) assignment depth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Subst.binderDepth_le_maxBinderDepth substitution index)))
    (fun offset smaller => fresh offset
      (Nat.lt_of_lt_of_le smaller (Subst.binderDepth_le_maxBinderDepth substitution index)))
    variableTyping constantTyping


#print axioms substitutionTyping
#print axioms weakenVariables
#print axioms weakenConstants
#print axioms compileWithAssignment
#print axioms compile

/-- Bounds every variable stored in the generated typing receipt, including
its binder cases and weakened variable/constant proof inputs. -/
theorem compileWithAssignment_varsBelow (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (depth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
      (boundSlots : ∀ offset < source.binderDepth, context[binders (depth + offset)]? = some (.bound signature.ids.object))
      (independent : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
      (variableProof : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
      (constantProof : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      (limit : Nat)
      (_ : ∀ index, Preterm.VarsBelow limit (base index))
      (_ : ∀ {type} (symbol : Const type), Preterm.VarsBelow limit (constant symbol))
      (_ : ∀ {type} (index : Var gamma type), Preterm.VarsBelow limit (assignment index))
      (_ : Preterm.VarsBelow limit antecedent)
      (_ : ∀ offset < source.binderDepth, binders (depth + offset) < limit)
      (_ : ∀ {type} (index : Var gamma type), (variableProof index).val.VarsBelow limit)
      (_ : ∀ {type} (symbol : Const type), (constantProof symbol).val.VarsBelow limit),
      (compileWithAssignment signature structural typing base constant binders baseSorted constantSorted
        bindersInjective baseIndependent source assignment depth antecedent antecedentSorted assignmentSorted
        boundSlots independent variableProof constantProof).val.VarsBelow limit := by
  induction source with
  | var index =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      exact variableProofBound index
  | const symbol =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      exact constantProofBound symbol
  | top =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      change ProofWitness.VarsBelow _ (.theoremApp _ [_] [])
      simpa only [ProofWitness.VarsBelow, List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
        using antecedentBound
  | bot =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      change ProofWitness.VarsBelow _ (.theoremApp _ [_] [])
      simpa only [ProofWitness.VarsBelow, List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
        using antecedentBound
  | app first second ihFirst ihSecond | and first second ihFirst ihSecond | or first second ihFirst ihSecond | imp first second ihFirst ihSecond | eq first second ihFirst ihSecond =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      have firstBound (offset : Nat) (smaller : offset < first.binderDepth) : binders (depth + offset) < limit :=
        bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have secondBound (offset : Nat) (smaller : offset < second.binderDepth) : binders (depth + offset) < limit :=
        bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have firstTerm := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound first assignment depth assignmentBound firstBound
      have secondTerm := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound second assignment depth assignmentBound secondBound
      have firstProof := ihFirst assignment depth antecedent antecedentSorted assignmentSorted
        (fun offset smaller => boundSlots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        variableProof constantProof limit baseBound constantBound assignmentBound antecedentBound firstBound variableProofBound constantProofBound
      have secondProof := ihSecond assignment depth antecedent antecedentSorted assignmentSorted
        (fun offset smaller => boundSlots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        variableProof constantProof limit baseBound constantBound assignmentBound antecedentBound secondBound variableProofBound constantProofBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ _)
      simp only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      first
      | exact ⟨⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound _, encodeType_varsBelow _ _ _ baseBound _, firstTerm, secondTerm⟩, firstProof, secondProof⟩
      | exact ⟨⟨antecedentBound, firstTerm, secondTerm⟩, firstProof, secondProof⟩
      | exact ⟨⟨encodeType_varsBelow _ _ _ baseBound _, antecedentBound, firstTerm, secondTerm⟩, firstProof, secondProof⟩
  | not body ih =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      have bodyTerm := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound body assignment depth assignmentBound bindersBound
      have bodyProof := ih assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent
        variableProof constantProof limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ _)
      simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro ⟨antecedentBound, bodyTerm⟩ bodyProof
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro assignment depth antecedent antecedentSorted assignmentSorted boundSlots independent variableProof constantProof
        limit baseBound constantBound assignmentBound antecedentBound bindersBound variableProofBound constantProofBound
      have rootBound : binders depth < limit := by
        simpa only [Nat.add_zero] using bindersBound 0 (Nat.zero_lt_succ _)
      have rootLookup : context[binders depth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using boundSlots 0 (Nat.zero_lt_succ _)
      have rootSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object := .var rootLookup
      let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
      have extraBound : Preterm.VarsBelow limit extra :=
        ⟨⟨trivial, rootBound⟩, encodeType_varsBelow _ _ _ baseBound domain⟩
      have extraSorted := hasType_sorted signature context rootSorted (encodeType_sorted signature context base baseSorted domain)
      have extensionBound : Preterm.VarsBelow limit (conjunction signature.symbol antecedent extra) :=
        ⟨⟨trivial, antecedentBound⟩, extraBound⟩
      have assignmentExtended : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.VarsBelow limit (Assignment.extend (.var (binders depth)) assignment index) :=
        Assignment.extend_varsBelow (domain := domain) limit
          (.var (binders depth)) assignment rootBound assignmentBound
      have bodyNames : ∀ offset < body.binderDepth, binders (depth + 1 + offset) < limit := by
        intro offset smaller
        have moved := bindersBound (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using moved
      have bodyTerm := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound body
        (Assignment.extend (.var (binders depth)) assignment) (depth + 1) assignmentExtended bodyNames
      change ProofWitness.VarsBelow limit (.theoremApp _ _ _)
      simp only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      constructor
      · first
        | exact ⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound _, encodeType_varsBelow _ _ _ baseBound _, rootBound, bodyTerm⟩
        | exact ⟨encodeType_varsBelow _ _ _ baseBound domain, antecedentBound, rootBound, bodyTerm⟩
      · apply ih
        · exact baseBound
        · exact constantBound
        · exact assignmentExtended
        · exact extensionBound
        · exact bodyNames
        · intro type index
          cases index with
          | vz =>
              change ProofWitness.VarsBelow limit (.theoremApp _ _ [])
              simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false,
                forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, and_true] using
                And.intro antecedentBound extraBound
          | vs index =>
              exact HOLKernelStructuralRules.weaken_varsBelow signature structural limit antecedent extra _
                antecedentSorted extraSorted
                (hasType_sorted signature context (assignmentSorted index)
                  (encodeType_sorted signature context base baseSorted type)) (variableProof index)
                antecedentBound extraBound
                ⟨⟨trivial, assignmentBound index⟩, encodeType_varsBelow _ _ _ baseBound type⟩ (variableProofBound index)
        · intro type symbol
          exact HOLKernelStructuralRules.weaken_varsBelow signature structural limit antecedent extra _
            antecedentSorted extraSorted
            (hasType_sorted signature context (constantSorted symbol)
              (encodeType_sorted signature context base baseSorted type)) (constantProof symbol)
            antecedentBound extraBound
            ⟨⟨trivial, constantBound symbol⟩, encodeType_varsBelow _ _ _ baseBound type⟩ (constantProofBound symbol)

#print axioms compileWithAssignment_varsBelow

theorem weakenVariables_varsBelow (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (base : Base → Preterm) {gamma : Ctx Base} (assignment : Assignment gamma)
    (antecedent extra : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (proofs : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (limit : Nat)
    (baseBound : ∀ index, Preterm.VarsBelow limit (base index))
    (valuesBound : ∀ {type} (index : Var gamma type), Preterm.VarsBelow limit (assignment index))
    (antecedentBound : Preterm.VarsBelow limit antecedent) (extraBound : Preterm.VarsBelow limit extra)
    (proofsBound : ∀ {type} (index : Var gamma type), (proofs index).val.VarsBelow limit) :
    ∀ {type} (index : Var gamma type),
      (weakenVariables signature structural base assignment antecedent extra antecedentSorted extraSorted baseSorted assignmentSorted proofs index).val.VarsBelow limit := by
  intro type index
  exact HOLKernelStructuralRules.weaken_varsBelow signature structural limit antecedent extra _
    antecedentSorted extraSorted
    (hasType_sorted signature context (assignmentSorted index) (encodeType_sorted signature context base baseSorted type))
    (proofs index) antecedentBound extraBound
    ⟨⟨trivial, valuesBound index⟩, encodeType_varsBelow _ _ _ baseBound type⟩ (proofsBound index)

theorem weakenConstants_varsBelow (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (antecedent extra : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (proofs : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (limit : Nat)
    (baseBound : ∀ index, Preterm.VarsBelow limit (base index))
    (valuesBound : ∀ {type} (symbol : Const type), Preterm.VarsBelow limit (constant symbol))
    (antecedentBound : Preterm.VarsBelow limit antecedent) (extraBound : Preterm.VarsBelow limit extra)
    (proofsBound : ∀ {type} (symbol : Const type), (proofs symbol).val.VarsBelow limit) :
    ∀ {type} (symbol : Const type),
      (weakenConstants signature structural base constant antecedent extra antecedentSorted extraSorted baseSorted constantSorted proofs symbol).val.VarsBelow limit := by
  intro type symbol
  exact HOLKernelStructuralRules.weaken_varsBelow signature structural limit antecedent extra _
    antecedentSorted extraSorted
    (hasType_sorted signature context (constantSorted symbol) (encodeType_sorted signature context base baseSorted type))
    (proofs symbol) antecedentBound extraBound
    ⟨⟨trivial, valuesBound symbol⟩, encodeType_varsBelow _ _ _ baseBound type⟩ (proofsBound symbol)


end Mettapedia.Languages.MM0.HOLKernelTermTyping
