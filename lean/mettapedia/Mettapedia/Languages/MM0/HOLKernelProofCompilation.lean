import Mettapedia.Languages.MM0.HOLKernelProofExtensionality

/-!
# Constructive compilation of all retained HOL rules to maintained MM0 HOL

The source is the complete 29-constructor ProofSyntax calculus. Each recursive
premise compiles in its allocated preorder frame. Binding premises extend the
source assignment and transport the ordered assumptions; constructed alpha and
substitution equations restore the exact source conclusion.

The output is an actual native proof witness with its local checking derivation.
The theorem-table premises identify the maintained rule headers and logical
definitions. Admission of that table and native binary qualification are separate
obligations. No arbitrary accepted MM0 proof is asserted to belong to the source
calculus, and no bijection of proof presentations is claimed.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofCompilation
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelProofEnvironment HOLKernelProofAllocation
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {hypotheses : List Preterm}
variable {signature : Signature sorts terms} {layout : Layout} {initial : Context}
variable {encoding : Encoding signature layout initial Base Const}

abbrev Conclusion {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {sourceDepth : Nat}
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth) (formula : Formula Const gamma) :=
  CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := NativeContext signature layout initial) (hypotheses := hypotheses)
    (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode formula)))

def compile
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {formula : Formula Const gamma}
    (proof : ProofSyntax Const assumptions formula) :
    ∀ {sourceDepth : Nat}
      (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
        encoding gamma assumptions sourceDepth) (frame : Nat),
      frame + proof.nodeCount ≤ layout.frames →
      sourceDepth + layout.width ≤ layout.workDepth frame →
      proof.binderBudget ≤ layout.width → Conclusion environment formula := by
  intro sourceDepth environment frame space before budget
  have active : frame < layout.frames := by have positive := proof.nodeCount_pos; omega
  have counts := proof.nodeCount_eq_premiseSum
  have own := proof.conclusionBinderDepth_lt
  match proof with
  | .hyp occurrence => exact (environment.assumptionProof occurrence)
  | .topI => exact (HOLKernelInferenceProofs.Native.truth signature rules environment.scope.logical environment.scope.logicalSorted)
  | .andI (φ := first) (ψ := second) left right =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have leftBudget : left.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.andI left right)) (max left.binderBudget right.binderBudget) ≤ layout.width at budget
        omega
      have rightBudget : right.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.andI left right)) (max left.binderBudget right.binderBudget) ≤ layout.width at budget
        omega
      have leftFit : first.binderDepth ≤ layout.width := by have h := left.conclusionBinderDepth_lt; omega
      have rightFit : second.binderDepth ≤ layout.width := by have h := right.conclusionBinderDepth_lt; omega
      have leftBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have rightBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + left.nodeCount by omega))
      exact Id.run do
        let leftProof ← compile abbreviation profile structural typing rules binding left environment (frame + 1) (by omega) leftBefore leftBudget
        let rightProof ← compile abbreviation profile structural typing rules binding right environment (frame + 1 + left.nodeCount) (by omega) rightBefore rightBudget
        pure (HOLKernelInferenceProofs.Native.conjunctionIntroduction signature rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first leftFit active before)
          (environment.encoded_sorted second rightFit active before) leftProof rightProof)
  | .impI (φ := first) (ψ := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.impI child)) child.binderBudget ≤ layout.width at budget
        omega
      have firstFit : first.binderDepth < layout.width := by
        simp only [Term.binderDepth] at own
        omega
      have secondFit : second.binderDepth ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.assume structural first firstFit active before
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.implicationIntroduction signature rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before)
          (environment.encoded_sorted second secondFit active before)
          (environment.typed structural typing first (Nat.le_of_lt firstFit) active before)
          (environment.typed structural typing second secondFit active before) childProof)
  | .allI (σ := domain) (φ := body) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.allI child)) (child.binderBudget + 1) ≤ layout.width at budget
        omega
      have bodyFit : body.binderDepth + 1 ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.bind abbreviation profile structural typing rules binding domain active before
      have nextBefore := layout.child_source_before_next_frame (show frame < frame + 1 by omega)
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelSourceBinding.universalIntroduction signature abbreviation profile structural typing rules binding
          encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
          (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
          body environment.assignment environment.scope (environment.windows active before) bodyFit
          (environment.logicalIndependent _ before) environment.assignmentSorted environment.variableTyping environment.constantTyping childProof)
  | .botE (φ := result) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.botE child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have resultFit : result.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.contradiction signature rules environment.scope.logical _ environment.scope.logicalSorted
          (environment.encoded_sorted result resultFit active before) (environment.typed structural typing result resultFit active before) childProof)
  | .andEL (φ := first) (ψ := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.andEL child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have bound := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at bound
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.conjunctionLeft signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof)
  | .andER (φ := first) (ψ := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.andER child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have bound := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at bound
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.conjunctionRight signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof)
  | .orIL (φ := first) (ψ := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orIL child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.disjunctionLeft signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
          childProof (environment.typed structural typing second secondFit active before))
  | .orIR (φ := first) (ψ := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orIR child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.disjunctionRight signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
          (environment.typed structural typing first firstFit active before) childProof)
  | .impE (φ := first) (ψ := second) function argument =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have functionBudget : function.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.impE function argument)) (max function.binderBudget argument.binderBudget) ≤ layout.width at budget
        omega
      have argumentBudget : argument.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.impE function argument)) (max function.binderBudget argument.binderBudget) ≤ layout.width at budget
        omega
      have bound := function.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at bound
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      have functionBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have argumentBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + function.nodeCount by omega))
      exact Id.run do
        let functionProof ← compile abbreviation profile structural typing rules binding function environment (frame + 1) (by omega) functionBefore functionBudget
        let argumentProof ← compile abbreviation profile structural typing rules binding argument environment (frame + 1 + function.nodeCount) (by omega) argumentBefore argumentBudget
        pure (HOLKernelInferenceProofs.Native.implicationElimination signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) functionProof argumentProof)
  | .notI (φ := first) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.notI child)) child.binderBudget ≤ layout.width at budget
        omega
      have firstFit : first.binderDepth < layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.assume structural first firstFit active before
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
        let implication := HOLKernelInferenceProofs.Native.implicationIntroduction signature rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before)
          (signature.application _ .falsity [] .nil)
          (environment.typed structural typing first (Nat.le_of_lt firstFit) active before)
          (environment.typed structural typing (.bot : Formula Const gamma) (by simp [Term.binderDepth]) active before) childProof
        pure (HOLKernelInferenceProofs.Native.negationIntroduction signature rules environment.scope.logical _ environment.scope.logicalSorted
          (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before) implication)
  | .notE (φ := first) negative positive =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have negativeBudget : negative.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.notE negative positive)) (max negative.binderBudget positive.binderBudget) ≤ layout.width at budget
        omega
      have positiveBudget : positive.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.notE negative positive)) (max negative.binderBudget positive.binderBudget) ≤ layout.width at budget
        omega
      have firstFit : first.binderDepth ≤ layout.width := by have bound := positive.conclusionBinderDepth_lt; omega
      have negativeBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have positiveBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + negative.nodeCount by omega))
      exact Id.run do
        let negativeProof ← compile abbreviation profile structural typing rules binding negative environment (frame + 1) (by omega) negativeBefore negativeBudget
        let positiveProof ← compile abbreviation profile structural typing rules binding positive environment (frame + 1 + negative.nodeCount) (by omega) positiveBefore positiveBudget
        let implication := HOLKernelInferenceProofs.Native.negationElimination signature rules environment.scope.logical _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) negativeProof
        pure (HOLKernelInferenceProofs.Native.implicationElimination signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (signature.application _ .falsity [] .nil) implication positiveProof)
  | .eqRefl (τ := type) term =>
      have fit : term.binderDepth ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      exact (HOLKernelInferenceProofs.Native.reflexivity signature rules environment.scope.logical (encodeType signature.symbol encoding.base type) _
        environment.scope.logicalSorted (encodeType_sorted signature _ encoding.base encoding.baseSorted type)
        (environment.encoded_sorted term fit active before) (environment.typed structural typing term fit active before))
  | .orE (φ := first) (ψ := second) (χ := result) cases left right =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have caseBudget : cases.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orE cases left right)) (max cases.binderBudget (max left.binderBudget right.binderBudget)) ≤ layout.width at budget
        omega
      have leftBudget : left.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orE cases left right)) (max cases.binderBudget (max left.binderBudget right.binderBudget)) ≤ layout.width at budget
        omega
      have rightBudget : right.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orE cases left right)) (max cases.binderBudget (max left.binderBudget right.binderBudget)) ≤ layout.width at budget
        omega
      have raw := cases.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at raw
      have firstFit : first.binderDepth < layout.width := by omega
      have secondFit : second.binderDepth < layout.width := by omega
      have resultFit : result.binderDepth ≤ layout.width := by omega
      let leftEnvironment := environment.assume structural first firstFit active before
      let rightEnvironment := environment.assume structural second secondFit active before
      have casesBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have leftBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + cases.nodeCount by omega))
      have rightBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + cases.nodeCount + left.nodeCount by omega))
      exact Id.run do
        let casesProof ← compile abbreviation profile structural typing rules binding cases environment (frame + 1) (by omega) casesBefore caseBudget
        let leftProof ← compile abbreviation profile structural typing rules binding left leftEnvironment (frame + 1 + cases.nodeCount) (by omega) leftBefore leftBudget
        let rightProof ← compile abbreviation profile structural typing rules binding right rightEnvironment (frame + 1 + cases.nodeCount + left.nodeCount) (by omega) rightBefore rightBudget
        pure (HOLKernelInferenceProofs.Native.disjunctionElimination signature rules environment.scope.logical _ _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before) (environment.encoded_sorted second (Nat.le_of_lt secondFit) active before)
          (environment.encoded_sorted result resultFit active before) casesProof (environment.typed structural typing result resultFit active before) leftProof rightProof)
  | .eqLam (σ := domain) (τ := result) (t := first) (u := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqLam child)) (child.binderBudget + 1) ≤ layout.width at budget
        omega
      have bodyFit : max first.binderDepth second.binderDepth + 1 ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.bind abbreviation profile structural typing rules binding domain active before
      have nextBefore := layout.child_source_before_next_frame (show frame < frame + 1 by omega)
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelSourceBinding.abstractionCongruence signature profile structural typing rules binding
          encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
          (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
          first second environment.assignment environment.scope (environment.windows active before) bodyFit
          (environment.logicalIndependent _ before) environment.assignmentSorted environment.variableTyping environment.constantTyping childProof)
  | .exE (σ := domain) (φ := body) (ψ := result) existential bodyProof =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have existsBudget : existential.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.exE existential bodyProof)) (max existential.binderBudget bodyProof.binderBudget) ≤ layout.width at budget
        omega
      have bodyBudget : bodyProof.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.exE existential bodyProof)) (max existential.binderBudget bodyProof.binderBudget) ≤ layout.width at budget
        omega
      have raw := existential.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at raw
      have bodyFit : body.binderDepth < layout.width := by omega
      have combinedFit : max (body.binderDepth + 1) (result.binderDepth + 1) ≤ layout.width := by omega
      have existsBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have bodySpace : frame + 1 + existential.nodeCount + bodyProof.nodeCount ≤ layout.frames := by omega
      have bodyActive : frame + 1 + existential.nodeCount < layout.frames := by have positive := bodyProof.nodeCount_pos; omega
      have bodyBefore := layout.child_source_before_next_frame (show frame < frame + 1 + existential.nodeCount by omega)
      let opened := environment.bind abbreviation profile structural typing rules binding domain active before
      let next := opened.assume structural body bodyFit bodyActive bodyBefore
      exact Id.run do
        let existsProof ← compile abbreviation profile structural typing rules binding existential environment (frame + 1) (by omega) existsBefore existsBudget
        let childProof ← compile abbreviation profile structural typing rules binding bodyProof next (frame + 1 + existential.nodeCount) bodySpace bodyBefore bodyBudget
        pure (HOLKernelSourceBinding.existentialElimination signature abbreviation profile structural typing rules binding
          encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
          (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
          body result environment.assignment environment.scope (environment.windows active before) combinedFit
          (environment.logicalIndependent _ before)
          (environment.assignmentIndependent _ (by change sourceDepth ≤ layout.workDepth frame; omega)) (encoding.constantIndependent _)
          (by intro offset smaller same; have equal := Layout.names_injective initial same
              simp only [Environment.windows] at equal; omega)
          environment.assignmentSorted environment.variableTyping environment.constantTyping existsProof childProof)
  | .eqSymm (τ := type) (t := first) (u := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqSymm child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.symmetry signature rules (encodeType signature.symbol encoding.base type) environment.scope.logical _ _
          (encodeType_sorted signature _ encoding.base encoding.baseSorted type) environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof)
  | .eqTrans (τ := type) (t := first) (u := middle) (v := last) left right =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have leftBudget : left.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqTrans left right)) (max left.binderBudget right.binderBudget) ≤ layout.width at budget
        omega
      have rightBudget : right.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqTrans left right)) (max left.binderBudget right.binderBudget) ≤ layout.width at budget
        omega
      have leftBound := left.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at own leftBound
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have middleFit : middle.binderDepth ≤ layout.width := by omega
      have lastFit : last.binderDepth ≤ layout.width := by omega
      have leftBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have rightBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + left.nodeCount by omega))
      exact Id.run do
        let leftProof ← compile abbreviation profile structural typing rules binding left environment (frame + 1) (by omega) leftBefore leftBudget
        let rightProof ← compile abbreviation profile structural typing rules binding right environment (frame + 1 + left.nodeCount) (by omega) rightBefore rightBudget
        pure (HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical (encodeType signature.symbol encoding.base type) _ _ _
          environment.scope.logicalSorted (encodeType_sorted signature _ encoding.base encoding.baseSorted type)
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted middle middleFit active before)
          (environment.encoded_sorted last lastFit active before) leftProof rightProof)
  | .eqPropI (p := first) (q := second) forward backward =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have forwardBudget : forward.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqPropI forward backward)) (max forward.binderBudget backward.binderBudget) ≤ layout.width at budget
        omega
      have backwardBudget : backward.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqPropI forward backward)) (max forward.binderBudget backward.binderBudget) ≤ layout.width at budget
        omega
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      have forwardBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have backwardBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 + forward.nodeCount by omega))
      exact Id.run do
        let forwardProof ← compile abbreviation profile structural typing rules binding forward environment (frame + 1) (by omega) forwardBefore forwardBudget
        let backwardProof ← compile abbreviation profile structural typing rules binding backward environment (frame + 1 + forward.nodeCount) (by omega) backwardBefore backwardBudget
        pure (HOLKernelInferenceProofs.propositionalExtensionality signature abbreviation rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) forwardProof backwardProof)
  | .eqPropEL (p := first) (q := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqPropEL child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have raw := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at raw
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.equalityImplicationLeft signature abbreviation rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) childProof)
  | .eqPropER (p := first) (q := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqPropER child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have raw := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at raw
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.equalityImplicationRight signature abbreviation rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) childProof)
  | .eqApp (σ := domain) (τ := result) (f := first) (g := second) argument child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqApp argument child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      have argumentFit : argument.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.applicationFunction signature rules
          (encodeType signature.symbol encoding.base domain) (encodeType signature.symbol encoding.base result) environment.scope.logical _ _ _
          (encodeType_sorted signature _ encoding.base encoding.baseSorted domain) (encodeType_sorted signature _ encoding.base encoding.baseSorted result)
          environment.scope.logicalSorted (environment.encoded_sorted argument argumentFit active before)
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
          childProof (environment.typed structural typing argument argumentFit active before))
  | .eqAppArg (σ := domain) (τ := result) function (t := first) (u := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqAppArg function child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have functionFit : function.binderDepth ≤ layout.width := by omega
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelInferenceProofs.Native.applicationArgument signature rules
          (encodeType signature.symbol encoding.base domain) (encodeType signature.symbol encoding.base result) environment.scope.logical _ _ _
          (encodeType_sorted signature _ encoding.base encoding.baseSorted domain) (encodeType_sorted signature _ encoding.base encoding.baseSorted result)
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) (environment.encoded_sorted function functionFit active before)
          (environment.typed structural typing function functionFit active before) childProof)
  | .allE (φ := body) argument child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.allE argument child)) child.binderBudget ≤ layout.width at budget
        omega
      have required := ProofSyntax.specialization_requirement_le argument child
      have fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width := by omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelProofInstantiation.universalElimination abbreviation profile structural typing rules binding
          environment argument body fits active before childProof)
  | .exI (φ := body) argument child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.exI argument child)) child.binderBudget ≤ layout.width at budget
        omega
      have required := ProofSyntax.existential_requirement_le argument child
      have fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width := by omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelProofInstantiation.existentialIntroduction abbreviation profile structural typing rules binding
          environment argument body fits active before childProof)
  | .beta argument body =>
      have required := ProofSyntax.beta_requirement_le (Δ := assumptions) argument body
      have fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width := by omega
      exact (HOLKernelProofInstantiation.beta abbreviation profile structural typing rules binding
        environment argument body fits active before)
  | .eta function =>
      have required : function.binderDepth + 1 ≤ (ProofSyntax.eta (Δ := assumptions) function).localBinderBudget := Nat.le_max_right _ _
      have fits : function.binderDepth + 1 ≤ layout.width :=
        required.trans ((ProofSyntax.eta (Δ := assumptions) function).localBinderBudget_le.trans budget)
      exact (HOLKernelProofExtensionality.eta profile structural typing rules binding environment function fits active before)
  | .funExt (σ := domain) (f := first) (g := second) child =>
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.funExt child)) child.binderBudget ≤ layout.width at budget
        omega
      have fits : max first.binderDepth second.binderDepth + 1 ≤ layout.width := by
        apply Nat.le_trans (Nat.le_of_lt (m := child.binderBudget) ?_) childBudget
        calc
          max first.binderDepth second.binderDepth + 1 =
              (Term.all (σ := domain) (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))).binderDepth := by
                simp only [Term.binderDepth, weaken, Term.binderDepth_rename, Nat.max_zero]
          _ < child.binderBudget := child.conclusionBinderDepth_lt
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      exact Id.run do
        let childProof ← compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
        pure (HOLKernelProofExtensionality.functionExtensionality abbreviation profile structural typing rules binding
          environment first second fits active before childProof)
termination_by structural proof

theorem compile_accepted
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {formula : Formula Const gamma}
    (proof : ProofSyntax Const assumptions formula) {sourceDepth : Nat}
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth) (frame : Nat)
    (space : frame + proof.nodeCount ≤ layout.frames)
    (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (budget : proof.binderBudget ≤ layout.width)
    : (compile abbreviation profile structural typing rules binding proof environment frame space before budget).val.check terms definitions theorems (NativeContext signature layout initial) hypotheses
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode formula))) = true :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mpr (compile abbreviation profile structural typing rules binding proof environment frame space before budget).property

theorem compile_refuses_changed_conclusion
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {formula : Formula Const gamma}
    (proof : ProofSyntax Const assumptions formula) {sourceDepth : Nat}
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth) (frame : Nat)
    (space : frame + proof.nodeCount ≤ layout.frames)
    (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (budget : proof.binderBudget ≤ layout.width)
    (changed : Preterm)
    (different : changed ≠ entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode formula))) :
    (compile abbreviation profile structural typing rules binding proof environment frame space before budget).val.check terms definitions theorems (NativeContext signature layout initial) hypotheses changed = false := by
  let output := compile abbreviation profile structural typing rules binding proof environment frame space before budget
  cases accepted : output.val.check terms definitions theorems (NativeContext signature layout initial) hypotheses changed with
  | false => rfl
  | true =>
      have original := output.property.eval
      have altered := ((ProofWitness.check_iff _ _ _ _ _ _ _).mp accepted).eval
      rw [original] at altered
      exact (different (Option.some.inj altered).symm).elim

/-- Allocate the complete proof after an admitted initial context. Inputs
supply only source-variable and constant typing, never a compound proof. -/
def compileFromInitial (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (formed : Context.WellFormed sorts initial)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (baseSorted : ∀ index, Preterm.HasType terms initial (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms initial (constant symbol) [] signature.ids.object)
    {gamma : Ctx Base} (assignment : Assignment gamma)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms initial (assignment index) [] signature.ids.object)
    (formation : Preterm) (formationSorted : Preterm.HasType terms initial formation [] signature.ids.wff)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := initial) (hypotheses := hypotheses)
        (HOLKernelTypingRules.typed signature.symbol formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := initial) (hypotheses := hypotheses)
        (HOLKernelTypingRules.typed signature.symbol formation (constant symbol) (encodeType signature.symbol base type)))
    {assumptions : List (Formula Const gamma)} {formula : Formula Const gamma}
    (proof : ProofSyntax Const assumptions formula) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := (forProof proof).target initial signature.ids.object) (hypotheses := hypotheses)
      (entails signature.symbol
        (HOLKernelAssumptions.antecedent signature.symbol formation
          (assumptions.map (fun source => holds signature.symbol
            (encodeWithAssignment signature.symbol base constant (Layout.names initial) assignment 0 source))))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant (Layout.names initial) assignment 0 formula))) := by
  let environment := Environment.fromInitial signature (forProof proof) initial formed structural base constant baseSorted constantSorted
    gamma assignment assignmentSorted formation formationSorted variableTyping constantTyping assumptions
    (fun source member => proof.assumptionBinderDepth_lt source member)
  exact compile abbreviation profile structural typing rules binding proof environment 0
    (by change 0 + proof.nodeCount ≤ proof.nodeCount; omega)
    (by simp [Layout.workDepth]) (Nat.le_refl _)

#print axioms compile
#print axioms compileFromInitial
#print axioms compile_accepted
#print axioms compile_refuses_changed_conclusion
end Mettapedia.Languages.MM0.HOLKernelProofCompilation
