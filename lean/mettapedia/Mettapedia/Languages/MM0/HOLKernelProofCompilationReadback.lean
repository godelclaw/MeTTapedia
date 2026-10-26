import Mettapedia.Languages.MM0.HOLKernelContextualProofReadback

/-!
# Independent admission of the complete maintained HOL compiler

Every constructor of the common HOL proof syntax compiles to a certificate in
`AdmittedProof`. The induction follows the actual native certificate producer,
including its allocated binder frames and Boolean-equivalence definitions.

The induction permits an additional reader context. In the extensionality
case, the pointwise child is reconstructed under the fresh argument name;
only the environment's bounded leaf certificates are weakened. No arbitrary
proof-tree renaming or supplied source derivation is used for admission.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofCompilationReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelRuleInstances HOLKernelProofReadback HOLKernelProofEnvironment HOLKernelProofAllocation
open HOLKernelEnvironmentReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)
open HOLKernelStructuralRules (CheckedProof)
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms} {layout : Layout}
variable {encoding : Encoding signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids) Unit Symbol}

set_option maxHeartbeats 3000000 in
/-- The actual compiler image satisfies the independent certificate grammar,
with exact renamed conclusions and the environment's ordered assumptions. -/
theorem compile_admitted
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {formula : Formula Symbol gamma}
    (proof : ProofSyntax Symbol assumptions formula) :
    ∀ {depth : Nat} (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := []) encoding gamma assumptions depth)
      (frame : Nat) (space : frame + proof.nodeCount ≤ layout.frames)
      (before : depth + layout.width ≤ layout.workDepth frame) (budget : proof.binderBudget ≤ layout.width)
      {target : Ctx Unit} (rho : Rename Unit gamma target) (names : Names target)
      (reading : ContextualReading abbreviation profile environment rho names)
      (_scope : InScope 7 names (layout.workDepth frame))
      (_sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
      (_bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
      (_projection : reading.ProjectionAdmitted ruleAt bindingAt)
      (_assumptionTrees : reading.AssumptionsAdmitted ruleAt bindingAt),
      ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
        (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding proof environment frame space before budget).val
        (.imp reading.logical.formula (HOL.rename rho formula))) := by
  induction proof with
  | @hyp gamma assumptions occurrence =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (assumptions.get occurrence) := (ProofSyntax.hyp occurrence)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.hyp occurrence) environment frame space before budget).val = (environment.assumptionProof occurrence).val := rfl
      rw [witnessEq]
      exact assumptionTrees occurrence
  | @topI gamma assumptions =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.top) := (ProofSyntax.topI (Const := Symbol) (Γ := gamma) (Δ := assumptions))
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      let parent := HOLKernelInferenceProofs.Native.truth (definitions := definitions) (hypotheses := []) signature rules environment.scope.logical environment.scope.logicalSorted
      let parentOperands : InferenceArguments Symbol target .truth := (.truth reading.logical.formula)
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .truth ([environment.scope.logical].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .truth [environment.scope.logical] parentOperands parentParsed
        ruleAt bindingAt (selected .truth) _ parent [] rfl (1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using .nil)
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.topI (Const := Symbol) (Γ := gamma) (Δ := assumptions)) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @andI gamma assumptions first second left right leftIH rightIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.and first second) := (ProofSyntax.andI left right)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let leftProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding left environment (frame + 1) (by omega) leftBefore leftBudget
      obtain ⟨leftProofFuel, ⟨leftProofTree⟩⟩ := leftIH environment (frame + 1) (by omega) leftBefore leftBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let rightProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding right environment (frame + 1 + left.nodeCount) (by omega) rightBefore rightBudget
      obtain ⟨rightProofFuel, ⟨rightProofTree⟩⟩ := rightIH environment (frame + 1 + left.nodeCount) (by omega) rightBefore rightBudget
        rho names reading (scopeLater (frame + 1 + left.nodeCount) (by omega)) sourceWindow (boundedLater (frame + 1 + left.nodeCount) (by omega)) projection assumptionTrees
      let parent := HOLKernelInferenceProofs.Native.conjunctionIntroduction signature rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first leftFit active before)
          (environment.encoded_sorted second rightFit active before) leftProof rightProof
      let parentOperands : InferenceArguments Symbol target .conjunctionIntroduction := (.conjunctionIntroduction reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .conjunctionIntroduction ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .conjunctionIntroduction [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .conjunctionIntroduction) _ parent [leftProof.val, rightProof.val] rfl (1 + leftProofFuel + rightProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (leftProofTree.weakenFuel (by omega)) (.cons (rightProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.andI left right) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @impI gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.imp first second) := (ProofSyntax.impI child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let nextReading := reading.assume distinct structural first firstFit active before
      have nextReadingProjection := reading.assume_projection_admitted distinct structural ruleAt bindingAt structuralSelected projection first firstFit active before
      have nextReadingAssumptions := reading.assume_assumptions_admitted distinct structural ruleAt bindingAt structuralSelected assumptionTrees first firstFit active before
      have nextReadingBound := environment.assume_proofsVarsBelow structural first firstFit active before (layout.workDepth (frame + 1)) nextBefore
        (boundedLater (frame + 1) (by omega))
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH next (frame + 1) (by omega) nextBefore childBudget
        rho names nextReading (scopeLater (frame + 1) (by omega)) sourceWindow nextReadingBound nextReadingProjection nextReadingAssumptions
      let firstTyped := environment.typed structural typing first (Nat.le_of_lt firstFit) active before
      obtain ⟨firstTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt first (Nat.le_of_lt firstFit) active before
      let secondTyped := environment.typed structural typing second secondFit active before
      obtain ⟨secondTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt second secondFit active before
      let parent := HOLKernelInferenceProofs.Native.implicationIntroduction signature rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before)
          (environment.encoded_sorted second secondFit active before)
          (environment.typed structural typing first (Nat.le_of_lt firstFit) active before)
          (environment.typed structural typing second secondFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .implicationIntroduction := (.implicationIntroduction reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .implicationIntroduction ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .implicationIntroduction [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .implicationIntroduction) _ parent [firstTyped.val, secondTyped.val, childProof.val] rfl (1 + 1 + 1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (firstTypedTree.weakenFuel (by omega)) (.cons (secondTypedTree.weakenFuel (by omega)) (.cons (childProofTree.weakenFuel (by omega)) .nil))))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.impI child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @allI gamma assumptions domain body child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.all body) := (ProofSyntax.allI child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.allI child)) (child.binderBudget + 1) ≤ layout.width at budget
        omega
      have bodyFit : body.binderDepth + 1 ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.bind abbreviation profile structural typing rules binding domain active before
      have nextBefore := layout.child_source_before_next_frame (show frame < frame + 1 by omega)
      let root := Layout.names initial (layout.workDepth frame)
      let nextNames : Names (domain :: target) := BinderNames.cons root names
      let boundReading := reading.bind distinct structural typing rules binding domain active before scope
      have boundProjection := reading.bind_projection_admitted distinct structural typing rules binding ruleAt bindingAt structuralSelected projection domain active before bounded scope
      have boundAssumptions := reading.bind_assumptions_admitted distinct structural typing rules binding ruleAt bindingAt selected structuralSelected
        (bindingSelected .abstractionRenaming) assumptionTrees projection domain active before bounded scope sourceWindow
      have boundBounds := environment.bind_proofsVarsBelow abbreviation profile structural typing rules binding domain active before bounded
      have namesBefore : InScope 7 nextNames (layout.workDepth frame + 1) := by
        refine ⟨boundReading.names_distinct, ?_⟩
        intro name member
        refine ⟨boundReading.names_above name member, ?_⟩
        rcases List.mem_cons.mp member with rfl | old
        · change 7 + layout.workDepth frame < 7 + (layout.workDepth frame + 1); omega
        · have h := (scope.2 _ old).2; omega
      have boundScope (nextFrame : Nat) (later : frame < nextFrame) : InScope 7 nextNames (layout.workDepth nextFrame) := by
        refine ⟨namesBefore.1, ?_⟩
        intro name member
        have h := namesBefore.2 name member
        have after := layout.child_source_before_next_frame later
        exact ⟨h.1, by omega⟩
      have boundWindow : ∀ offset < layout.width, 7 + (layout.workDepth frame + 1 + offset) ∉ nextNames.toList := by
        intro offset _ member
        have h := (namesBefore.2 _ member).2
        omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH next (frame + 1) (by omega) nextBefore childBudget
        (Rename.lift rho) nextNames boundReading (boundScope (frame + 1) (by omega)) boundWindow boundBounds boundProjection boundAssumptions
      let parent := HOLKernelSourceBinding.universalIntroduction signature abbreviation profile structural typing rules binding
          encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
          (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
          body environment.assignment environment.scope (environment.windows active before) bodyFit
          (environment.logicalIndependent _ before) environment.assignmentSorted environment.variableTyping environment.constantTyping childProof
      have parentAdmitted := reading.universalIntroduction_admitted distinct structural typing rules binding body bodyFit active before scope sourceWindow childProof ruleAt bindingAt selected structuralSelected bindingSelected projection (by simpa only [boundReading, ContextualReading.bind, Judgment.formula, Judgment.rename_formula, HOL.weaken] using childProofTree)
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.allI child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @botE gamma assumptions result child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (result) := (ProofSyntax.botE (φ := result) child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.botE child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have resultFit : result.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let resultTyped := environment.typed structural typing result resultFit active before
      obtain ⟨resultTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt result resultFit active before
      let parent := HOLKernelInferenceProofs.Native.contradiction signature rules environment.scope.logical _ environment.scope.logicalSorted
          (environment.encoded_sorted result resultFit active before) (environment.typed structural typing result resultFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .contradiction := (.contradiction reading.logical.formula (HOL.rename rho result))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .contradiction ([environment.scope.logical, (environment.encode result)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .contradiction [environment.scope.logical, (environment.encode result)] parentOperands parentParsed
        ruleAt bindingAt (selected .contradiction) _ parent [resultTyped.val, childProof.val] rfl (1 + 1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (resultTypedTree.weakenFuel (by omega)) (.cons (childProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.botE child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @andEL gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (first) := (ProofSyntax.andEL child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.andEL child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have bound := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at bound
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let parent := HOLKernelInferenceProofs.Native.conjunctionLeft signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .conjunctionLeft := (.conjunctionLeft reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .conjunctionLeft ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .conjunctionLeft [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .conjunctionLeft) _ parent [childProof.val] rfl (1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (childProofTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.andEL child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @andER gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (second) := (ProofSyntax.andER child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.andER child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have bound := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at bound
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let parent := HOLKernelInferenceProofs.Native.conjunctionRight signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .conjunctionRight := (.conjunctionRight reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .conjunctionRight ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .conjunctionRight [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .conjunctionRight) _ parent [childProof.val] rfl (1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (childProofTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.andER child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @orIL gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.or first second) := (ProofSyntax.orIL (ψ := second) child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orIL child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let secondTyped := environment.typed structural typing second secondFit active before
      obtain ⟨secondTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt second secondFit active before
      let parent := HOLKernelInferenceProofs.Native.disjunctionLeft signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
          childProof (environment.typed structural typing second secondFit active before)
      let parentOperands : InferenceArguments Symbol target .disjunctionLeft := (.disjunctionLeft reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .disjunctionLeft ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .disjunctionLeft [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .disjunctionLeft) _ parent [childProof.val, secondTyped.val] rfl (1 + childProofFuel + 1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (childProofTree.weakenFuel (by omega)) (.cons (secondTypedTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.orIL (ψ := second) child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @orIR gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.or first second) := (ProofSyntax.orIR (φ := first) child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.orIR child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let firstTyped := environment.typed structural typing first firstFit active before
      obtain ⟨firstTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt first firstFit active before
      let parent := HOLKernelInferenceProofs.Native.disjunctionRight signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
          (environment.typed structural typing first firstFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .disjunctionRight := (.disjunctionRight reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .disjunctionRight ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .disjunctionRight [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .disjunctionRight) _ parent [firstTyped.val, childProof.val] rfl (1 + 1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (firstTypedTree.weakenFuel (by omega)) (.cons (childProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.orIR (φ := first) child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @impE gamma assumptions first second function argument functionIH argumentIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (second) := (ProofSyntax.impE function argument)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let functionProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding function environment (frame + 1) (by omega) functionBefore functionBudget
      obtain ⟨functionProofFuel, ⟨functionProofTree⟩⟩ := functionIH environment (frame + 1) (by omega) functionBefore functionBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let argumentProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding argument environment (frame + 1 + function.nodeCount) (by omega) argumentBefore argumentBudget
      obtain ⟨argumentProofFuel, ⟨argumentProofTree⟩⟩ := argumentIH environment (frame + 1 + function.nodeCount) (by omega) argumentBefore argumentBudget
        rho names reading (scopeLater (frame + 1 + function.nodeCount) (by omega)) sourceWindow (boundedLater (frame + 1 + function.nodeCount) (by omega)) projection assumptionTrees
      let parent := HOLKernelInferenceProofs.Native.implicationElimination signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) functionProof argumentProof
      let parentOperands : InferenceArguments Symbol target .implicationElimination := (.implicationElimination reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .implicationElimination ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .implicationElimination [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .implicationElimination) _ parent [functionProof.val, argumentProof.val] rfl (1 + functionProofFuel + argumentProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (functionProofTree.weakenFuel (by omega)) (.cons (argumentProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.impE function argument) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @notI gamma assumptions first child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.not first) := (ProofSyntax.notI child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.notI child)) child.binderBudget ≤ layout.width at budget
        omega
      have firstFit : first.binderDepth < layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.assume structural first firstFit active before
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      let nextReading := reading.assume distinct structural first firstFit active before
      have nextReadingProjection := reading.assume_projection_admitted distinct structural ruleAt bindingAt structuralSelected projection first firstFit active before
      have nextReadingAssumptions := reading.assume_assumptions_admitted distinct structural ruleAt bindingAt structuralSelected assumptionTrees first firstFit active before
      have nextReadingBound := environment.assume_proofsVarsBelow structural first firstFit active before (layout.workDepth (frame + 1)) nextBefore
        (boundedLater (frame + 1) (by omega))
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH next (frame + 1) (by omega) nextBefore childBudget
        rho names nextReading (scopeLater (frame + 1) (by omega)) sourceWindow nextReadingBound nextReadingProjection nextReadingAssumptions
      let firstTyped := environment.typed structural typing first (Nat.le_of_lt firstFit) active before
      obtain ⟨firstTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt first (Nat.le_of_lt firstFit) active before
      let botTyped := environment.typed structural typing (Term.bot : Formula Symbol gamma) (by simp [Term.binderDepth]) active before
      obtain ⟨botTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt (Term.bot : Formula Symbol gamma) (by simp [Term.binderDepth]) active before
      let implication := HOLKernelInferenceProofs.Native.implicationIntroduction signature rules environment.scope.logical _ _
        environment.scope.logicalSorted (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before) (signature.application _ .falsity [] .nil)
        firstTyped botTyped childProof
      let implicationOperands : InferenceArguments Symbol target .implicationIntroduction := (.implicationIntroduction reading.logical.formula (HOL.rename rho first) (HOL.rename rho (Term.bot : Formula Symbol gamma)))
      have implicationParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .implicationIntroduction ([environment.scope.logical, (environment.encode first), (environment.encode (Term.bot : Formula Symbol gamma))].map (expandEquivalence signature.symbol abbreviation.reference)) = some implicationOperands := by simp [implicationOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have implicationAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .implicationIntroduction [environment.scope.logical, (environment.encode first), (environment.encode (Term.bot : Formula Symbol gamma))] implicationOperands implicationParsed
        ruleAt bindingAt (selected .implicationIntroduction) _ implication [firstTyped.val, botTyped.val, childProof.val] rfl (1 + 1 + 1 + childProofFuel)
        (by simpa only [implicationOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (firstTypedTree.weakenFuel (by omega)) (.cons (botTypedTree.weakenFuel (by omega)) (.cons (childProofTree.weakenFuel (by omega)) .nil))))
      obtain ⟨implicationTree⟩ := implicationAdmitted
      let parent := HOLKernelInferenceProofs.Native.negationIntroduction signature rules environment.scope.logical _ environment.scope.logicalSorted
          (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before) implication
      let parentOperands : InferenceArguments Symbol target .negationIntroduction := (.negationIntroduction reading.logical.formula (HOL.rename rho first))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .negationIntroduction ([environment.scope.logical, (environment.encode first)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .negationIntroduction [environment.scope.logical, (environment.encode first)] parentOperands parentParsed
        ruleAt bindingAt (selected .negationIntroduction) _ parent [implication.val] rfl (1 + 1 + 1 + 1 + childProofFuel + 1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (implicationTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.notI child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @notE gamma assumptions first negative positive negativeIH positiveIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.bot) := (ProofSyntax.notE negative positive)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let negativeProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding negative environment (frame + 1) (by omega) negativeBefore negativeBudget
      obtain ⟨negativeProofFuel, ⟨negativeProofTree⟩⟩ := negativeIH environment (frame + 1) (by omega) negativeBefore negativeBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let positiveProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding positive environment (frame + 1 + negative.nodeCount) (by omega) positiveBefore positiveBudget
      obtain ⟨positiveProofFuel, ⟨positiveProofTree⟩⟩ := positiveIH environment (frame + 1 + negative.nodeCount) (by omega) positiveBefore positiveBudget
        rho names reading (scopeLater (frame + 1 + negative.nodeCount) (by omega)) sourceWindow (boundedLater (frame + 1 + negative.nodeCount) (by omega)) projection assumptionTrees
      let implication := HOLKernelInferenceProofs.Native.negationElimination signature rules environment.scope.logical _ environment.scope.logicalSorted
        (environment.encoded_sorted first firstFit active before) negativeProof
      let implicationOperands : InferenceArguments Symbol target .negationElimination := (.negationElimination reading.logical.formula (HOL.rename rho first))
      have implicationParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .negationElimination ([environment.scope.logical, (environment.encode first)].map (expandEquivalence signature.symbol abbreviation.reference)) = some implicationOperands := by simp [implicationOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have implicationAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .negationElimination [environment.scope.logical, (environment.encode first)] implicationOperands implicationParsed
        ruleAt bindingAt (selected .negationElimination) _ implication [negativeProof.val] rfl (1 + negativeProofFuel)
        (by simpa only [implicationOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (negativeProofTree.weakenFuel (by omega)) .nil))
      obtain ⟨implicationTree⟩ := implicationAdmitted
      let parent := HOLKernelInferenceProofs.Native.implicationElimination signature rules environment.scope.logical _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (signature.application _ .falsity [] .nil) implication positiveProof
      let parentOperands : InferenceArguments Symbol target .implicationElimination := (.implicationElimination reading.logical.formula (HOL.rename rho first) (HOL.rename rho (Term.bot : Formula Symbol gamma)))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .implicationElimination ([environment.scope.logical, (environment.encode first), (environment.encode (Term.bot : Formula Symbol gamma))].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .implicationElimination [environment.scope.logical, (environment.encode first), (environment.encode (Term.bot : Formula Symbol gamma))] parentOperands parentParsed
        ruleAt bindingAt (selected .implicationElimination) _ parent [implication.val, positiveProof.val] rfl (1 + 1 + negativeProofFuel + 1 + positiveProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (implicationTree.weakenFuel (by omega)) (.cons (positiveProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.notE negative positive) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqRefl gamma assumptions type term =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq term term) := (ProofSyntax.eqRefl (Δ := assumptions) term)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      have fit : term.binderDepth ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      let termTyped := environment.typed structural typing term fit active before
      obtain ⟨termTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt term fit active before
      let parent := HOLKernelInferenceProofs.Native.reflexivity signature rules environment.scope.logical (encodeType signature.symbol encoding.base type) _
        environment.scope.logicalSorted (encodeType_sorted signature _ encoding.base encoding.baseSorted type)
        (environment.encoded_sorted term fit active before) (environment.typed structural typing term fit active before)
      let parentOperands : InferenceArguments Symbol target .reflexivity := (.reflexivity reading.logical.formula (HOL.rename rho term))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .reflexivity ([environment.scope.logical, (encodeType signature.symbol encoding.base type), (environment.encode term)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, readObjectWith, expect_same, reading.type_read distinct]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .reflexivity [environment.scope.logical, (encodeType signature.symbol encoding.base type), (environment.encode term)] parentOperands parentParsed
        ruleAt bindingAt (selected .reflexivity) _ parent [termTyped.val] rfl (1 + 1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (termTypedTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqRefl (Δ := assumptions) term) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @orE gamma assumptions first second result cases left right casesIH leftIH rightIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (result) := (ProofSyntax.orE cases left right)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let leftReading := reading.assume distinct structural first firstFit active before
      have leftReadingProjection := reading.assume_projection_admitted distinct structural ruleAt bindingAt structuralSelected projection first firstFit active before
      have leftReadingAssumptions := reading.assume_assumptions_admitted distinct structural ruleAt bindingAt structuralSelected assumptionTrees first firstFit active before
      have leftReadingBound := environment.assume_proofsVarsBelow structural first firstFit active before (layout.workDepth (frame + 1 + cases.nodeCount)) leftBefore
        (boundedLater (frame + 1 + cases.nodeCount) (by omega))
      let rightReading := reading.assume distinct structural second secondFit active before
      have rightReadingProjection := reading.assume_projection_admitted distinct structural ruleAt bindingAt structuralSelected projection second secondFit active before
      have rightReadingAssumptions := reading.assume_assumptions_admitted distinct structural ruleAt bindingAt structuralSelected assumptionTrees second secondFit active before
      have rightReadingBound := environment.assume_proofsVarsBelow structural second secondFit active before (layout.workDepth (frame + 1 + cases.nodeCount + left.nodeCount)) rightBefore
        (boundedLater (frame + 1 + cases.nodeCount + left.nodeCount) (by omega))
      let casesProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding cases environment (frame + 1) (by omega) casesBefore caseBudget
      obtain ⟨casesProofFuel, ⟨casesProofTree⟩⟩ := casesIH environment (frame + 1) (by omega) casesBefore caseBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let leftProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding left leftEnvironment (frame + 1 + cases.nodeCount) (by omega) leftBefore leftBudget
      obtain ⟨leftProofFuel, ⟨leftProofTree⟩⟩ := leftIH leftEnvironment (frame + 1 + cases.nodeCount) (by omega) leftBefore leftBudget
        rho names leftReading (scopeLater (frame + 1 + cases.nodeCount) (by omega)) sourceWindow leftReadingBound leftReadingProjection leftReadingAssumptions
      let rightProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding right rightEnvironment (frame + 1 + cases.nodeCount + left.nodeCount) (by omega) rightBefore rightBudget
      obtain ⟨rightProofFuel, ⟨rightProofTree⟩⟩ := rightIH rightEnvironment (frame + 1 + cases.nodeCount + left.nodeCount) (by omega) rightBefore rightBudget
        rho names rightReading (scopeLater (frame + 1 + cases.nodeCount + left.nodeCount) (by omega)) sourceWindow rightReadingBound rightReadingProjection rightReadingAssumptions
      let resultTyped := environment.typed structural typing result resultFit active before
      obtain ⟨resultTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt result resultFit active before
      let parent := HOLKernelInferenceProofs.Native.disjunctionElimination signature rules environment.scope.logical _ _ _ environment.scope.logicalSorted
          (environment.encoded_sorted first (Nat.le_of_lt firstFit) active before) (environment.encoded_sorted second (Nat.le_of_lt secondFit) active before)
          (environment.encoded_sorted result resultFit active before) casesProof (environment.typed structural typing result resultFit active before) leftProof rightProof
      let parentOperands : InferenceArguments Symbol target .disjunctionElimination := (.disjunctionElimination reading.logical.formula (HOL.rename rho first) (HOL.rename rho second) (HOL.rename rho result))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .disjunctionElimination ([environment.scope.logical, (environment.encode first), (environment.encode second), (environment.encode result)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .disjunctionElimination [environment.scope.logical, (environment.encode first), (environment.encode second), (environment.encode result)] parentOperands parentParsed
        ruleAt bindingAt (selected .disjunctionElimination) _ parent [casesProof.val, resultTyped.val, leftProof.val, rightProof.val] rfl (1 + casesProofFuel + 1 + leftProofFuel + rightProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (casesProofTree.weakenFuel (by omega)) (.cons (resultTypedTree.weakenFuel (by omega)) (.cons (leftProofTree.weakenFuel (by omega)) (.cons (rightProofTree.weakenFuel (by omega)) .nil)))))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.orE cases left right) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqLam gamma assumptions domain result first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq (.lam first) (.lam second)) := (ProofSyntax.eqLam child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqLam child)) (child.binderBudget + 1) ≤ layout.width at budget
        omega
      have bodyFit : max first.binderDepth second.binderDepth + 1 ≤ layout.width := by simp only [Term.binderDepth] at own; omega
      let next := environment.bind abbreviation profile structural typing rules binding domain active before
      have nextBefore := layout.child_source_before_next_frame (show frame < frame + 1 by omega)
      let root := Layout.names initial (layout.workDepth frame)
      let nextNames : Names (domain :: target) := BinderNames.cons root names
      let boundReading := reading.bind distinct structural typing rules binding domain active before scope
      have boundProjection := reading.bind_projection_admitted distinct structural typing rules binding ruleAt bindingAt structuralSelected projection domain active before bounded scope
      have boundAssumptions := reading.bind_assumptions_admitted distinct structural typing rules binding ruleAt bindingAt selected structuralSelected
        (bindingSelected .abstractionRenaming) assumptionTrees projection domain active before bounded scope sourceWindow
      have boundBounds := environment.bind_proofsVarsBelow abbreviation profile structural typing rules binding domain active before bounded
      have namesBefore : InScope 7 nextNames (layout.workDepth frame + 1) := by
        refine ⟨boundReading.names_distinct, ?_⟩
        intro name member
        refine ⟨boundReading.names_above name member, ?_⟩
        rcases List.mem_cons.mp member with rfl | old
        · change 7 + layout.workDepth frame < 7 + (layout.workDepth frame + 1); omega
        · have h := (scope.2 _ old).2; omega
      have boundScope (nextFrame : Nat) (later : frame < nextFrame) : InScope 7 nextNames (layout.workDepth nextFrame) := by
        refine ⟨namesBefore.1, ?_⟩
        intro name member
        have h := namesBefore.2 name member
        have after := layout.child_source_before_next_frame later
        exact ⟨h.1, by omega⟩
      have boundWindow : ∀ offset < layout.width, 7 + (layout.workDepth frame + 1 + offset) ∉ nextNames.toList := by
        intro offset _ member
        have h := (namesBefore.2 _ member).2
        omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child next (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH next (frame + 1) (by omega) nextBefore childBudget
        (Rename.lift rho) nextNames boundReading (boundScope (frame + 1) (by omega)) boundWindow boundBounds boundProjection boundAssumptions
      let parent := HOLKernelSourceBinding.abstractionCongruence signature profile structural typing rules binding
          encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
          (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
          first second environment.assignment environment.scope (environment.windows active before) bodyFit
          (environment.logicalIndependent _ before) environment.assignmentSorted environment.variableTyping environment.constantTyping childProof
      have parentAdmitted := reading.abstractionCongruence_admitted distinct structural typing rules binding first second bodyFit active before scope sourceWindow childProof ruleAt bindingAt selected structuralSelected bindingSelected projection (by simpa only [boundReading, ContextualReading.bind, Judgment.formula, Judgment.rename_formula, HOL.weaken, HOL.rename] using childProofTree)
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqLam child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @exE gamma assumptions domain body result existential bodyProof existentialIH bodyIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (result) := (ProofSyntax.exE (ψ := result) existential bodyProof)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let root := Layout.names initial (layout.workDepth frame)
      let nextNames : Names (domain :: target) := BinderNames.cons root names
      let boundReading := reading.bind distinct structural typing rules binding domain active before scope
      have boundProjection := reading.bind_projection_admitted distinct structural typing rules binding ruleAt bindingAt structuralSelected projection domain active before bounded scope
      have boundAssumptions := reading.bind_assumptions_admitted distinct structural typing rules binding ruleAt bindingAt selected structuralSelected
        (bindingSelected .abstractionRenaming) assumptionTrees projection domain active before bounded scope sourceWindow
      have boundBounds := environment.bind_proofsVarsBelow abbreviation profile structural typing rules binding domain active before bounded
      have namesBefore : InScope 7 nextNames (layout.workDepth frame + 1) := by
        refine ⟨boundReading.names_distinct, ?_⟩
        intro name member
        refine ⟨boundReading.names_above name member, ?_⟩
        rcases List.mem_cons.mp member with rfl | old
        · change 7 + layout.workDepth frame < 7 + (layout.workDepth frame + 1); omega
        · have h := (scope.2 _ old).2; omega
      have boundScope (nextFrame : Nat) (later : frame < nextFrame) : InScope 7 nextNames (layout.workDepth nextFrame) := by
        refine ⟨namesBefore.1, ?_⟩
        intro name member
        have h := namesBefore.2 name member
        have after := layout.child_source_before_next_frame later
        exact ⟨h.1, by omega⟩
      have boundWindow : ∀ offset < layout.width, 7 + (layout.workDepth frame + 1 + offset) ∉ nextNames.toList := by
        intro offset _ member
        have h := (namesBefore.2 _ member).2
        omega
      let nextReading := boundReading.assume distinct structural body bodyFit bodyActive bodyBefore
      have nextProjection := boundReading.assume_projection_admitted distinct structural ruleAt bindingAt structuralSelected boundProjection body bodyFit bodyActive bodyBefore
      have nextAssumptions := boundReading.assume_assumptions_admitted distinct structural ruleAt bindingAt structuralSelected boundAssumptions body bodyFit bodyActive bodyBefore
      have nextBounds := opened.assume_proofsVarsBelow structural body bodyFit bodyActive bodyBefore
        (layout.workDepth (frame + 1 + existential.nodeCount)) bodyBefore
        (boundBounds.mono opened (Nat.add_le_add_left (layout.workDepth_mono (by omega)) 7))
      let existsProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding existential environment (frame + 1) (by omega) existsBefore existsBudget
      obtain ⟨existsProofFuel, ⟨existsProofTree⟩⟩ := existentialIH environment (frame + 1) (by omega) existsBefore existsBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding bodyProof next (frame + 1 + existential.nodeCount) (by omega) bodyBefore bodyBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := bodyIH next (frame + 1 + existential.nodeCount) (by omega) bodyBefore bodyBudget
        (Rename.lift rho) nextNames nextReading (boundScope (frame + 1 + existential.nodeCount) (by omega)) boundWindow nextBounds nextProjection nextAssumptions
      let parent := HOLKernelSourceBinding.existentialElimination signature abbreviation profile structural typing rules binding
          encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
          (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
          body result environment.assignment environment.scope (environment.windows active before) combinedFit
          (environment.logicalIndependent _ before)
          (environment.assignmentIndependent _ (by change depth ≤ layout.workDepth frame; omega)) (encoding.constantIndependent _)
          (by intro offset smaller same; have equal := Layout.names_injective initial same
              simp only [Environment.windows] at equal; omega)
          environment.assignmentSorted environment.variableTyping environment.constantTyping existsProof childProof
      have parentAdmitted := reading.existentialElimination_admitted distinct structural typing rules binding body result combinedFit active before scope sourceWindow existsProof childProof ruleAt bindingAt selected structuralSelected bindingSelected projection bounded existsProofTree (by
          have shape : Term.imp nextReading.logical.formula (HOL.rename (Rename.lift rho) (HOL.weaken result)) =
              .imp (.and (.and (HOL.weaken reading.logical.formula) .top) (HOL.rename (Rename.lift rho) body))
                (HOL.weaken (HOL.rename rho result)) := by
            simp only [nextReading, boundReading, ContextualReading.assume, ContextualReading.bind,
              Judgment.formula, Judgment.rename_formula, HOL.weaken, HOL.rename_comp]
            rfl
          rw [shape] at childProofTree
          exact childProofTree)
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.exE existential bodyProof) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @eqSymm gamma assumptions type first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq second first) := (ProofSyntax.eqSymm child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqSymm child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let parent := HOLKernelInferenceProofs.Native.symmetry signature rules (encodeType signature.symbol encoding.base type) environment.scope.logical _ _
          (encodeType_sorted signature _ encoding.base encoding.baseSorted type) environment.scope.logicalSorted
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .symmetry := (.symmetry reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .symmetry ([(encodeType signature.symbol encoding.base type), environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, readObjectWith, expect_same, reading.type_read distinct]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .symmetry [(encodeType signature.symbol encoding.base type), environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .symmetry) _ parent [childProof.val] rfl (1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (childProofTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqSymm child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqTrans gamma assumptions type first middle last left right leftIH rightIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq first last) := (ProofSyntax.eqTrans left right)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let leftProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding left environment (frame + 1) (by omega) leftBefore leftBudget
      obtain ⟨leftProofFuel, ⟨leftProofTree⟩⟩ := leftIH environment (frame + 1) (by omega) leftBefore leftBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let rightProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding right environment (frame + 1 + left.nodeCount) (by omega) rightBefore rightBudget
      obtain ⟨rightProofFuel, ⟨rightProofTree⟩⟩ := rightIH environment (frame + 1 + left.nodeCount) (by omega) rightBefore rightBudget
        rho names reading (scopeLater (frame + 1 + left.nodeCount) (by omega)) sourceWindow (boundedLater (frame + 1 + left.nodeCount) (by omega)) projection assumptionTrees
      let parent := HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical (encodeType signature.symbol encoding.base type) _ _ _
          environment.scope.logicalSorted (encodeType_sorted signature _ encoding.base encoding.baseSorted type)
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted middle middleFit active before)
          (environment.encoded_sorted last lastFit active before) leftProof rightProof
      let parentOperands : InferenceArguments Symbol target .transitivity := (.transitivity reading.logical.formula (HOL.rename rho first) (HOL.rename rho middle) (HOL.rename rho last))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .transitivity ([environment.scope.logical, (encodeType signature.symbol encoding.base type), (environment.encode first), (environment.encode middle), (environment.encode last)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, readObjectWith, expect_same, reading.type_read distinct]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .transitivity [environment.scope.logical, (encodeType signature.symbol encoding.base type), (environment.encode first), (environment.encode middle), (environment.encode last)] parentOperands parentParsed
        ruleAt bindingAt (selected .transitivity) _ parent [leftProof.val, rightProof.val] rfl (1 + leftProofFuel + rightProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (leftProofTree.weakenFuel (by omega)) (.cons (rightProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqTrans left right) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqPropI gamma assumptions first second forward backward forwardIH backwardIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq first second) := (ProofSyntax.eqPropI forward backward)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let forwardProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding forward environment (frame + 1) (by omega) forwardBefore forwardBudget
      obtain ⟨forwardProofFuel, ⟨forwardProofTree⟩⟩ := forwardIH environment (frame + 1) (by omega) forwardBefore forwardBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let backwardProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding backward environment (frame + 1 + forward.nodeCount) (by omega) backwardBefore backwardBudget
      obtain ⟨backwardProofFuel, ⟨backwardProofTree⟩⟩ := backwardIH environment (frame + 1 + forward.nodeCount) (by omega) backwardBefore backwardBudget
        rho names reading (scopeLater (frame + 1 + forward.nodeCount) (by omega)) sourceWindow (boundedLater (frame + 1 + forward.nodeCount) (by omega)) projection assumptionTrees
      let nativeParent := HOLKernelInferenceProofs.Native.propositionalExtensionality signature rules environment.scope.logical _ _
        environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
        forwardProof backwardProof
      let nativeParentOperands : InferenceArguments Symbol target .propositionalExtensionality := (.propositionalExtensionality reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have nativeParentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .propositionalExtensionality ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some nativeParentOperands := by simp [nativeParentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have nativeParentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .propositionalExtensionality [environment.scope.logical, (environment.encode first), (environment.encode second)] nativeParentOperands nativeParentParsed
        ruleAt bindingAt (selected .propositionalExtensionality) _ nativeParent [forwardProof.val, backwardProof.val] rfl (1 + forwardProofFuel + backwardProofFuel)
        (by simpa only [nativeParentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (forwardProofTree.weakenFuel (by omega)) (.cons (backwardProofTree.weakenFuel (by omega)) .nil)))
      obtain ⟨nativeTree⟩ := nativeParentAdmitted
      let parent := HOLKernelInferenceProofs.propositionalExtensionality signature abbreviation rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) forwardProof backwardProof
      have parentAdmitted := HOLKernelCongruenceReadback.expandProof_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
        names environment.scope.logical _ _ environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
        (environment.encoded_sorted second secondFit active before) nativeParent reading.logical (HOL.rename rho first) (HOL.rename rho second)
        reading.logical_read (reading.term_read distinct first) (reading.term_read distinct second) ruleAt bindingAt nativeTree
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqPropI forward backward) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout)) (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val (.imp reading.logical.formula (.eq (HOL.rename rho first) (HOL.rename rho second)))) from ⟨_, parentAdmitted⟩)
  | @eqPropEL gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.imp first second) := (ProofSyntax.eqPropEL child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqPropEL child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have raw := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at raw
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let contracted := HOLKernelBooleanEquality.contractProof signature abbreviation environment.scope.logical _ _
        environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof
      obtain ⟨contractedTree⟩ := HOLKernelCongruenceReadback.contractProof_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
        names environment.scope.logical _ _ environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
        (environment.encoded_sorted second secondFit active before) childProof reading.logical (HOL.rename rho first) (HOL.rename rho second)
        reading.logical_read (reading.term_read distinct first) (reading.term_read distinct second) ruleAt bindingAt
        (by simpa only [HOL.rename] using childProofTree)
      let parent := HOLKernelInferenceProofs.equalityImplicationLeft signature abbreviation rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .equalityImplicationLeft := (.equalityImplicationLeft reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .equalityImplicationLeft ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .equalityImplicationLeft [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .equalityImplicationLeft) _ parent [contracted.val] rfl (1 + childProofFuel + 1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (contractedTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqPropEL child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqPropER gamma assumptions first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.imp second first) := (ProofSyntax.eqPropER child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqPropER child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      have raw := child.conclusionBinderDepth_lt
      simp only [Term.binderDepth] at raw
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let contracted := HOLKernelBooleanEquality.contractProof signature abbreviation environment.scope.logical _ _
        environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before) childProof
      obtain ⟨contractedTree⟩ := HOLKernelCongruenceReadback.contractProof_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
        names environment.scope.logical _ _ environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
        (environment.encoded_sorted second secondFit active before) childProof reading.logical (HOL.rename rho first) (HOL.rename rho second)
        reading.logical_read (reading.term_read distinct first) (reading.term_read distinct second) ruleAt bindingAt
        (by simpa only [HOL.rename] using childProofTree)
      let parent := HOLKernelInferenceProofs.equalityImplicationRight signature abbreviation rules environment.scope.logical _ _
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .equalityImplicationRight := (.equalityImplicationRight reading.logical.formula (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .equalityImplicationRight ([environment.scope.logical, (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, expect_same]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .equalityImplicationRight [environment.scope.logical, (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .equalityImplicationRight) _ parent [contracted.val] rfl (1 + childProofFuel + 1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (contractedTree.weakenFuel (by omega)) .nil))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqPropER child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqApp gamma assumptions domain result first second argument child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq (.app first argument) (.app second argument)) := (ProofSyntax.eqApp argument child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqApp argument child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      have argumentFit : argument.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let argumentTyped := environment.typed structural typing argument argumentFit active before
      obtain ⟨argumentTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt argument argumentFit active before
      let parent := HOLKernelInferenceProofs.Native.applicationFunction signature rules
          (encodeType signature.symbol encoding.base domain) (encodeType signature.symbol encoding.base result) environment.scope.logical _ _ _
          (encodeType_sorted signature _ encoding.base encoding.baseSorted domain) (encodeType_sorted signature _ encoding.base encoding.baseSorted result)
          environment.scope.logicalSorted (environment.encoded_sorted argument argumentFit active before)
          (environment.encoded_sorted first firstFit active before) (environment.encoded_sorted second secondFit active before)
          childProof (environment.typed structural typing argument argumentFit active before)
      let parentOperands : InferenceArguments Symbol target .applicationFunction := (.applicationFunction reading.logical.formula (HOL.rename rho argument) (HOL.rename rho first) (HOL.rename rho second))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .applicationFunction ([(encodeType signature.symbol encoding.base domain), (encodeType signature.symbol encoding.base result), environment.scope.logical, (environment.encode argument), (environment.encode first), (environment.encode second)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, readObjectWith, expect_same, reading.type_read distinct]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .applicationFunction [(encodeType signature.symbol encoding.base domain), (encodeType signature.symbol encoding.base result), environment.scope.logical, (environment.encode argument), (environment.encode first), (environment.encode second)] parentOperands parentParsed
        ruleAt bindingAt (selected .applicationFunction) _ parent [childProof.val, argumentTyped.val] rfl (1 + childProofFuel + 1)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (childProofTree.weakenFuel (by omega)) (.cons (argumentTypedTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqApp argument child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @eqAppArg gamma assumptions domain result function first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq (.app function first) (.app function second)) := (ProofSyntax.eqAppArg function child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.eqAppArg function child)) child.binderBudget ≤ layout.width at budget
        omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      simp only [Term.binderDepth] at own
      have functionFit : function.binderDepth ≤ layout.width := by omega
      have firstFit : first.binderDepth ≤ layout.width := by omega
      have secondFit : second.binderDepth ≤ layout.width := by omega
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let functionTyped := environment.typed structural typing function functionFit active before
      obtain ⟨functionTypedTree⟩ := reading.typed_admitted distinct structural typing ruleAt bindingAt function functionFit active before
      let parent := HOLKernelInferenceProofs.Native.applicationArgument signature rules
          (encodeType signature.symbol encoding.base domain) (encodeType signature.symbol encoding.base result) environment.scope.logical _ _ _
          (encodeType_sorted signature _ encoding.base encoding.baseSorted domain) (encodeType_sorted signature _ encoding.base encoding.baseSorted result)
          environment.scope.logicalSorted (environment.encoded_sorted first firstFit active before)
          (environment.encoded_sorted second secondFit active before) (environment.encoded_sorted function functionFit active before)
          (environment.typed structural typing function functionFit active before) childProof
      let parentOperands : InferenceArguments Symbol target .applicationArgument := (.applicationArgument reading.logical.formula (HOL.rename rho first) (HOL.rename rho second) (HOL.rename rho function))
      have parentParsed : readInferenceArguments (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
          signature.symbol names .applicationArgument ([(encodeType signature.symbol encoding.base domain), (encodeType signature.symbol encoding.base result), environment.scope.logical, (environment.encode first), (environment.encode second), (environment.encode function)].map (expandEquivalence signature.symbol abbreviation.reference)) = some parentOperands := by simp [parentOperands, readInferenceArguments, List.map_cons, List.map_nil, reading.logical_read, reading.term_read distinct, readObjectWith, expect_same, reading.type_read distinct]
      have parentAdmitted := HOLKernelCongruenceReadback.checked_application_admitted signature abbreviation profile distinct
        HOLKernelSetOperationReadback.readConstant 7 rules names .applicationArgument [(encodeType signature.symbol encoding.base domain), (encodeType signature.symbol encoding.base result), environment.scope.logical, (environment.encode first), (environment.encode second), (environment.encode function)] parentOperands parentParsed
        ruleAt bindingAt (selected .applicationArgument) _ parent [functionTyped.val, childProof.val] rfl (1 + 1 + childProofFuel)
        (by simpa only [parentOperands, InferenceArguments.premises, HOL.rename, ContextualReading.assume, Judgment.formula] using (.cons (functionTypedTree.weakenFuel (by omega)) (.cons (childProofTree.weakenFuel (by omega)) .nil)))
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eqAppArg function child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename, InferenceArguments.conclusion, parentOperands] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems
        (HOLKernelEnvironmentReadback.NativeContext (signature := signature) (layout := layout))
        (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names parent.val
        parentOperands.conclusion) from ⟨_, parentAdmitted⟩)
  | @allE gamma assumptions domain body argument child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (instantiate argument body) := (ProofSyntax.allE argument child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.allE argument child)) child.binderBudget ≤ layout.width at budget
        omega
      have required := ProofSyntax.specialization_requirement_le argument child
      have fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width := by omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let parent := HOLKernelProofInstantiation.universalElimination abbreviation profile structural typing rules binding
          environment argument body fits active before childProof
      have parentAdmitted := reading.universalElimination_admitted distinct structural typing rules binding argument body fits active before childProof scope sourceWindow ruleAt bindingAt selected structuralSelected bindingSelected projection bounded childProofTree
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.allE argument child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @exI gamma assumptions domain body argument child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.ex body) := (ProofSyntax.exI (φ := body) argument child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      simp only [ProofSyntax.premiseMeasures, List.sum_cons, List.sum_nil, Nat.add_zero] at counts
      have childBudget : child.binderBudget ≤ layout.width := by
        change max (ProofSyntax.localBinderBudget (.exI argument child)) child.binderBudget ≤ layout.width at budget
        omega
      have required := ProofSyntax.existential_requirement_le argument child
      have fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width := by omega
      have nextBefore := before.trans (layout.workDepth_mono (show frame ≤ frame + 1 by omega))
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        rho names reading (scopeLater (frame + 1) (by omega)) sourceWindow (boundedLater (frame + 1) (by omega)) projection assumptionTrees
      let parent := HOLKernelProofInstantiation.existentialIntroduction abbreviation profile structural typing rules binding
          environment argument body fits active before childProof
      have parentAdmitted := reading.existentialIntroduction_admitted distinct structural typing rules binding argument body fits active before childProof scope sourceWindow ruleAt bindingAt selected structuralSelected bindingSelected projection bounded childProofTree
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.exI (φ := body) argument child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @beta gamma assumptions domain result argument body =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq (.app (.lam body) argument) (instantiate argument body)) := (ProofSyntax.beta (Δ := assumptions) argument body)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      have required := ProofSyntax.beta_requirement_le (Δ := assumptions) argument body
      have fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width := by omega
      let parent := HOLKernelProofInstantiation.beta abbreviation profile structural typing rules binding
        environment argument body fits active before
      have parentAdmitted := reading.beta_admitted distinct structural typing rules binding argument body fits active before scope sourceWindow ruleAt bindingAt selected structuralSelected bindingSelected projection
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.beta (Δ := assumptions) argument body) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @eta gamma assumptions domain result function =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq (.lam (.app (HOL.weaken function) (.var .vz))) function) := (ProofSyntax.eta (Δ := assumptions) function)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
      have required : function.binderDepth + 1 ≤ (ProofSyntax.eta (Δ := assumptions) function).localBinderBudget := Nat.le_max_right _ _
      have fits : function.binderDepth + 1 ≤ layout.width :=
        required.trans ((ProofSyntax.eta (Δ := assumptions) function).localBinderBudget_le.trans budget)
      let parent := HOLKernelProofExtensionality.eta profile structural typing rules binding environment function fits active before
      have parentAdmitted := reading.eta_admitted distinct structural typing rules binding function fits active before ruleAt bindingAt selected (structuralSelected .syl) bindingSelected projection
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.eta (Δ := assumptions) function) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted
  | @funExt gamma assumptions domain result first second child childIH =>
      intro depth environment frame space before budget target rho names reading scope sourceWindow bounded projection assumptionTrees
      let proof : ProofSyntax Symbol assumptions (.eq first second) := (ProofSyntax.funExt (f := first) (g := second) child)
      let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
      have active : frame < layout.frames := by have positive := proof.nodeCount_pos; dsimp only [proof] at positive; omega
      have counts := proof.nodeCount_eq_premiseSum
      have own := proof.conclusionBinderDepth_lt
      dsimp only [proof] at counts own
      have scopeLater (nextFrame : Nat) (later : frame ≤ nextFrame) : InScope 7 names (layout.workDepth nextFrame) := by
        refine ⟨scope.1, ?_⟩
        intro name member
        have bound := scope.2 name member
        have advance := layout.workDepth_mono later
        exact ⟨bound.1, by omega⟩
      have boundedLater (nextFrame : Nat) (later : frame ≤ nextFrame) : environment.ProofsVarsBelow (7 + layout.workDepth nextFrame) :=
        bounded.mono environment (Nat.add_le_add_left (layout.workDepth_mono later) 7)
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
      let argumentRoot := 7 + layout.temporaryDepth frame
      let nextNames : Names (domain :: target) := BinderNames.cons argumentRoot names
      have argumentScope := argument_frame_scope layout depth frame names domain scope before sourceWindow
      have rootAfter : 7 + layout.workDepth frame ≤ argumentRoot := by simp only [argumentRoot, Layout.temporaryDepth]; omega
      have rootAbove : 7 ≤ argumentRoot := by omega
      have rootAbsent : names.lookup? argumentRoot = none := by
        apply BinderNames.lookup?_none_of_not_mem
        intro member
        have h := (scope.2 _ member).2
        omega
      have dictionaryFresh : HOLKernelSetOperationReadback.readConstant argumentRoot = none := by
        dsimp only [argumentRoot]
        rw [Nat.add_comm]
        rfl
      let nextReading := reading.weaken domain argumentRoot rootAbove rootAbsent dictionaryFresh
      have within : layout.workDepth frame ≤ layout.limit := layout.workDepth_mono (Nat.le_of_lt active)
      have nextProjection := reading.weaken_projection_admitted ruleAt bindingAt projection (layout.workDepth frame) within bounded.projection domain argumentRoot rootAfter rootAbsent dictionaryFresh
      have nextAssumptions := reading.weaken_assumptions_admitted ruleAt bindingAt assumptionTrees (layout.workDepth frame) within bounded domain argumentRoot rootAfter rootAbsent dictionaryFresh
      let childProof := HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding child environment (frame + 1) (by omega) nextBefore childBudget
      obtain ⟨childProofFuel, ⟨childProofTree⟩⟩ := childIH environment (frame + 1) (by omega) nextBefore childBudget
        (fun index => Var.vs (rho index)) nextNames nextReading argumentScope.1 argumentScope.2.1 (boundedLater (frame + 1) (by omega)) nextProjection nextAssumptions
      let parent := HOLKernelProofExtensionality.functionExtensionality abbreviation profile structural typing rules binding
          environment first second fits active before childProof
      have parentAdmitted := reading.functionExtensionality_admitted distinct structural typing rules binding first second fits active before childProof scope ruleAt bindingAt selected structuralSelected bindingSelected projection bounded (by
          have shape : Term.imp nextReading.logical.formula
              (HOL.rename (fun index => Var.vs (rho index))
                (.all (.eq (.app (HOL.weaken first) (.var .vz)) (.app (HOL.weaken second) (.var .vz))))) =
              .imp (HOL.weaken (σ := domain) reading.logical.formula)
                (.all (.eq (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho first))) (.var .vz))
                  (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho second))) (.var .vz)))) := by
            simp only [nextReading, ContextualReading.weaken, ContextualReading.rename,
              Judgment.rename_formula, HOL.rename, HOL.weaken, HOL.rename_comp]
            rfl
          rw [shape] at childProofTree
          exact childProofTree)
      have witnessEq : (HOLKernelProofCompilation.compile abbreviation profile structural typing rules binding (ProofSyntax.funExt child) environment frame space before budget).val = parent.val := rfl
      rw [witnessEq]
      simpa only [HOL.rename] using parentAdmitted

#print axioms compile_admitted

open HOLKernelSetOperationProofReadback

/-- Every compiled closed material sequent is independently admitted, including
its formation antecedent and ordered assumption occurrences. -/
theorem closed_compile_admitted
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {assumptions : List (ClosedFormula Symbol)} {formula : ClosedFormula Symbol}
    (proof : ProofSyntax Symbol assumptions formula) :
    ∃ fuel, Nonempty (AdmittedSourceProof signature abbreviation theorems profile
      ((forProof proof).target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      ruleAt bindingAt fuel
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof).val
      (assumptions, formula)) := by
  let layout := forProof proof
  let bounds := fun source member => proof.assumptionBinderDepth_lt source member
  let environment := initialEnvironment (definitions := definitions) signature layout structural assumptions bounds
  let reading := initialReading abbreviation profile distinct layout structural assumptions bounds
  have projection := reading.contextual_projection ruleAt bindingAt
    (initial_projection_admitted abbreviation profile distinct layout structural ruleAt bindingAt structuralSelected assumptions bounds)
  have assumptionTrees := reading.contextual_assumptions ruleAt bindingAt
    (initial_assumptions_admitted abbreviation profile distinct layout structural ruleAt bindingAt structuralSelected assumptions bounds)
  have bounded : environment.ProofsVarsBelow (7 + layout.workDepth 0) := by
    simpa only [environment, Layout.workDepth, Nat.zero_mul, Nat.add_zero] using
      initial_proofs_varsBelow (definitions := definitions) signature layout structural assumptions bounds
  obtain ⟨fuel, ⟨tree⟩⟩ := compile_admitted abbreviation profile distinct structural typing rules binding
    ruleAt bindingAt selected structuralSelected bindingSelected proof environment 0
    (by change 0 + proof.nodeCount ≤ proof.nodeCount; omega)
    (by simp [Layout.workDepth]) (Nat.le_refl _) Rename.id BinderNames.nil reading.contextual
    (by simp [InScope, BinderNames.toList])
    (by simp [BinderNames.toList]) bounded projection assumptionTrees
  refine ⟨fuel, ⟨{
    contextReading := sourceContext assumptions
    antecedent_read := read_sourceAntecedent profile abbreviation distinct assumptions
    context_admitted := sourceContext_admitted assumptions
    native_accepted := (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mpr
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof).property
    proof_admitted := ?_ }⟩⟩
  have shape : Term.imp reading.contextual.logical.formula (HOL.rename Rename.id formula) =
      Term.imp (sourceContext assumptions).formula formula := by rw [rename_id]; rfl
  rw [shape] at tree
  exact tree

/-- Existence of an independently admitted certificate is equivalent to source
HOL derivability, under the stated native schema and reader policy. -/
theorem admitted_certificate_iff_derivable
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (assumptions : List (ClosedFormula Symbol)) (formula : ClosedFormula Symbol) :
    (∃ (context : Context) (fuel : Nat) (witness : ProofWitness),
      Nonempty (AdmittedSourceProof signature abbreviation theorems profile context
        ruleAt bindingAt fuel witness (assumptions, formula))) ↔
      ExtDerivation Symbol assumptions formula := by
  constructor
  · rintro ⟨context, fuel, witness, ⟨admitted⟩⟩
    exact admitted_source_derivation signature abbreviation theorems profile context ruleAt bindingAt
      fuel witness assumptions formula admitted
  · intro derived
    obtain ⟨proof⟩ := ProofSyntax.nonempty_of_derivation derived
    obtain ⟨fuel, admitted⟩ := closed_compile_admitted abbreviation profile distinct structural typing rules binding
      ruleAt bindingAt selected structuralSelected bindingSelected proof
    exact ⟨_, fuel, _, admitted⟩

/-- Every compiled source proof is in the executable reader's successful domain,
with its original ordered assumptions and conclusion. -/
theorem closed_compile_readback
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {assumptions : List (ClosedFormula Symbol)} {formula : ClosedFormula Symbol}
    (proof : ProofSyntax Symbol assumptions formula) :
    ∃ fuel, ∃ out : SourceProofReadback abbreviation theorems
      ((forProof proof).target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof).val,
      readSourceProof signature abbreviation theorems profile _ ruleAt bindingAt fuel
        (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof).val = some out ∧
      out.sequent = (assumptions, formula) := by
  obtain ⟨fuel, ⟨admitted⟩⟩ := closed_compile_admitted abbreviation profile distinct structural typing rules binding
    ruleAt bindingAt selected structuralSelected bindingSelected proof
  exact ⟨fuel, readSourceProof_of_admitted signature abbreviation theorems profile _ ruleAt bindingAt
    fuel _ (assumptions, formula) admitted⟩

#print axioms admitted_certificate_iff_derivable
#print axioms closed_compile_readback

#print axioms closed_compile_admitted

end Mettapedia.Languages.MM0.HOLKernelProofCompilationReadback
