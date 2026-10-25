import Mettapedia.Languages.MM0.HOLKernelAlpha

/-!
# Checked comparison of source and native HOL substitution

For every intrinsic HOL term, the compiler constructs an object-equality proof
between literal insertion of encoded substitution images and encoding the
source-substituted term. The finite name budget is the source binder depth
plus the maximum image depth. Public and temporary windows retain their actual
bound-slot lookups, context independence and disjointness.

Binding cases first prove image-rebinding equations in the preceding context,
then weaken them into the extended context. Pointwise assignment congruence
and the recursive source-substitution comparison construct the body equation.
The result is a checked equality witness; the raw encodings may differ.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSubstitution
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelTypeSupport
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

def compile (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ {delta : Ctx Base} (substitution : Subst Const gamma delta) (assignment : Assignment delta)
      (depth temporaryDepth : Nat) (antecedent : Preterm),
      Preterm.HasType terms context antecedent [] signature.ids.wff →
      (∀ {type} (index : Var delta type),
        Preterm.HasType terms context (assignment index) [] signature.ids.object) →
      (∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
        context[binders (depth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
        context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
        ¬ Preterm.HasVar context (binders (depth + offset)) antecedent) →
      (∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
        ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent) →
      (∀ firstOffset < source.binderDepth + Subst.maxBinderDepth substitution,
        ∀ secondOffset < source.binderDepth + Subst.maxBinderDepth substitution,
          binders (depth + firstOffset) ≠ temporary (temporaryDepth + secondOffset)) →
      (∀ {type} (index : Var delta type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type))) →
      (∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) →
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (entails signature.symbol antecedent (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base type)
            (encodeWithAssignment signature.symbol base constant binders
              (encodeSubstitution signature.symbol base constant binders assignment depth substitution) depth source)
            (encodeWithAssignment signature.symbol base constant binders assignment depth (subst substitution source))))) := by
  match source with
  | .var index =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted _)
        ((encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted
          substitution assignment depth assignmentSorted (fun offset smaller => slots offset (by simpa only [Term.binderDepth, Nat.zero_add] using smaller))) index)
        ((HOLKernelTermTyping.substitutionTyping signature structural typing base constant binders baseSorted
          constantSorted bindersInjective baseIndependent substitution assignment depth antecedent antecedentSorted
          assignmentSorted (fun offset smaller => slots offset (by simpa only [Term.binderDepth, Nat.zero_add] using smaller))
          (fun offset smaller => fresh offset (by simpa only [Term.binderDepth, Nat.zero_add] using smaller))
          variableTyping constantTyping) index)
  | .const symbol =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (constantSorted symbol) (constantTyping symbol)
  | .top =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (signature.application context .bool [] .nil) (signature.application context .truth [] .nil)
        (HOLKernelTypingProofs.truthTyping signature typing antecedent antecedentSorted)
  | .bot =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (signature.application context .bool [] .nil) (signature.application context .falsity [] .nil)
        (HOLKernelTypingProofs.falsityTyping signature typing antecedent antecedentSorted)
  | .app first second | .and first second | .or first second | .imp first second =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
          max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
        Nat.add_le_add_right (Nat.le_max_left _ _) _
      have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
        disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
          secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
      have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
        constantSorted first substitution assignment depth assignmentSorted firstSlots
      let firstProof := compile signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
        firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
          max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
        Nat.add_le_add_right (Nat.le_max_right _ _) _
      have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
        disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
          secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
      have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
        constantSorted second substitution assignment depth assignmentSorted secondSlots
      let secondProof := compile signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
        secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      first
      | exact HOLKernelCongruence.application signature rules binding antecedent _ _ _ _ _ _
          antecedentSorted (encodeType_sorted signature context base baseSorted _)
          (encodeType_sorted signature context base baseSorted _) firstSorted.1 firstSorted.2
          secondSorted.1 secondSorted.2 firstProof secondProof
      | exact HOLKernelCongruence.conjunctionCongruence signature profile rules binding antecedent _ _ _ _
          antecedentSorted firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof
      | exact HOLKernelCongruence.disjunctionCongruence signature profile rules binding antecedent _ _ _ _
          antecedentSorted firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof
      | exact HOLKernelCongruence.implicationCongruence signature profile rules binding antecedent _ _ _ _
          antecedentSorted firstSorted.1 firstSorted.2 secondSorted.1 secondSorted.2 firstProof secondProof
  | .not body =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      have formed := substitution_encodings_sorted signature context base constant binders baseSorted constantSorted
        body substitution assignment depth assignmentSorted slots
      exact HOLKernelCongruence.negationCongruence signature profile rules antecedent _ _ antecedentSorted formed.1 formed.2
        (compile signature profile structural typing rules binding base constant binders temporary baseSorted constantSorted
          bindersInjective temporaryInjective baseIndependent temporaryIndependent body substitution assignment depth
          temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint
          variableTyping constantTyping)
  | .eq (τ := type) first second =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      have firstBudget : first.binderDepth + Subst.maxBinderDepth substitution ≤
          max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
        Nat.add_le_add_right (Nat.le_max_left _ _) _
      have firstSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller firstBudget)
      have firstDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
        disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller firstBudget)
          secondOffset (Nat.lt_of_lt_of_le secondSmaller firstBudget)
      have firstSorted := substitution_encodings_sorted signature context base constant binders baseSorted
        constantSorted first substitution assignment depth assignmentSorted firstSlots
      let firstProof := compile signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        first substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
        firstSlots firstTemporarySlots firstFresh firstTemporaryFresh firstDisjoint variableTyping constantTyping
      have secondBudget : second.binderDepth + Subst.maxBinderDepth substitution ≤
          max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution :=
        Nat.add_le_add_right (Nat.le_max_right _ _) _
      have secondSlots := fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondTemporarySlots := fun offset smaller => temporarySlots offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondFresh := fun offset smaller => fresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondTemporaryFresh := fun offset smaller => temporaryFresh offset (Nat.lt_of_lt_of_le smaller secondBudget)
      have secondDisjoint := fun firstOffset firstSmaller secondOffset secondSmaller =>
        disjoint firstOffset (Nat.lt_of_lt_of_le firstSmaller secondBudget)
          secondOffset (Nat.lt_of_lt_of_le secondSmaller secondBudget)
      have secondSorted := substitution_encodings_sorted signature context base constant binders baseSorted
        constantSorted second substitution assignment depth assignmentSorted secondSlots
      let secondProof := compile signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
        second substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted
        secondSlots secondTemporarySlots secondFresh secondTemporaryFresh secondDisjoint variableTyping constantTyping
      exact HOLKernelCongruence.equalityCongruence signature profile rules binding antecedent
        (encodeType signature.symbol base type) _ _ _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted type) firstSorted.1 firstSorted.2
        secondSorted.1 secondSorted.2 firstProof secondProof
  | .lam (σ := domain) body | .all (σ := domain) body | .ex (σ := domain) body =>
      intro delta substitution assignment depth temporaryDepth antecedent antecedentSorted assignmentSorted slots temporarySlots fresh temporaryFresh disjoint variableTyping constantTyping
      simp only [Term.binderDepth] at slots temporarySlots fresh temporaryFresh disjoint
      have head : context[binders depth]? = some (.bound signature.ids.object) := by
        have found := slots 0 (by omega)
        simpa only [Nat.add_zero] using found
      have domainSorted := encodeType_sorted signature context base baseSorted domain
      have headSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) head
      let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
      let extended := conjunction signature.symbol antecedent extra
      have extraSorted := hasType_sorted signature context headSorted domainSorted
      have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
      have bodySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
          context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        rw [Subst.maxBinderDepth_lift] at smaller
        have found := slots (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have bodyTemporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
          context[temporary (temporaryDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        rw [Subst.maxBinderDepth_lift] at smaller
        have found := temporarySlots (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have bodyFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
          ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
        intro offset smaller
        rw [Subst.maxBinderDepth_lift] at smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
        · intro same
          have impossible := bindersInjective same
          omega
        · have independent := fresh (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent
        · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
      have bodyTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
          ¬ Preterm.HasVar context (temporary (temporaryDepth + 1 + offset)) extended := by
        intro offset smaller
        rw [Subst.maxBinderDepth_lift] at smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
        · have apart := Ne.symm (disjoint 0 (by omega) (offset + 1) (by omega))
          simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using apart
        · have independent := temporaryFresh (offset + 1) (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent
        · exact encodeType_independent context _ signature.symbol base (temporaryIndependent _) domain
      have bodyDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
          ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.lift (σ := domain) substitution),
            binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + 1 + secondOffset) := by
        intro firstOffset firstSmaller secondOffset secondSmaller
        rw [Subst.maxBinderDepth_lift] at firstSmaller secondSmaller
        have apart := disjoint (firstOffset + 1) (by omega) (secondOffset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 firstOffset, Nat.add_comm 1 secondOffset] using apart
      have extendedTargetSorted : ∀ {type} (index : Var (domain :: delta) type),
          Preterm.HasType terms context (Assignment.extend (.var (binders depth)) assignment index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
      have extendedVariables : ∀ {type} (index : Var (domain :: delta) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol extended (Assignment.extend (.var (binders depth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted
        | vs index =>
            exact (HOLKernelTermTyping.weakenVariables signature structural base assignment antecedent extra
              antecedentSorted extraSorted baseSorted assignmentSorted variableTyping) index
      have extendedConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
        HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
          antecedentSorted extraSorted baseSorted constantSorted constantTyping
      have leftImages : ∀ {type} (index : Var gamma type),
          Preterm.HasType terms context
            (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
            [] signature.ids.object :=
        encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted substitution
          assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
      have rightImages : ∀ {type} (index : Var gamma type),
          Preterm.HasType terms context
            (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution index)
            [] signature.ids.object := by
        apply encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted substitution
          assignment (depth + 1) assignmentSorted
        intro offset smaller
        have found := slots (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have imageEquations : ∀ {type} (index : Var gamma type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (entails signature.symbol extended (holds signature.symbol
              (equality signature.symbol (encodeType signature.symbol base type)
                (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
                (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution index)))) := by
        intro type index
        have heightBound := Subst.binderDepth_le_maxBinderDepth substitution index
        let renamed := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
          baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
          (substitution index) assignment depth (depth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
          (fun offset smaller => slots offset (by omega))
          (by
            intro offset smaller
            have found := slots (offset + 1) (by omega)
            simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
          (fun offset smaller => temporarySlots offset (by omega))
          (fun offset smaller => fresh offset (by omega))
          (by
            intro offset smaller
            have independent := fresh (offset + 1) (by omega)
            simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
          (fun offset smaller => temporaryFresh offset (by omega))
          (by intro first firstSmaller second secondSmaller; exact disjoint first (by omega) second (by omega))
          (by
            intro first firstSmaller second secondSmaller
            have apart := Ne.symm (disjoint (second + 1) (by omega) first (by omega))
            simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
          variableTyping constantTyping
        exact HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
          (holds_sorted signature context (signature.application context .eqc _
            (.cons (.regular (encodeType_sorted signature context base baseSorted type))
              (.cons (.regular (leftImages index)) (.cons (.regular (rightImages index)) .nil))))) renamed
      let leftAssignment : Assignment (domain :: gamma) := Assignment.extend (.var (binders depth))
        (encodeSubstitution signature.symbol base constant binders assignment depth substitution)
      let rightAssignment : Assignment (domain :: gamma) := Assignment.extend (.var (binders depth))
        (encodeSubstitution signature.symbol base constant binders assignment (depth + 1) substitution)
      have leftAssignmentSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (leftAssignment index) [] signature.ids.object :=
        Assignment.extend_sorted signature context _ _ headSorted leftImages
      have rightAssignmentSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (rightAssignment index) [] signature.ids.object :=
        Assignment.extend_sorted signature context _ _ headSorted rightImages
      have related : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (entails signature.symbol extended (holds signature.symbol
              (equality signature.symbol (encodeType signature.symbol base type)
                (leftAssignment index) (rightAssignment index)))) := by
        intro type index
        cases index with
        | vz =>
            exact HOLKernelInferenceProofs.Native.reflexivity signature rules extended _ _ extendedSorted
              domainSorted headSorted
              (HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted)
        | vs index => exact imageEquations index
      let assignmentComparison := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
        base constant binders baseSorted constantSorted bindersInjective baseIndependent body
        leftAssignment rightAssignment (depth + 1) extended extendedSorted leftAssignmentSorted rightAssignmentSorted
        (fun offset smaller => bodySlots offset (by omega))
        (fun offset smaller => bodyFresh offset (by omega)) related extendedConstants
      have substitutionComparison := compile signature profile structural typing rules binding base constant binders temporary
        baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent body
        (Subst.lift substitution) (Assignment.extend (.var (binders depth)) assignment)
        (depth + 1) (temporaryDepth + 1) extended extendedSorted extendedTargetSorted
        bodySlots bodyTemporarySlots bodyFresh bodyTemporaryFresh bodyDisjoint extendedVariables extendedConstants
      simp only [encodeSubstitution_lift] at substitutionComparison
      have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body
        leftAssignment (depth + 1) leftAssignmentSorted (fun offset smaller => bodySlots offset (by omega))
      have middleBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body
        rightAssignment (depth + 1) rightAssignmentSorted (fun offset smaller => bodySlots offset (by omega))
      have rightBodySorted := (substitution_encodings_sorted signature context base constant binders baseSorted constantSorted
        body (Subst.lift substitution) (Assignment.extend (.var (binders depth)) assignment) (depth + 1)
        extendedTargetSorted bodySlots).2
      let bodyEquality := HOLKernelInferenceProofs.Native.transitivity signature rules extended _ _ _ _
        extendedSorted (encodeType_sorted signature context base baseSorted _) leftBodySorted middleBodySorted
        rightBodySorted assignmentComparison substitutionComparison
      have abstractionEquality := HOLKernelBindingProofs.Native.abstractionCongruence signature binding
        antecedent (encodeType signature.symbol base domain) _ (binders depth) _ _ antecedentSorted domainSorted
        (encodeType_sorted signature context base baseSorted _) head leftBodySorted rightBodySorted
        (by simpa only [Nat.add_zero] using fresh 0 (by omega))
        (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependent depth) _) bodyEquality
      first
      | exact abstractionEquality
      | exact HOLKernelCongruence.universalCongruence signature profile rules antecedent _ _ _
          (binders depth) (binders depth) antecedentSorted domainSorted head head
          leftBodySorted rightBodySorted abstractionEquality
      | exact HOLKernelCongruence.existentialCongruence signature profile rules antecedent _ _ _
          (binders depth) (binders depth) antecedentSorted domainSorted head head
          leftBodySorted rightBodySorted abstractionEquality
termination_by structural source

def instanceEquation (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (depth temporaryDepth boundIndex : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var boundIndex) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var boundIndex) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment depth argument))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
          (.var boundIndex) argumentCode)))
        (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base result)
          (encodeWithAssignment signature.symbol base constant binders
            (Assignment.extend (.var boundIndex) assignment) depth body)
          (encodeWithAssignment signature.symbol base constant binders assignment depth (instantiate argument body))))) := by
  let extra := holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
    (.var boundIndex) argumentCode)
  let extended := conjunction signature.symbol antecedent extra
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have resultSorted := encodeType_sorted signature context base baseSorted result
  have variableSorted : Preterm.HasType terms context (.var boundIndex) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) bound
  have extraSorted := holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular domainSorted) (.cons (.regular variableSorted) (.cons (.regular argumentSorted) .nil))))
  have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) :=
    Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have encodedArgumentSorted := encode_sorted signature context base constant binders baseSorted constantSorted
    argument assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
  let relation := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
    signature structural antecedent extra antecedentSorted extraSorted
  let argumentEquationUnder := HOLKernelStructuralRules.weaken signature structural antecedent extra _
    antecedentSorted extraSorted (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular domainSorted) (.cons (.regular argumentSorted) (.cons (.regular encodedArgumentSorted) .nil)))))
    argumentEquation
  let relatedHead := HOLKernelInferenceProofs.Native.transitivity signature rules extended _ _ _ _
    extendedSorted domainSorted variableSorted argumentSorted encodedArgumentSorted relation argumentEquationUnder
  have leftSorted : ∀ {type} (index : Var (domain :: gamma) type),
      Preterm.HasType terms context (Assignment.extend (.var boundIndex) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment variableSorted assignmentSorted
  have rightSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index)
      [] signature.ids.object :=
    encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted
      (Subst.single argument) assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
  have related : ∀ {type} (index : Var (domain :: gamma) type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (entails signature.symbol extended (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base type)
            (Assignment.extend (.var boundIndex) assignment index)
            (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument) index)))) := by
    intro type index
    cases index with
    | vz => exact relatedHead
    | vs index =>
        exact HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
          (holds_sorted signature context (signature.application context .eqc _
            (.cons (.regular (encodeType_sorted signature context base baseSorted type))
              (.cons (.regular (assignmentSorted index)) (.cons (.regular (assignmentSorted index)) .nil)))))
          (HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
            (encodeType_sorted signature context base baseSorted type) (assignmentSorted index) (variableTyping index))
  have extendedVariables : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol extended (assignment index) (encodeType signature.symbol base type)) :=
    HOLKernelTermTyping.weakenVariables signature structural base assignment antecedent extra
      antecedentSorted extraSorted baseSorted assignmentSorted variableTyping
  have extendedConstants : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
    HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
      antecedentSorted extraSorted baseSorted constantSorted constantTyping
  let compareAssignments := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
    base constant binders baseSorted constantSorted bindersInjective baseIndependent body
    (Assignment.extend (.var boundIndex) assignment)
    (encodeSubstitution signature.symbol base constant binders assignment depth (Subst.single argument))
    depth extended extendedSorted leftSorted rightSorted (fun offset smaller => slots offset (by omega))
    (fun offset smaller => fresh offset (by omega)) related extendedConstants
  let compareSubstitution := compile signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    body (Subst.single argument) assignment depth temporaryDepth extended extendedSorted assignmentSorted
    slots temporarySlots fresh temporaryFresh disjoint extendedVariables extendedConstants
  have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
    body _ depth leftSorted (fun offset smaller => slots offset (by omega))
  have bothSorted := substitution_encodings_sorted signature context base constant binders baseSorted constantSorted
    body (Subst.single argument) assignment depth assignmentSorted slots
  exact HOLKernelInferenceProofs.Native.transitivity signature rules extended _ _ _ _ extendedSorted resultSorted
    leftBodySorted bothSorted.1 bothSorted.2 compareAssignments compareSubstitution


#print axioms compile
#print axioms instanceEquation
end Mettapedia.Languages.MM0.HOLKernelSubstitution
