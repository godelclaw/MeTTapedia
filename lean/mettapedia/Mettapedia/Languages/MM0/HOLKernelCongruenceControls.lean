import Mettapedia.Languages.MM0.HOLKernelCongruence
import Mettapedia.Languages.MM0.HOLKernelTermCongruence

/-!
# Dependent-body alpha-renaming through maintained HOL logical constructors

Two identity abstractions with distinct bound names are equated using the
actual change-of-variable theorem and constructed context projections. Their
quantifications are then transported through every logical constructor.
The final proof has no external logical hypotheses. Both dependent bodies and
both bound names remain in the submitted native syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelCongruenceControls

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {equivalenceReference : Nat}

def base (references : Symbol → Nat) : Preterm :=
  holds references (applySymbol references .truth [])

def identityAt (references : Symbol → Nat) (bound : Nat) : Preterm :=
  applySymbol references .lam [.var bound, boolType references, .var bound]

def identityRenaming (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := [.bound signature.ids.object, .bound signature.ids.object]) (hypotheses := [])
      (entails signature.symbol (base signature.symbol) (holds signature.symbol
        (equality signature.symbol (functionType signature.symbol
          (boolType signature.symbol) (boolType signature.symbol))
          (identityAt signature.symbol 0) (identityAt signature.symbol 1)))) := by
  let context : Context := [.bound signature.ids.object, .bound signature.ids.object]
  let bool := boolType signature.symbol
  let antecedent := base signature.symbol
  have boolSorted : Preterm.HasType terms context bool [] signature.ids.type :=
    signature.application context .bool [] .nil
  have antecedentSorted := holds_sorted signature context (signature.application context .truth [] .nil)
  have firstSorted : Preterm.HasType terms context (.var 0) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) rfl
  have secondSorted : Preterm.HasType terms context (.var 1) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) rfl
  have firstTypeSorted := hasType_sorted signature context firstSorted boolSorted
  have secondTypeSorted := hasType_sorted signature context secondSorted boolSorted
  have equalitySorted := holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular boolSorted) (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil))))
  let firstTyping := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature structural antecedent (hasType signature.symbol (.var 0) bool)
    antecedentSorted firstTypeSorted
  let secondTyping := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature structural antecedent (hasType signature.symbol (.var 1) bool)
    antecedentSorted secondTypeSorted
  let bodiesEqual := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature structural antecedent (holds signature.symbol (equality signature.symbol bool (.var 0) (.var 1)))
    antecedentSorted equalitySorted
  have boolIndependent (index : Nat) : ¬ Preterm.HasVar context index bool := by
    simp [bool, boolType, applySymbol, Preterm.applyArgs]
  have antecedentIndependent (index : Nat) : ¬ Preterm.HasVar context index antecedent := by
    simp [antecedent, base, holds, applySymbol, Preterm.applyArgs, Preterm.hasVar_app_iff]
  exact HOLKernelBindingProofs.Native.abstractionRenaming signature binding bool bool antecedent 0 1
    (.var 0) (.var 1) boolSorted boolSorted antecedentSorted rfl rfl firstSorted secondSorted
    (boolIndependent 0) (boolIndependent 0) (antecedentIndependent 0)
    (boolIndependent 1) (boolIndependent 1) (antecedentIndependent 1) (by decide)
    firstTyping secondTyping bodiesEqual

theorem identity_presentations_distinct (references : Symbol → Nat) :
    identityAt references 0 ≠ identityAt references 1 := by
  simp [identityAt, applySymbol, boolType, Preterm.applyArgs]

def universalAt (references : Symbol → Nat) (bound : Nat) : Preterm :=
  applySymbol references .allc [.var bound, boolType references, .var bound]

def existentialAt (references : Symbol → Nat) (bound : Nat) : Preterm :=
  applySymbol references .exc [.var bound, boolType references, .var bound]

def formulaAt (references : Symbol → Nat) (bound : Nat) : Preterm :=
  let universal := universalAt references bound
  let existential := existentialAt references bound
  let conjunction := applySymbol references .andc [universal, existential]
  let disjunction := applySymbol references .orc [existential, universal]
  let implication := applySymbol references .impc [conjunction, disjunction]
  let negation := applySymbol references .notc [implication]
  equality references (boolType references) negation universal

def nestedLogicalRenaming (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := [.bound signature.ids.object, .bound signature.ids.object]) (hypotheses := [])
      (entails signature.symbol (base signature.symbol) (holds signature.symbol
        (equality signature.symbol (boolType signature.symbol)
          (formulaAt signature.symbol 0) (formulaAt signature.symbol 1)))) := by
  let context : Context := [.bound signature.ids.object, .bound signature.ids.object]
  let bool := boolType signature.symbol
  let antecedent := base signature.symbol
  have boolSorted : Preterm.HasType terms context bool [] signature.ids.type :=
    signature.application context .bool [] .nil
  have antecedentSorted := holds_sorted signature context (signature.application context .truth [] .nil)
  have firstSorted : Preterm.HasType terms context (.var 0) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) rfl
  have secondSorted : Preterm.HasType terms context (.var 1) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) rfl
  let abstractions := identityRenaming (definitions := definitions) signature structural binding
  let universals := HOLKernelCongruence.universalCongruence signature profile rules antecedent bool
    (.var 0) (.var 1) 0 1 antecedentSorted boolSorted rfl rfl firstSorted secondSorted abstractions
  let existentials := HOLKernelCongruence.existentialCongruence signature profile rules antecedent bool
    (.var 0) (.var 1) 0 1 antecedentSorted boolSorted rfl rfl firstSorted secondSorted abstractions
  have universalSorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :
      Preterm.HasType terms context (universalAt signature.symbol index) [] signature.ids.object :=
    signature.application context .allc _ (.cons (.bound bound) (.cons (.regular boolSorted)
      (.cons (.regular (.var (binder := .bound signature.ids.object) bound)) .nil)))
  have existentialSorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :
      Preterm.HasType terms context (existentialAt signature.symbol index) [] signature.ids.object :=
    signature.application context .exc _ (.cons (.bound bound) (.cons (.regular boolSorted)
      (.cons (.regular (.var (binder := .bound signature.ids.object) bound)) .nil)))
  let firstAll := universalAt signature.symbol 0
  let secondAll := universalAt signature.symbol 1
  let firstEx := existentialAt signature.symbol 0
  let secondEx := existentialAt signature.symbol 1
  let conjunctions := HOLKernelCongruence.conjunctionCongruence signature profile rules binding antecedent
    firstAll secondAll firstEx secondEx antecedentSorted
    (universalSorted 0 rfl) (universalSorted 1 rfl) (existentialSorted 0 rfl) (existentialSorted 1 rfl)
    universals existentials
  let disjunctions := HOLKernelCongruence.disjunctionCongruence signature profile rules binding antecedent
    firstEx secondEx firstAll secondAll antecedentSorted
    (existentialSorted 0 rfl) (existentialSorted 1 rfl) (universalSorted 0 rfl) (universalSorted 1 rfl)
    existentials universals
  have conjunctionSorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :=
    signature.application context .andc [universalAt signature.symbol index, existentialAt signature.symbol index]
      (.cons (.regular (universalSorted index bound)) (.cons (.regular (existentialSorted index bound)) .nil))
  have disjunctionSorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :=
    signature.application context .orc [existentialAt signature.symbol index, universalAt signature.symbol index]
      (.cons (.regular (existentialSorted index bound)) (.cons (.regular (universalSorted index bound)) .nil))
  let implications := HOLKernelCongruence.implicationCongruence signature profile rules binding antecedent _ _ _ _
    antecedentSorted (conjunctionSorted 0 rfl) (conjunctionSorted 1 rfl)
    (disjunctionSorted 0 rfl) (disjunctionSorted 1 rfl) conjunctions disjunctions
  have implicationSorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :=
    signature.application context .impc _ (.cons (.regular (conjunctionSorted index bound))
      (.cons (.regular (disjunctionSorted index bound)) .nil))
  let negations := HOLKernelCongruence.negationCongruence signature profile rules antecedent _ _
    antecedentSorted (implicationSorted 0 rfl) (implicationSorted 1 rfl) implications
  have negationSorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :=
    signature.application context .notc _ (.cons (.regular (implicationSorted index bound)) .nil)
  exact HOLKernelCongruence.equalityCongruence signature profile rules binding antecedent bool _ _ _ _
    antecedentSorted boolSorted (negationSorted 0 rfl) (negationSorted 1 rfl)
    (universalSorted 0 rfl) (universalSorted 1 rfl) negations universals

open HOLKernelTermAssignments

def closedArgumentSubstitution (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference) :
    let baseCode := fun (_ : Unit) => boolType signature.symbol
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := [.bound signature.ids.object, .bound signature.ids.object]) (hypotheses := [])
      (entails signature.symbol (base signature.symbol) (holds signature.symbol
        (equality signature.symbol (functionType signature.symbol (boolType signature.symbol)
          (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))
          (encodeWithAssignment signature.symbol baseCode SubstitutionControl.noConstants id
            (Assignment.extend
              (encodeWithAssignment signature.symbol baseCode SubstitutionControl.noConstants id
                SubstitutionControl.noAssignment 0 SubstitutionControl.argument)
              SubstitutionControl.noAssignment) 0 SubstitutionControl.body)
          (encodeWithAssignment signature.symbol baseCode SubstitutionControl.noConstants id
            SubstitutionControl.noAssignment 0
            (Mettapedia.Logic.HOL.instantiate SubstitutionControl.argument SubstitutionControl.body))))) := by
  let context : Context := [.bound signature.ids.object, .bound signature.ids.object]
  let bool := boolType signature.symbol
  let baseCode := fun (_ : Unit) => bool
  let left : Assignment ([.arr .prop .prop] : Mettapedia.Logic.HOL.Ctx Unit) :=
    Assignment.extend (identityAt signature.symbol 0) SubstitutionControl.noAssignment
  let right : Assignment ([.arr .prop .prop] : Mettapedia.Logic.HOL.Ctx Unit) :=
    Assignment.extend (identityAt signature.symbol 1) SubstitutionControl.noAssignment
  have boolSorted : Preterm.HasType terms context bool [] signature.ids.type :=
    signature.application context .bool [] .nil
  have identitySorted (index : Nat) (bound : context[index]? = some (.bound signature.ids.object)) :
      Preterm.HasType terms context (identityAt signature.symbol index) [] signature.ids.object :=
    signature.application context .lam _ (.cons (.bound bound) (.cons (.regular boolSorted)
      (.cons (.regular (.var (binder := .bound signature.ids.object) bound)) .nil)))
  have leftSorted : ∀ {type} (index : Mettapedia.Logic.HOL.Var [.arr .prop .prop] type),
      Preterm.HasType terms context (left index) [] signature.ids.object := by
    intro type index
    cases index with
    | vz => exact identitySorted 0 rfl
    | vs index => nomatch index
  have rightSorted : ∀ {type} (index : Mettapedia.Logic.HOL.Var [.arr .prop .prop] type),
      Preterm.HasType terms context (right index) [] signature.ids.object := by
    intro type index
    cases index with
    | vz => exact identitySorted 1 rfl
    | vs index => nomatch index
  have leaves : ∀ {type} (index : Mettapedia.Logic.HOL.Var [.arr .prop .prop] type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := [])
        (entails signature.symbol (base signature.symbol) (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol baseCode type) (left index) (right index)))) := by
    intro type index
    cases index with
    | vz => exact identityRenaming signature structural binding
    | vs index => nomatch index
  let proof := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
    baseCode SubstitutionControl.noConstants id (fun _ => boolSorted)
    (fun symbol => nomatch symbol) (fun _ _ same => same)
    (by intro slot index; simp [baseCode, bool, boolType, applySymbol, Preterm.applyArgs])
    SubstitutionControl.body left right 0 (base signature.symbol)
    (holds_sorted signature context (signature.application context .truth [] .nil))
    leftSorted rightSorted
    (by intro offset smaller; have zero : offset = 0 := by
          simpa [SubstitutionControl.body, Mettapedia.Logic.HOL.Term.binderDepth] using smaller
        subst offset; rfl)
    (by intro offset; simp [base, holds, applySymbol, Preterm.applyArgs, Preterm.hasVar_app_iff])
    leaves (fun symbol => nomatch symbol)
  simpa [SubstitutionControl.body, SubstitutionControl.argument, Mettapedia.Logic.HOL.instantiate,
    Mettapedia.Logic.HOL.subst, Mettapedia.Logic.HOL.Subst.single, Mettapedia.Logic.HOL.Subst.lift,
    Mettapedia.Logic.HOL.rename, Mettapedia.Logic.HOL.Rename.lift,
    encodeWithAssignment, Assignment.extend, encodeType, left, right, baseCode, bool, identityAt,
    boolType, functionType, context]
    using proof

#print axioms identityRenaming
#print axioms identity_presentations_distinct
#print axioms nestedLogicalRenaming
#print axioms closedArgumentSubstitution

end Mettapedia.Languages.MM0.HOLKernelCongruenceControls
