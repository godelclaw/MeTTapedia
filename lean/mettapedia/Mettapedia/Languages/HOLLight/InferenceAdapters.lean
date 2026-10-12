import Mettapedia.Languages.HOLLight.SourceSubstitution
import Mettapedia.Languages.OpenTheory.DerivedRulesEquality
import Mettapedia.Languages.OpenTheory.Definitions

/-!
# HOL Light inference adapters to the shared HOL kernel

At HOL Light revision `924faf0c3471a04174ffdeb8576ce7cabcb92d64`,
`TRANS` is included as a primitive for efficiency although it is derivable.
Its structural checker below preserves the exact hypothesis and axiom unions;
the derivation theorem reuses the existing kernel transitivity proof.

HOL Light's primitive `BETA` accepts only `(lambda x. body) x`. The shared
OpenTheory beta rule permits arbitrary arguments. The named-source guard is
therefore retained before calling that existing rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight

open Mettapedia.Languages.OpenTheory Mettapedia.Logic

/-- Structural source transitivity, retaining the exact premise unions. -/
def TransSemantics (left right out : Theorem) : Prop :=
  ∃ first middle middle' last equality,
    CanonicalTerm.EqualityViewSemantics left.sequent.concl first middle ∧
    CanonicalTerm.EqualityViewSemantics right.sequent.concl middle' last ∧
    middle = middle' ∧
    CanonicalTerm.EqualityConstructionSemantics first last equality ∧
    HasParts out (left.axioms ∪ right.axioms)
      (left.sequent.hyp ∪ right.sequent.hyp) equality

/-- Alpha matching is equality of the existing checked canonical terms. -/
def checkTrans (left right : Theorem) : Option Theorem := do
  let (first, middle) ← left.sequent.concl.destEquality?
  let (middle', last) ← right.sequent.concl.destEquality?
  if middle.same middle' then
    let equality ← first.mkEquality? last
    pure (Theorem.unionResult left right
      (left.sequent.hyp ∪ right.sequent.hyp) equality)
  else
    none

theorem checkTrans_eq_some_iff (left right out : Theorem) :
    checkTrans left right = some out ↔ TransSemantics left right out := by
  simp [checkTrans, TransSemantics, Option.bind_eq_some_iff,
    CanonicalTerm.destEquality?_eq_some_iff, CanonicalTerm.same_eq_true_iff,
    CanonicalTerm.mkEquality?_eq_some_iff]

theorem TransSemantics.deterministic {left right out out' : Theorem}
    (first : TransSemantics left right out) (second : TransSemantics left right out') :
    out = out' := by
  have accepted := (checkTrans_eq_some_iff left right out).mpr first
  have accepted' := (checkTrans_eq_some_iff left right out').mpr second
  exact Option.some.inj (accepted.symm.trans accepted')

/-- The retained dependency union remains authorized by the selected theory. -/
theorem TransSemantics.outputAxiomsAllowed (policy : AxiomPolicy)
    {left right out : Theorem}
    (step : TransSemantics left right out)
    (leftAllowed : policy.AllowsTheorem left)
    (rightAllowed : policy.AllowsTheorem right) : policy.AllowsTheorem out := by
  obtain ⟨_, _, _, _, _, _, _, _, _, parts⟩ := step
  exact policy.allows_of_axioms_eq_union out left right parts.1 leftAllowed rightAllowed

/-- Source transitivity preserves general provability in the shared kernel.
The source result's exact axiom accounting is separately retained above. -/
theorem TransSemantics.derivation_preservation {policy : AxiomPolicy}
    {left right out : Theorem}
    (step : TransSemantics left right out)
    (leftProof : Derives (PolicyPrimitiveRule policy) left)
    (rightProof : Derives (PolicyPrimitiveRule policy) right) :
    KernelProvable policy out.sequent.hyp out.sequent.concl.term := by
  obtain ⟨first, middle, middle', last, equality, leftView, rightView,
    matchMiddle, construction, parts⟩ := step
  subst middle'
  have leftKernel : KernelProvable policy left.sequent.hyp
      (CanonicalTerm.equalityDB first.ty first.term middle.term) :=
    ⟨left, leftProof, rfl, leftView.2⟩
  have rightKernel : KernelProvable policy right.sequent.hyp
      (CanonicalTerm.equalityDB first.ty middle.term last.term) := by
    refine ⟨right, rightProof, rfl, ?_⟩
    exact rightView.2.trans (congrArg
      (fun type => CanonicalTerm.equalityDB type middle.term last.term) leftView.1.symm)
  have result := KernelProvable.trans leftKernel rightKernel
  rw [parts.2.1, parts.2.2, construction.2]
  exact result

/-- Transitivity expands to reflexivity, application and equality modus
ponens in the shared kernel, preserving the entire theorem object. -/
theorem TransSemantics.shared_derivation (policy : AxiomPolicy)
    {left right out : Theorem} (step : TransSemantics left right out)
    (leftProof : Derives (PolicyPrimitiveRule policy) left)
    (rightProof : Derives (PolicyPrimitiveRule policy) right) :
    Derives (PolicyPrimitiveRule policy) out := by
  obtain ⟨first, middle, middle', last, equality, leftView, rightView,
    matchMiddle, construction, parts⟩ := step
  subst middle'
  let function : CanonicalTerm :=
    ⟨.app (.const Const.equality (Ty.equality first.ty)) first.term,
      .function first.ty Ty.bool,
      DBTerm.inferType_app_of (DBTerm.inferType_equality_const [] first.ty) first.checked⟩
  let reflexivityEquality := CanonicalTerm.equalityOfSameType function function rfl
  let reflexivity := Theorem.emptyResult ∅ reflexivityEquality
  have reflexivityProof : Derives (PolicyPrimitiveRule policy) reflexivity :=
    derives_of_nullary_check policy (.core (.refl function)) reflexivity rfl True.intro
      ((checkRefl_eq_some_iff _ _).mpr
        ⟨reflexivityEquality, CanonicalTerm.equalityOfSameType_semantics _ _ rfl,
          rfl, rfl, rfl⟩)
  have leftBool := (derives_isBool leftProof).1
  have outBool : out.sequent.concl.ty = Ty.bool := by
    rw [parts.2.2]
    exact construction.resultIsBool
  let congruenceEquality := CanonicalTerm.equalityOfSameType
    left.sequent.concl out.sequent.concl (leftBool.trans outBool.symm)
  let congruence := Theorem.unionResult reflexivity right
    (reflexivity.sequent.hyp ∪ right.sequent.hyp) congruenceEquality
  have functionView : CanonicalTerm.EqualityViewSemantics
      reflexivity.sequent.concl function function := ⟨rfl, rfl⟩
  have firstApplication : CanonicalTerm.ApplicationSemantics
      function middle left.sequent.concl :=
    ⟨first.ty, Ty.bool, Ty.destFunction?_function _ _, leftView.1,
      leftView.2⟩
  have lastApplication : CanonicalTerm.ApplicationSemantics
      function last out.sequent.concl :=
    ⟨first.ty, Ty.bool, Ty.destFunction?_function _ _,
      leftView.1.trans rightView.1,
      (congrArg CanonicalTerm.term parts.2.2).trans construction.2⟩
  have applicationStep : PrimitiveStep (.core (.app reflexivity right)) congruence :=
    ⟨.core (.app function function middle last left.sequent.concl out.sequent.concl
      congruenceEquality functionView rightView firstApplication lastApplication
      (CanonicalTerm.equalityOfSameType_semantics _ _ _) ⟨rfl, rfl, rfl⟩)⟩
  have congruenceProof : Derives (PolicyPrimitiveRule policy) congruence := by
    refine Derives.node [reflexivity, right] congruence
      ⟨.core (.app reflexivity right), rfl,
        ⟨derives_only_authorized_axioms policy reflexivityProof,
          derives_only_authorized_axioms policy rightProof⟩, applicationStep⟩ ?_
    intro premise member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact reflexivityProof
    · exact rightProof
  have outParts : HasParts out (congruence.axioms ∪ left.axioms)
      (congruence.sequent.hyp ∪ left.sequent.hyp) out.sequent.concl := by
    refine ⟨?_, ?_, rfl⟩
    · simpa only [congruence, reflexivity, Theorem.unionResult, Theorem.emptyResult,
        Finset.empty_union, Finset.union_empty, Finset.union_comm] using parts.1
    · simpa only [congruence, reflexivity, Theorem.unionResult, Theorem.emptyResult,
        Finset.empty_union, Finset.union_empty, Finset.union_comm] using parts.2.1
  refine Derives.node [congruence, left] out
    ⟨.core (.eqMp congruence left), rfl,
      ⟨derives_only_authorized_axioms policy congruenceProof,
        derives_only_authorized_axioms policy leftProof⟩,
      ⟨.core (.eqMp left.sequent.concl out.sequent.concl
        ⟨leftBool.trans outBool.symm, rfl⟩ rfl outParts)⟩⟩ ?_
  intro premise member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact congruenceProof
  · exact leftProof

/-- Independent named-source description of HOL Light's trivial beta redex. -/
def TrivialBetaRedex : SourceTerm → Prop
  | .app (.abs name type _) (.var other otherType) =>
      name = other ∧ type = otherType
  | _ => False

def trivialBetaB : SourceTerm → Bool
  | .app (.abs name type _) (.var other otherType) =>
      sourceVarSame ⟨name, type⟩ ⟨other, otherType⟩
  | _ => false

theorem trivialBetaB_eq_true_iff (source : SourceTerm) :
    trivialBetaB source = true ↔ TrivialBetaRedex source := by
  cases source with
  | const constant type => simp only [trivialBetaB, TrivialBetaRedex, Bool.false_eq_true]
  | var name type => simp only [trivialBetaB, TrivialBetaRedex, Bool.false_eq_true]
  | abs name type body => simp only [trivialBetaB, TrivialBetaRedex, Bool.false_eq_true]
  | app function argument =>
      cases function <;> cases argument <;>
        simp only [trivialBetaB, TrivialBetaRedex, Bool.false_eq_true,
          sourceVarSame_eq_true_iff, Var.mk.injEq]

/-- Keep the source admission guard and reuse the shared beta inference. -/
def checkSourceBeta (source : CheckedSourceTerm) : Option Theorem :=
  if trivialBetaB source.source then checkBetaConv source.canonical else none

def SourceBetaSemantics (source : CheckedSourceTerm) (out : Theorem) : Prop :=
  TrivialBetaRedex source.source ∧ BetaConvSemantics source.canonical out

theorem checkSourceBeta_eq_some_iff (source : CheckedSourceTerm) (out : Theorem) :
    checkSourceBeta source = some out ↔ SourceBetaSemantics source out := by
  by_cases trivialRedex : trivialBetaB source.source = true
  · simp [checkSourceBeta, SourceBetaSemantics, trivialRedex,
      (trivialBetaB_eq_true_iff source.source).mp trivialRedex, checkBetaConv_eq_some_iff]
  · have notTrivial : ¬ TrivialBetaRedex source.source :=
      fun redex => trivialRedex ((trivialBetaB_eq_true_iff source.source).mpr redex)
    simp [checkSourceBeta, SourceBetaSemantics, trivialRedex, notTrivial]

/-- A checked HOL Light beta step is an actual shared-kernel primitive step. -/
theorem SourceBetaSemantics.shared_step {source : CheckedSourceTerm} {out : Theorem}
    (step : SourceBetaSemantics source out) :
    PrimitiveStep (.binding (.betaConv source.canonical)) out :=
  (checkPrimitive_eq_some_iff _ _).mp
    ((checkBetaConv_eq_some_iff _ _).mpr step.2)

/-- General derivation preservation uses the same rule closure as authored
proofs, rather than trusting an exported theorem name. -/
theorem SourceBetaSemantics.derivation_preservation (policy : AxiomPolicy)
    {source : CheckedSourceTerm} {out : Theorem} (step : SourceBetaSemantics source out) :
    Derives (PolicyPrimitiveRule policy) out :=
  derives_of_nullary_check policy (.binding (.betaConv source.canonical)) out rfl
    True.intro ((checkPrimitive_eq_some_iff _ _).mpr step.shared_step)

namespace Controls

def trivialRedex : SourceTerm :=
  .app (.abs (.global "x") Ty.bool (.var (.global "x") Ty.bool))
    (.var (.global "x") Ty.bool)

def differentArgument : SourceTerm :=
  .app (.abs (.global "x") Ty.bool (.var (.global "x") Ty.bool))
    (.var (.global "y") Ty.bool)

theorem same_argument_admitted : TrivialBetaRedex trivialRedex :=
  ⟨rfl, rfl⟩

/-- A different, well-typed argument is outside the source primitive even
though the shared kernel supports its broader beta conversion. -/
theorem different_argument_refused : ¬ TrivialBetaRedex differentArgument := by
  rw [← trivialBetaB_eq_true_iff]
  decide

end Controls
end Mettapedia.Languages.HOLLight
