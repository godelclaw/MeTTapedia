import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions
import Mettapedia.Logic.HOL.ProofSyntaxCongruence
import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Retained proofs for HOL Light's equality-based truth and conjunction

The source conjunction compares two Boolean-selector functions. Applying
that equality to the two projections recovers its arguments; conversely,
proofs of the arguments construct the function equality by abstraction.
These proofs connect the source definition to the logical conjunction used
by the retained calculus, without identifying the two encodings by beta
conversion or assuming a new equation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HOLLightBooleanProofs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}

abbrev Selector : Ty Base := .prop ⇒ .prop ⇒ .prop

def truth : Formula Const Γ :=
  .eq (.lam (.var (.vz : Var (.prop :: Γ) .prop))) (.lam (.var .vz))

def pairFunction (first second : Formula Const Γ) : Term Const Γ (Selector ⇒ .prop) :=
  .lam (.app (.app (.var .vz) (weaken first)) (weaken second))

def conjunction (first second : Formula Const Γ) : Formula Const Γ :=
  .eq (pairFunction first second) (pairFunction truth truth)

def truthProof : ProofSyntax Const Δ truth := .eqRefl (.lam (.var .vz))

def truthEquation : ProofSyntax Const Δ (.eq truth .top) :=
  .eqPropI (.impI .topI) (.impI truthProof)

def toTruth {formula : Formula Const Γ} (proof : ProofSyntax Const Δ formula) :
    ProofSyntax Const Δ (.eq formula truth) :=
  .eqPropI (.impI truthProof) (.impI (proof.prepend truth))

def selector (right : Bool) : Term Const Γ Selector :=
  if right then .lam (.lam (.var .vz)) else .lam (.lam (.var (.vs .vz)))

def selectorBeta (right : Bool) (first second : Formula Const Γ) :
    ProofSyntax Const Δ (.eq (.app (.app (selector right) first) second)
      (if right then second else first)) := by
  cases right
  · apply ProofSyntax.eqTrans (ProofSyntax.eqApp second (ProofSyntax.beta first _))
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta second (weaken first))
    simp [instantiate, HOL.subst, Subst.single, Subst.lift]
    rfl
  · exact .eqTrans (.eqApp second (.beta first _)) (.beta second (.var .vz))

def pairFunctionBeta (function : Term Const Γ Selector) (first second : Formula Const Γ) :
    ProofSyntax Const Δ (.eq (.app (pairFunction first second) function)
      (.app (.app function first) second)) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta function (.app (.app (.var .vz) (weaken first)) (weaken second)))
  simp [instantiate, HOL.subst, Subst.single]
  rfl

def project (right : Bool) (first second : Formula Const Γ)
    (proof : ProofSyntax Const Δ (conjunction first second)) :
    ProofSyntax Const Δ (if right then second else first) := by
  let selected := selector (Const := Const) (Γ := Γ) right
  have leftBeta : ProofSyntax Const Δ
      (.eq (.app (pairFunction first second) selected) (if right then second else first)) :=
    .eqTrans (pairFunctionBeta selected first second) (selectorBeta right first second)
  have rightBeta : ProofSyntax Const Δ (.eq (.app (pairFunction truth truth) selected) truth) := by
    exact ProofSyntax.castIndices rfl (by cases right <;> rfl)
      (.eqTrans (pairFunctionBeta selected truth truth) (selectorBeta right truth truth))
  have equation := ProofSyntax.eqTrans (.eqSymm leftBeta)
    (.eqTrans (.eqApp selected proof) rightBeta)
  exact .impE (.eqPropER equation) truthProof

def introduce {first second : Formula Const Γ}
    (firstProof : ProofSyntax Const Δ first) (secondProof : ProofSyntax Const Δ second) :
    ProofSyntax Const Δ (conjunction first second) := by
  apply ProofSyntax.eqLam
  have firstEq := PredicateFixedPoint.weakenProof (σ := Selector) (toTruth firstProof)
  have secondEq := PredicateFixedPoint.weakenProof (σ := Selector) (toTruth secondProof)
  exact ProofSyntax.appCongr (.eqAppArg (.var .vz) firstEq) secondEq

def conjunctionEquation (first second : Formula Const Γ) :
    ProofSyntax Const Δ (.eq (conjunction first second) (.and first second)) :=
  .eqPropI
    (.impI (.andI (project false first second (.hyp 0)) (project true first second (.hyp 0))))
    (.impI (introduce (.andEL (.hyp 0)) (.andER (.hyp 0))))

theorem truth_is_source : (truth : ClosedFormula Const) = HOLLightBooleanDefinitions.truth := rfl

@[simp] theorem subst_truth {Γ' : Ctx Base} (substitution : Subst Const Γ Γ') :
    HOL.subst substitution truth = truth := rfl

@[simp] theorem subst_pairFunction {Γ' : Ctx Base} (substitution : Subst Const Γ Γ')
    (first second : Formula Const Γ) :
    HOL.subst substitution (pairFunction first second) =
      pairFunction (HOL.subst substitution first) (HOL.subst substitution second) := by
  simp [pairFunction, HOL.subst, weaken, HOL.subst_rename, HOL.rename_subst,
    Subst.lift, Rename.weaken]

@[simp] theorem subst_conjunction {Γ' : Ctx Base} (substitution : Subst Const Γ Γ')
    (first second : Formula Const Γ) :
    HOL.subst substitution (conjunction first second) =
      conjunction (HOL.subst substitution first) (HOL.subst substitution second) := by
  simp only [conjunction, HOL.subst, subst_pairFunction, subst_truth]

def sourceConjunctionBeta (first second : Formula Const Γ) :
    ProofSyntax Const Δ (.eq (HOLLightBooleanDefinitions.conj first second) (conjunction first second)) := by
  have firstBeta : ProofSyntax Const Δ
      (.eq (.app (weakenCtx Γ HOLLightBooleanDefinitions.conjunction) first)
        (.lam (conjunction (weaken first) (.var .vz)))) := by
    rw [← rename_weakenCtx (Γ' := []) (Δ' := Γ) (fun {_} index => nomatch index)
      HOLLightBooleanDefinitions.conjunction]
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.beta first (.lam (conjunction (.var (.vs .vz)) (.var .vz))))
    simp [HOLLightBooleanDefinitions.conjunction, HOLLightBooleanDefinitions.truth,
      conjunction, pairFunction, truth, weakenCtx, weaken, HOL.rename,
      instantiate, HOL.subst, Subst.single, Subst.lift, Rename.weaken, Rename.lift]
  apply ProofSyntax.eqTrans (.eqApp second firstBeta)
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta second (conjunction (weaken first) (.var .vz)))
  simp [instantiate, subst_conjunction, HOL.subst, Subst.single]

theorem selectorBeta_free (right : Bool) (first second : Formula Const Γ) :
    (selectorBeta right first second (Δ := Δ)).FunctionExtensionalityFree := by
  cases right <;> simp [selectorBeta, ProofSyntax.FunctionExtensionalityFree]

theorem pairFunctionBeta_free (function : Term Const Γ Selector) (first second : Formula Const Γ) :
    (pairFunctionBeta function first second (Δ := Δ)).FunctionExtensionalityFree := by
  simp [pairFunctionBeta, ProofSyntax.FunctionExtensionalityFree]

theorem toTruth_free {formula : Formula Const Γ} (proof : ProofSyntax Const Δ formula)
    (free : proof.FunctionExtensionalityFree) : (toTruth proof).FunctionExtensionalityFree := by
  simp [toTruth, truthProof, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend, free]

set_option backward.isDefEq.respectTransparency false in
theorem project_free (right : Bool) (first second : Formula Const Γ)
    (proof : ProofSyntax Const Δ (conjunction first second)) (free : proof.FunctionExtensionalityFree) :
    (project right first second proof).FunctionExtensionalityFree := by
  simp [project, ProofSyntax.FunctionExtensionalityFree, truthProof,
    pairFunctionBeta_free, selectorBeta_free, free]

set_option backward.isDefEq.respectTransparency false in
theorem introduce_free {first second : Formula Const Γ}
    (firstProof : ProofSyntax Const Δ first) (secondProof : ProofSyntax Const Δ second)
    (firstFree : firstProof.FunctionExtensionalityFree) (secondFree : secondProof.FunctionExtensionalityFree) :
    (introduce firstProof secondProof).FunctionExtensionalityFree := by
  simp [introduce, ProofSyntax.appCongr, ProofSyntax.FunctionExtensionalityFree,
    PredicateFixedPoint.weakenProof, toTruth_free firstProof firstFree,
    toTruth_free secondProof secondFree]

theorem conjunctionEquation_free (first second : Formula Const Γ) :
    (conjunctionEquation first second (Δ := Δ)).FunctionExtensionalityFree := by
  unfold conjunctionEquation
  constructor
  · exact ⟨project_free (Δ := conjunction first second :: Δ) false first second (.hyp 0) trivial,
      project_free (Δ := conjunction first second :: Δ) true first second (.hyp 0) trivial⟩
  · exact introduce_free (Δ := Term.and first second :: Δ) (first := first) (second := second)
      (.andEL (.hyp 0)) (.andER (.hyp 0)) trivial trivial

theorem truthEquation_free : (truthEquation (Const := Const) (Γ := Γ) (Δ := Δ)).FunctionExtensionalityFree :=
  ⟨trivial, trivial⟩

#print axioms truthEquation
#print axioms selectorBeta
#print axioms pairFunctionBeta
#print axioms conjunctionEquation
#print axioms sourceConjunctionBeta
#print axioms conjunctionEquation_free

end Mettapedia.Logic.HOL.HOLLightBooleanProofs
