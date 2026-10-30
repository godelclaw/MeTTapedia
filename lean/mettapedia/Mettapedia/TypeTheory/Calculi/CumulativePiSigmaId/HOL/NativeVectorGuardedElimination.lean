import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorGuardedFamily
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Dependent elimination for the constructed indexed Vec guard

The method predicate retains its element, length, tail and recursive-result
arguments. The eliminator's result typing uses induction derived from the
least family predicate, together with the existing root computation proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.GuardedFamily
open Mettapedia.Logic
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}

def sourceCons (A : HOL.Term Const Γ operations.elementPredicate)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element)
    (t : HOL.Term Const Γ operations.vector) :=
  HOL.Term.app (.app (.app (.app (HOL.weakenCtx Γ operations.consCode) A) n) h) t

def methodResult (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element)
    (t : HOL.Term Const Γ operations.vector) : HOL.Term Const Γ ((operations.result ⇒ operations.result) ⇒ .prop) :=
  HOL.PredicateProducts.pi (.app (.app P n) t)
    (HOL.weaken (.app (.app P (.app (HOL.weakenCtx Γ operations.successor) n)) (sourceCons operations A n h t)))

def methodTail (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element) :=
  HOL.PredicateProducts.pi (.app (.app (familyCode operations) A) n)
    (methodResult operations (HOL.weaken A) (HOL.weaken P) (HOL.weaken n) (HOL.weaken h) (.var .vz))

def methodHead (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (n : HOL.Term Const Γ operations.number) :=
  HOL.PredicateProducts.pi A
    (methodTail operations (HOL.weaken A) (HOL.weaken P) (HOL.weaken n) (.var .vz))

def methodPredicate (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :=
  HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
    (methodHead operations (HOL.weaken A) (HOL.weaken P) (.var .vz))

def resultPredicate (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :=
  HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
    (HOL.PredicateProducts.pi (.app (.app (familyCode operations) (HOL.weaken A)) (.var .vz))
      (.app (.app (HOL.weaken (HOL.weaken P)) (.var (.vs .vz))) (.var .vz)))

@[simp] theorem subst_sourceCons (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (n : HOL.Term Const Γ operations.number)
    (h : HOL.Term Const Γ operations.element) (t : HOL.Term Const Γ operations.vector) :
    HOL.subst substitution (sourceCons operations A n h t) =
      sourceCons operations (HOL.subst substitution A) (HOL.subst substitution n)
        (HOL.subst substitution h) (HOL.subst substitution t) := by
  simp [sourceCons, HOL.subst, HOL.subst_weakenCtx]

@[simp] theorem subst_methodResult (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element)
    (t : HOL.Term Const Γ operations.vector) :
    HOL.subst substitution (methodResult operations A P n h t) =
      methodResult operations (HOL.subst substitution A) (HOL.subst substitution P)
        (HOL.subst substitution n) (HOL.subst substitution h) (HOL.subst substitution t) := by
  simp [methodResult, HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx]

@[simp] theorem subst_methodTail (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element) :
    HOL.subst substitution (methodTail operations A P n h) =
      methodTail operations (HOL.subst substitution A) (HOL.subst substitution P)
        (HOL.subst substitution n) (HOL.subst substitution h) := by
  simp [methodTail, HOL.subst, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem subst_methodHead (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (n : HOL.Term Const Γ operations.number) :
    HOL.subst substitution (methodHead operations A P n) =
      methodHead operations (HOL.subst substitution A) (HOL.subst substitution P) (HOL.subst substitution n) := by
  simp [methodHead, HOL.subst, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem subst_methodPredicate (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :
    HOL.subst substitution (methodPredicate operations A P) =
      methodPredicate operations (HOL.subst substitution A) (HOL.subst substitution P) := by
  simp [methodPredicate, HOL.subst, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem rename_methodPredicate (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :
    HOL.rename rho (methodPredicate operations A P) = methodPredicate operations (HOL.rename rho A) (HOL.rename rho P) := by
  simpa only [HOL.subst_ofRename] using subst_methodPredicate operations (HOL.Subst.ofRename rho) A P

@[simp] theorem subst_resultPredicate (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :
    HOL.subst substitution (resultPredicate operations A P) =
      resultPredicate operations (HOL.subst substitution A) (HOL.subst substitution P) := by
  simp [resultPredicate, HOL.subst, HOL.subst_weaken, HOL.Subst.lift, HOL.Rename.weaken]

variable {Δ : List (HOL.Formula Const Γ)}

def method_at (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (s : HOL.Term Const Γ operations.method) (n : HOL.Term Const Γ operations.number)
    (h : HOL.Term Const Γ operations.element) (t : HOL.Term Const Γ operations.vector)
    (r : HOL.Term Const Γ operations.result)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (headTyped : HOL.ProofSyntax Const Δ (.app A h))
    (tailTyped : HOL.ProofSyntax Const Δ (membership operations A n t))
    (recursiveTyped : HOL.ProofSyntax Const Δ (.app (.app (.app P n) t) r)) :
    HOL.ProofSyntax Const Δ (.app (.app (.app P (.app (HOL.weakenCtx Γ operations.successor) n))
      (sourceCons operations A n h t)) (.app (.app (.app (.app s n) h) t) r)) := by
  have numberTyped : HOL.ProofSyntax Const Δ (.app (HOL.PredicateProducts.full operations.number) n) :=
    .impE (.eqPropER (.beta n .top)) .topI
  have atNumber : HOL.ProofSyntax Const Δ (.app (methodHead operations A P n) (.app s n)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (HOL.PredicateProducts.eliminate _ _ s n methodTyped numberTyped)
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single]
  have atHead : HOL.ProofSyntax Const Δ (.app (methodTail operations A P n h) (.app (.app s n) h)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (HOL.PredicateProducts.eliminate _ _ (.app s n) h atNumber headTyped)
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single]
  have atTail : HOL.ProofSyntax Const Δ (.app (methodResult operations A P n h t) (.app (.app (.app s n) h) t)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (HOL.PredicateProducts.eliminate _ _ (.app (.app s n) h) t atHead tailTyped)
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single]
  apply HOL.ProofSyntax.castIndices rfl ?_
    (HOL.PredicateProducts.eliminate _ _ (.app (.app (.app s n) h) t) r atTail recursiveTyped)
  simp only [HOL.instantiate_weaken]

def computed (P : HOL.Term Const Γ operations.motive)
    (function : HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ operations.result)) :
    HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ .prop) :=
  .lam (.lam (.app (.app (.app (HOL.weaken (HOL.weaken P)) (.var (.vs .vz))) (.var .vz))
    (.app (.app (HOL.weaken (HOL.weaken function)) (.var (.vs .vz))) (.var .vz))))

@[simp] theorem subst_computed (substitution : HOL.Subst Const Γ Ξ)
    (P : HOL.Term Const Γ operations.motive)
    (function : HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ operations.result)) :
    HOL.subst substitution (computed operations P function) =
      computed operations (HOL.subst substitution P) (HOL.subst substitution function) := by
  simp [computed, HOL.subst, HOL.subst_weaken, HOL.Subst.lift, HOL.Rename.weaken]

@[simp] theorem rename_computed (rho : HOL.Rename Base Γ Ξ)
    (P : HOL.Term Const Γ operations.motive)
    (function : HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ operations.result)) :
    HOL.rename rho (computed operations P function) = computed operations (HOL.rename rho P) (HOL.rename rho function) := by
  simpa only [HOL.subst_ofRename] using subst_computed operations (HOL.Subst.ofRename rho) P function

@[simp] theorem rename_recursion (rho : HOL.Rename Base Γ Ξ)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method) :
    HOL.rename rho (operations.recursion z s) = operations.recursion (HOL.rename rho z) (HOL.rename rho s) := by
  simpa only [HOL.subst_ofRename] using operations.subst_recursion (HOL.Subst.ofRename rho) z s

def computed_apply (P : HOL.Term Const Γ operations.motive)
    (function : HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ operations.result))
    (n : HOL.Term Const Γ operations.number) (t : HOL.Term Const Γ operations.vector) :
    HOL.ProofSyntax Const Δ (.eq (HOL.PredicatePair.holds (computed operations P function) n t)
      (.app (.app (.app P n) t) (.app (.app function n) t))) := by
  have first : HOL.ProofSyntax Const Δ (.eq (.app (computed operations P function) n)
      (.lam (.app (.app (.app (HOL.weaken P) (HOL.weaken n)) (.var .vz))
        (.app (.app (HOL.weaken function) (HOL.weaken n)) (.var .vz))))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta n (.lam (.app (.app (.app (HOL.weaken (HOL.weaken P)) (.var (.vs .vz))) (.var .vz))
        (.app (.app (HOL.weaken (HOL.weaken function)) (.var (.vs .vz))) (.var .vz)))))
    simp [computed, HOL.instantiate, HOL.subst, HOL.Subst.lift, HOL.Subst.single]
    rfl
  have second : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (.app (.app (.app (HOL.weaken P) (HOL.weaken n)) (.var .vz))
        (.app (.app (HOL.weaken function) (HOL.weaken n)) (.var .vz)))) t)
      (.app (.app (.app P n) t) (.app (.app function n) t))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta t (.app (.app (.app (HOL.weaken P) (HOL.weaken n)) (.var .vz))
        (.app (.app (HOL.weaken function) (HOL.weaken n)) (.var .vz))))
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp t first) second

abbrev RootEvidence (context : HOL.Ctx Base) (hypotheses : List (HOL.Formula Const context)) :=
  HOL.ProofSyntax.HypothesisSubstitution (operations.assumptions context) hypotheses

def RootEvidence.rename (rho : HOL.Rename Base Γ Ξ) (roots : RootEvidence operations Γ Δ) :
    RootEvidence operations Ξ (Δ.map (HOL.rename rho)) := by
  have maps : (operations.assumptions Γ).map (HOL.rename rho) = operations.assumptions Ξ := by
    calc
      _ = (operations.assumptions Γ).map (HOL.subst (HOL.Subst.ofRename rho)) := by
        apply List.map_congr_left
        intro formula _
        exact (HOL.subst_ofRename rho formula).symm
      _ = _ := operations.assumptions_substitute (HOL.Subst.ofRename rho)
  intro occurrence
  let original : Fin (operations.assumptions Γ).length := occurrence.cast (by simp [Operations.assumptions])
  apply HOL.ProofSyntax.castIndices rfl ?_ ((roots original).rename rho)
  have sourceBound : occurrence.val < (operations.assumptions Γ).length := original.isLt
  have mapBound : occurrence.val < ((operations.assumptions Γ).map (HOL.rename rho)).length := by simpa using sourceBound
  have same := congrArg (fun formulas => formulas[occurrence.val]?) maps
  simpa [List.getElem?_eq_getElem, sourceBound, mapBound, occurrence.isLt, List.get_eq_getElem, original] using same

def RootEvidence.prepend (roots : RootEvidence operations Γ Δ) (premise : HOL.Formula Const Γ) :
    RootEvidence operations Γ (premise :: Δ) := fun occurrence => (roots occurrence).prepend premise

def recursion_step_at (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element)
    (t : HOL.Term Const Γ operations.vector)
    (roots : RootEvidence operations Γ Δ)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (headTyped : HOL.ProofSyntax Const Δ (.app A h))
    (tailTyped : HOL.ProofSyntax Const Δ ((algebra operations).member A n t))
    (recursiveTyped : HOL.ProofSyntax Const Δ (HOL.PredicatePair.holds (computed operations P (operations.recursion z s)) n t)) :
    HOL.ProofSyntax Const Δ (HOL.PredicatePair.holds (computed operations P (operations.recursion z s))
      (.app (HOL.weakenCtx Γ operations.successor) n) ((algebra operations).consValue n h t)) := by
  have tailSource := HOL.ProofSyntax.impE (.eqPropER (family_apply operations A n t)) tailTyped
  have child := HOL.ProofSyntax.impE (.eqPropEL (computed_apply operations P (operations.recursion z s) n t)) recursiveTyped
  have applied := method_at operations A P s n h t (.app (.app (operations.recursion z s) n) t)
    methodTyped headTyped tailSource child
  have raw := HOL.ProofSyntax.impE (.eqPropEL
    (.eqApp (.app (.app (.app (.app s n) h) t) (.app (.app (operations.recursion z s) n) t))
      (.eqAppArg (.app P (.app (HOL.weakenCtx Γ operations.successor) n)) (operations.cons_apply A n h t)))) applied
  have equation := HOL.VectorRecursionProofs.atCons (HOL.weakenCtx Γ operations.selection)
    (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
    (HOL.weakenCtx Γ operations.head) (HOL.weakenCtx Γ operations.tail) (HOL.weakenCtx Γ operations.cons)
    z s n h t (roots ⟨0, by simp [Operations.assumptions]⟩) (roots ⟨1, by simp [Operations.assumptions]⟩)
    (operations.head_at n h t (roots ⟨2, by simp [Operations.assumptions]⟩))
    (operations.tail_at n h t (roots ⟨3, by simp [Operations.assumptions]⟩))
  have recursed := HOL.ProofSyntax.impE (.eqPropER
    (.eqAppArg (.app (.app P (.app (HOL.weakenCtx Γ operations.successor) n)) ((algebra operations).consValue n h t)) equation)) raw
  exact .impE (.eqPropER (computed_apply operations P (operations.recursion z s)
    (.app (HOL.weakenCtx Γ operations.successor) n) ((algebra operations).consValue n h t))) recursed

def recursion_step (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (roots : RootEvidence operations Γ Δ)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s)) :
    HOL.ProofSyntax Const Δ ((algebra operations).stepCondition A (computed operations P (operations.recursion z s))) := by
  refine .allI (.allI (.allI (.impI (.impI (.impI ?_)))))
  let a := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.element) (HOL.weaken (σ := operations.number) A))
  let p := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.element) (HOL.weaken (σ := operations.number) P))
  let base := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.element) (HOL.weaken (σ := operations.number) z))
  let method := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.element) (HOL.weaken (σ := operations.number) s))
  let n : HOL.Term Const (operations.vector :: operations.element :: operations.number :: Γ) operations.number := .var (.vs (.vs .vz))
  let h : HOL.Term Const (operations.vector :: operations.element :: operations.number :: Γ) operations.element := .var (.vs .vz)
  let t : HOL.Term Const (operations.vector :: operations.element :: operations.number :: Γ) operations.vector := .var .vz
  let headGuard := HOL.Term.app a h
  let tailGuard := (algebra operations).member a n t
  let childGuard := HOL.PredicatePair.holds (computed operations p (operations.recursion base method)) n t
  let hypotheses := childGuard :: tailGuard :: headGuard :: HOL.weakenHyps (σ := operations.vector)
    (HOL.weakenHyps (σ := operations.element) (HOL.weakenHyps (σ := operations.number) Δ))
  have liftedRoots : RootEvidence operations _ hypotheses :=
    (((RootEvidence.rename operations HOL.Rename.weaken
      (RootEvidence.rename operations HOL.Rename.weaken
        (RootEvidence.rename operations HOL.Rename.weaken roots))).prepend operations headGuard).prepend operations tailGuard).prepend operations childGuard
  have liftedMethod : HOL.ProofSyntax Const hypotheses (.app (methodPredicate operations a p) method) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      ((((HOL.PredicateFixedPoint.weakenProof (σ := operations.vector)
        (HOL.PredicateFixedPoint.weakenProof (σ := operations.element)
          (HOL.PredicateFixedPoint.weakenProof (σ := operations.number) methodTyped))).prepend headGuard).prepend tailGuard).prepend childGuard)
    simp only [a, p, method, HOL.weaken, HOL.rename, rename_methodPredicate]
  have proved := recursion_step_at operations a p base method n h t liftedRoots liftedMethod
    (.hyp (Δ := hypotheses) ⟨2, by simp [hypotheses]⟩)
    (.hyp (Δ := hypotheses) ⟨1, by simp [hypotheses]⟩)
    (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)
  apply HOL.ProofSyntax.castIndices ?_ ?_ proved
  · simp only [hypotheses, childGuard, tailGuard, headGuard, a, p, base, method, n, h, t,
      HOL.weaken, rename_computed, rename_recursion]
  · simp only [p, base, method, n, h, t, HOL.weaken, rename_computed, rename_recursion]
    rfl

def basePredicate (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :=
  HOL.Term.app (.app P (HOL.weakenCtx Γ operations.zero)) (.app (HOL.weakenCtx Γ operations.nilCode) A)

def appliedEliminator (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method) :=
  HOL.Term.app (.app (.app (.app operations.eliminator A) P) z) s

@[simp] theorem subst_basePredicate (substitution : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :
    HOL.subst substitution (basePredicate operations A P) =
      basePredicate operations (HOL.subst substitution A) (HOL.subst substitution P) := by
  simp [basePredicate, HOL.subst, HOL.subst_weakenCtx]

@[simp] theorem rename_basePredicate (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive) :
    HOL.rename rho (basePredicate operations A P) = basePredicate operations (HOL.rename rho A) (HOL.rename rho P) := by
  simpa only [HOL.subst_ofRename] using subst_basePredicate operations (HOL.Subst.ofRename rho) A P

@[simp] theorem rename_appliedEliminator (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method) :
    HOL.rename rho (appliedEliminator operations A P z s) =
      appliedEliminator operations (HOL.rename rho A) (HOL.rename rho P) (HOL.rename rho z) (HOL.rename rho s) := by
  have reads := operations.subst_eliminator (HOL.Subst.ofRename rho)
  simp only [HOL.subst_ofRename] at reads
  simp only [appliedEliminator, HOL.rename, reads]

/-- The result at an arbitrary guarded vector follows from the constructed
family induction. Root recursion and selector commitments remain explicit. -/
def result_at (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (n : HOL.Term Const Γ operations.number) (t : HOL.Term Const Γ operations.vector)
    (roots : RootEvidence operations Γ Δ)
    (baseTyped : HOL.ProofSyntax Const Δ (.app (basePredicate operations A P) z))
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (vectorTyped : HOL.ProofSyntax Const Δ (membership operations A n t)) :
    HOL.ProofSyntax Const Δ (.app (.app (.app P n) t) (.app (.app (appliedEliminator operations A P z s) n) t)) := by
  have rawBase := HOL.ProofSyntax.impE (.eqPropEL
    (.eqApp z (.eqAppArg (.app P (HOL.weakenCtx Γ operations.zero)) (nil_apply operations A)))) baseTyped
  have zeroEquation := HOL.VectorRecursionProofs.atZero (HOL.weakenCtx Γ operations.selection)
    (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
    (HOL.weakenCtx Γ operations.head) (HOL.weakenCtx Γ operations.tail) z s (HOL.weakenCtx Γ operations.nil)
    (roots ⟨0, by simp [Operations.assumptions]⟩) (roots ⟨1, by simp [Operations.assumptions]⟩)
  have recursionBase := HOL.ProofSyntax.impE (.eqPropER
    (.eqAppArg (.app (.app P (HOL.weakenCtx Γ operations.zero)) (HOL.weakenCtx Γ operations.nil)) zeroEquation)) rawBase
  have base := HOL.ProofSyntax.impE (.eqPropER (computed_apply operations P (operations.recursion z s)
    (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.nil))) recursionBase
  have member := HOL.ProofSyntax.impE (.eqPropEL (family_apply operations A n t)) vectorTyped
  have inducted := (algebra operations).inductionProof A (computed operations P (operations.recursion z s)) n t
    base (recursion_step operations A P z s roots methodTyped) member
  have recursionTyped := HOL.ProofSyntax.impE (.eqPropEL (computed_apply operations P (operations.recursion z s) n t)) inducted
  exact .impE (.eqPropER (.eqAppArg (.app (.app P n) t)
    (.eqApp t (.eqApp n (operations.eliminator_apply A P z s))))) recursionTyped

/-- The curried declared eliminator belongs to its guarded dependent result
predicate; the proof is valid in an arbitrary open context. -/
def result_typed (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (roots : RootEvidence operations Γ Δ)
    (baseTyped : HOL.ProofSyntax Const Δ (.app (basePredicate operations A P) z))
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s)) :
    HOL.ProofSyntax Const Δ (.app (resultPredicate operations A P) (appliedEliminator operations A P z s)) := by
  apply HOL.PredicateProducts.introduce
  apply HOL.PredicateProducts.introduce
  let a := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.number) A)
  let p := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.number) P)
  let base := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.number) z)
  let method := HOL.weaken (σ := operations.vector) (HOL.weaken (σ := operations.number) s)
  let n : HOL.Term Const (operations.vector :: operations.number :: Γ) operations.number := .var (.vs .vz)
  let t : HOL.Term Const (operations.vector :: operations.number :: Γ) operations.vector := .var .vz
  let numberGuard : HOL.Formula Const (operations.vector :: operations.number :: Γ) :=
    .app (HOL.PredicateProducts.full operations.number) n
  let vectorGuard := membership operations a n t
  let hypotheses := vectorGuard :: numberGuard :: HOL.weakenHyps (σ := operations.vector) (HOL.weakenHyps (σ := operations.number) Δ)
  have liftedRoots : RootEvidence operations _ hypotheses :=
    ((RootEvidence.rename operations HOL.Rename.weaken
      (RootEvidence.rename operations HOL.Rename.weaken roots)).prepend operations numberGuard).prepend operations vectorGuard
  have liftedBase : HOL.ProofSyntax Const hypotheses (.app (basePredicate operations a p) base) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (((HOL.PredicateFixedPoint.weakenProof (σ := operations.vector)
        (HOL.PredicateFixedPoint.weakenProof (σ := operations.number) baseTyped)).prepend numberGuard).prepend vectorGuard)
    simp only [a, p, base, HOL.weaken, HOL.rename, rename_basePredicate]
  have liftedMethod : HOL.ProofSyntax Const hypotheses (.app (methodPredicate operations a p) method) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (((HOL.PredicateFixedPoint.weakenProof (σ := operations.vector)
        (HOL.PredicateFixedPoint.weakenProof (σ := operations.number) methodTyped)).prepend numberGuard).prepend vectorGuard)
    simp only [a, p, method, HOL.weaken, HOL.rename, rename_methodPredicate]
  have proved := result_at operations a p base method n t liftedRoots liftedBase liftedMethod
    (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)
  apply HOL.ProofSyntax.castIndices ?_ ?_ proved
  · simp only [hypotheses, vectorGuard, numberGuard, membership, a, n, t, HOL.weakenHyps,
      List.map_cons, HOL.weaken, HOL.rename, HOL.PredicateProducts.rename_full]
    have reads := subst_familyCode operations (HOL.Subst.ofRename (HOL.Rename.weaken (Γ := operations.number :: Γ) (σ := operations.vector)))
    simp only [HOL.subst_ofRename] at reads
    rw [reads]
    rfl
  · simp only [a, p, base, method, n, t, HOL.weaken, HOL.rename, rename_appliedEliminator, HOL.Rename.weaken]

theorem method_at_free (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (s : HOL.Term Const Γ operations.method) (n : HOL.Term Const Γ operations.number)
    (h : HOL.Term Const Γ operations.element) (t : HOL.Term Const Γ operations.vector)
    (r : HOL.Term Const Γ operations.result)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (headTyped : HOL.ProofSyntax Const Δ (.app A h))
    (tailTyped : HOL.ProofSyntax Const Δ (membership operations A n t))
    (recursiveTyped : HOL.ProofSyntax Const Δ (.app (.app (.app P n) t) r))
    (methodTypedFree : methodTyped.FunctionExtensionalityFree)
    (headTypedFree : headTyped.FunctionExtensionalityFree)
    (tailTypedFree : tailTyped.FunctionExtensionalityFree)
    (recursiveTypedFree : recursiveTyped.FunctionExtensionalityFree) :
    (method_at (Δ := Δ) operations A P s n h t r methodTyped headTyped tailTyped recursiveTyped).FunctionExtensionalityFree := by
  simp [method_at, HOL.ProofSyntax.FunctionExtensionalityFree, HOL.PredicateProducts.eliminate, HOL.PredicateProducts.beta_free,
    methodTypedFree, headTypedFree, tailTypedFree, recursiveTypedFree]

theorem computed_apply_free (P : HOL.Term Const Γ operations.motive)
    (function : HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ operations.result))
    (n : HOL.Term Const Γ operations.number) (t : HOL.Term Const Γ operations.vector) :
    (computed_apply (Δ := Δ) operations P function n t).FunctionExtensionalityFree := by
  simp [computed_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem RootEvidence.rename_free (rho : HOL.Rename Base Γ Ξ) (roots : RootEvidence operations Γ Δ)
    (free : ∀ occurrence, (roots occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, ((RootEvidence.rename operations rho roots) occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simpa only [RootEvidence.rename, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_rename] using free (occurrence.cast (by simp [Operations.assumptions]))

theorem RootEvidence.prepend_free (roots : RootEvidence operations Γ Δ) (premise : HOL.Formula Const Γ)
    (free : ∀ occurrence, (roots occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, ((RootEvidence.prepend operations roots premise) occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simpa only [RootEvidence.prepend, HOL.ProofSyntax.prepend,
    HOL.ProofSyntax.functionExtensionalityFree_mono] using free occurrence

theorem recursion_step_at_free (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (n : HOL.Term Const Γ operations.number) (h : HOL.Term Const Γ operations.element)
    (t : HOL.Term Const Γ operations.vector)
    (roots : RootEvidence operations Γ Δ)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (headTyped : HOL.ProofSyntax Const Δ (.app A h))
    (tailTyped : HOL.ProofSyntax Const Δ ((algebra operations).member A n t))
    (recursiveTyped : HOL.ProofSyntax Const Δ (HOL.PredicatePair.holds (computed operations P (operations.recursion z s)) n t))
    (methodTypedFree : methodTyped.FunctionExtensionalityFree)
    (headTypedFree : headTyped.FunctionExtensionalityFree)
    (tailTypedFree : tailTyped.FunctionExtensionalityFree)
    (recursiveTypedFree : recursiveTyped.FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (roots occurrence).FunctionExtensionalityFree) :
    (recursion_step_at (Δ := Δ) operations A P z s n h t roots methodTyped headTyped tailTyped recursiveTyped).FunctionExtensionalityFree := by
  simp [recursion_step_at, HOL.ProofSyntax.FunctionExtensionalityFree, method_at_free, computed_apply_free, family_apply_free,
    Operations.cons_apply, HOL.VectorRecursionProofs.atCons_free, Operations.head_at, Operations.tail_at,
    methodTypedFree, headTypedFree, tailTypedFree, recursiveTypedFree, rootsFree]

theorem recursion_step_free (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (roots : RootEvidence operations Γ Δ)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (methodTypedFree : methodTyped.FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (roots occurrence).FunctionExtensionalityFree) :
    (recursion_step (Δ := Δ) operations A P z s roots methodTyped).FunctionExtensionalityFree := by
  simp only [recursion_step, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_castIndices]
  apply recursion_step_at_free <;>
    simp [HOL.PredicateFixedPoint.weakenProof, HOL.ProofSyntax.prepend, RootEvidence.prepend,
      RootEvidence.rename, HOL.ProofSyntax.FunctionExtensionalityFree, methodTypedFree, rootsFree]

theorem result_at_free (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (n : HOL.Term Const Γ operations.number) (t : HOL.Term Const Γ operations.vector)
    (roots : RootEvidence operations Γ Δ)
    (baseTyped : HOL.ProofSyntax Const Δ (.app (basePredicate operations A P) z))
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (vectorTyped : HOL.ProofSyntax Const Δ (membership operations A n t))
    (baseTypedFree : baseTyped.FunctionExtensionalityFree)
    (methodTypedFree : methodTyped.FunctionExtensionalityFree)
    (vectorTypedFree : vectorTyped.FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (roots occurrence).FunctionExtensionalityFree) :
    (result_at (Δ := Δ) operations A P z s n t roots baseTyped methodTyped vectorTyped).FunctionExtensionalityFree := by
  simp [result_at, HOL.ProofSyntax.FunctionExtensionalityFree, HOL.IndexedVectorPredicate.Signature.inductionProof_free,
    recursion_step_free, computed_apply_free, family_apply_free, nil_apply, Operations.eliminator_apply,
    HOL.VectorRecursionProofs.atZero_free, baseTypedFree, methodTypedFree, vectorTypedFree, rootsFree]

theorem result_typed_free (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (z : HOL.Term Const Γ operations.result) (s : HOL.Term Const Γ operations.method)
    (roots : RootEvidence operations Γ Δ)
    (baseTyped : HOL.ProofSyntax Const Δ (.app (basePredicate operations A P) z))
    (methodTyped : HOL.ProofSyntax Const Δ (.app (methodPredicate operations A P) s))
    (baseTypedFree : baseTyped.FunctionExtensionalityFree)
    (methodTypedFree : methodTyped.FunctionExtensionalityFree)
    (rootsFree : ∀ occurrence, (roots occurrence).FunctionExtensionalityFree) :
    (result_typed (Δ := Δ) operations A P z s roots baseTyped methodTyped).FunctionExtensionalityFree := by
  unfold result_typed
  apply HOL.PredicateProducts.introduce_free
  apply HOL.PredicateProducts.introduce_free
  rw [HOL.ProofSyntax.functionExtensionalityFree_castIndices]
  apply result_at_free <;>
    simp [HOL.PredicateFixedPoint.weakenProof, HOL.ProofSyntax.prepend, RootEvidence.prepend,
      RootEvidence.rename, HOL.ProofSyntax.FunctionExtensionalityFree, baseTypedFree, methodTypedFree, rootsFree]

/-- The previously constructed raw constructor and selected field readbacks
supply every root premise of dependent elimination. -/
def encodedRoots (raw : HOL.RawVectorConstructors.Signature Base Const) (interface : EncodedConstructor.Interface raw)
    (context : HOL.Ctx Base) :
    RootEvidence (EncodedConstructor.operations raw interface) context (EncodedConstructor.assumptions raw interface context) := by
  intro occurrence
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun empty => Fin.elim0 empty)))) occurrence
  · exact .hyp ⟨0, by simp [EncodedConstructor.assumptions, EncodedConstructor.vectorAssumptions,
      SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩
  · exact .hyp ⟨1, by simp [EncodedConstructor.assumptions, EncodedConstructor.vectorAssumptions,
      SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩
  · exact SelectedProjections.head_law (EncodedConstructor.operations raw interface) (EncodedConstructor.choices raw interface)
      (.hyp ⟨2, by simp [EncodedConstructor.assumptions, EncodedConstructor.vectorAssumptions,
        SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩)
      (EncodedConstructor.injectivity raw interface context)
  · exact SelectedProjections.tail_law (EncodedConstructor.operations raw interface) (EncodedConstructor.choices raw interface)
      (.hyp ⟨3, by simp [EncodedConstructor.assumptions, EncodedConstructor.vectorAssumptions,
        SelectedProjections.assumptions, HOL.RawVectorConstructors.Signature.assumptions]⟩)
      (EncodedConstructor.injectivity raw interface context)

theorem encodedRoots_free (raw : HOL.RawVectorConstructors.Signature Base Const) (interface : EncodedConstructor.Interface raw)
    (context : HOL.Ctx Base) :
    ∀ occurrence, (encodedRoots raw interface context occurrence).FunctionExtensionalityFree := by
  intro occurrence
  fin_cases occurrence
  · trivial
  · trivial
  · exact SelectedProjections.head_law_free _ _ _ _ True.intro (EncodedConstructor.injectivity_free raw interface context)
  · exact SelectedProjections.tail_law_free _ _ _ _ True.intro (EncodedConstructor.injectivity_free raw interface context)

#print axioms method_at
#print axioms computed_apply
#print axioms recursion_step
#print axioms result_at
#print axioms result_typed
#print axioms result_typed_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.GuardedFamily
