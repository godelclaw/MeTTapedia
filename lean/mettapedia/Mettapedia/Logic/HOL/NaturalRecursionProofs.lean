import Mettapedia.Logic.HOL.SelectionProofs
import Mettapedia.Logic.HOL.NaturalFacts

/-!
# Selecting a natural recursor and retaining its computation proofs

The recursor is the supplied Hilbert selection operator applied to the actual
zero/successor specification. Its equations are derived by retained HOL proof
programs from the selection principle and recursion existence theorem. The
method keeps HOL Light's result-before-predecessor argument order.

The proof constructors are generic in the number and result types and in
the ambient context. The final syntax comparison identifies the independent
natural-carrier statement already used at the source replay boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NaturalRecursionProofs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {number result : Ty Base}

abbrev Method (number result : Ty Base) := result ⇒ number ⇒ result

def equations (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (function : Term Const Γ (number ⇒ result)) : Formula Const Γ :=
  .and (.eq (.app function zero) base)
    (.all (.eq (.app (weaken function) (.app (weaken successor) (.var .vz)))
      (.app (.app (weaken method) (.app (weaken function) (.var .vz))) (.var .vz))))

def body (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result)) :
    Formula Const ((number ⇒ result) :: Γ) :=
  equations (weaken zero) (weaken successor) (weaken base) (weaken method) (.var .vz)

def statement (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (result : Ty Base) : Formula Const Γ :=
  .all (σ := result) (.all (σ := Method number result)
    (.ex (body (weaken (weaken zero)) (weaken (weaken successor)) (.var (.vs .vz)) (.var .vz))))

def recursor (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result)) :
    Term Const Γ (number ⇒ result) :=
  SelectionProofs.selected selection (body zero successor base method)

@[simp] theorem subst_equations {Γ' : Ctx Base} (substitution : Subst Const Γ Γ')
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (function : Term Const Γ (number ⇒ result)) :
    HOL.subst substitution (equations zero successor base method function) =
      equations (HOL.subst substitution zero) (HOL.subst substitution successor)
        (HOL.subst substitution base) (HOL.subst substitution method) (HOL.subst substitution function) := by
  simp [equations, HOL.subst, weaken, HOL.subst_rename, HOL.rename_subst, Subst.lift, Rename.weaken]

@[simp] theorem subst_body {Γ' : Ctx Base} (substitution : Subst Const Γ Γ')
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result)) :
    HOL.subst (Subst.lift substitution) (body zero successor base method) =
      body (HOL.subst substitution zero) (HOL.subst substitution successor)
        (HOL.subst substitution base) (HOL.subst substitution method) := by
  simp [body, subst_equations, HOL.subst, weaken, HOL.subst_rename, HOL.rename_subst,
    Subst.lift, Rename.weaken]

variable {Δ : List (Formula Const Γ)}

def existence (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (recursion : ProofSyntax Const Δ (statement zero successor result)) :
    ProofSyntax Const Δ (.ex (body zero successor base method)) := by
  have atBase := ProofSyntax.allE base recursion
  have atBase' : ProofSyntax Const Δ (.all (.ex
      (body (weaken zero) (weaken successor) (weaken base) (.var .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_ atBase
    simp [instantiate, HOL.subst, subst_body, Subst.single, Subst.lift]
    rfl
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE method atBase')
  simp [instantiate, HOL.subst, subst_body, Subst.single]

def computation (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (statement zero successor result)) :
    ProofSyntax Const Δ (equations zero successor base method (recursor selection zero successor base method)) := by
  apply ProofSyntax.castIndices rfl ?_
    (SelectionProofs.specification selection (body zero successor base method) choice
      (existence zero successor base method recursion))
  simp [body, instantiate, subst_equations, HOL.subst, Subst.single, recursor]

def atZero (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (statement zero successor result)) :
    ProofSyntax Const Δ (.eq (.app (recursor selection zero successor base method) zero) base) :=
  .andEL (computation selection zero successor base method choice recursion)

def atSuccessor (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (numberValue : Term Const Γ number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (statement zero successor result)) :
    ProofSyntax Const Δ
      (.eq (.app (recursor selection zero successor base method) (.app successor numberValue))
        (.app (.app method (.app (recursor selection zero successor base method) numberValue)) numberValue)) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.allE numberValue (.andER (computation selection zero successor base method choice recursion)))
  simp [instantiate, HOL.subst, Subst.single]

theorem source_statement :
    statement (Const := NaturalFacts.Const) NaturalFacts.zero (.const .successor) NaturalFacts.target =
      NaturalFacts.recursion := rfl

set_option backward.isDefEq.respectTransparency false in
theorem existence_free (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (recursion : ProofSyntax Const Δ (statement zero successor result))
    (free : recursion.FunctionExtensionalityFree) :
    (existence zero successor base method recursion).FunctionExtensionalityFree := by
  simpa [existence, ProofSyntax.FunctionExtensionalityFree] using free

set_option backward.isDefEq.respectTransparency false in
theorem computation_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (statement zero successor result))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (computation selection zero successor base method choice recursion).FunctionExtensionalityFree := by
  unfold computation
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact SelectionProofs.specification_free selection _ choice _ choiceFree
    (existence_free zero successor base method recursion recursionFree)

def zeroImplication (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result)) :
    ProofSyntax Const [] (.imp (SelectionProofs.principle selection)
      (.imp (statement zero successor result)
        (.eq (.app (recursor selection zero successor base method) zero) base))) :=
  .impI (.impI (atZero selection zero successor base method (.hyp 1) (.hyp 0)))

def successorImplication (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (value : Term Const Γ number) :
    ProofSyntax Const [] (.imp (SelectionProofs.principle selection)
      (.imp (statement zero successor result)
        (.eq (.app (recursor selection zero successor base method) (.app successor value))
          (.app (.app method (.app (recursor selection zero successor base method) value)) value)))) :=
  .impI (.impI (atSuccessor selection zero successor base method value (.hyp 1) (.hyp 0)))

theorem zeroImplication_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result)) :
    (zeroImplication selection zero successor base method).FunctionExtensionalityFree := by
  exact computation_free (Δ := [statement zero successor result, SelectionProofs.principle selection])
    selection zero successor base method (.hyp 1) (.hyp 0) trivial trivial

set_option backward.isDefEq.respectTransparency false in
theorem successorImplication_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (value : Term Const Γ number) :
    (successorImplication selection zero successor base method value).FunctionExtensionalityFree := by
  simpa [successorImplication, atSuccessor, ProofSyntax.FunctionExtensionalityFree] using
    computation_free (Δ := [statement zero successor result, SelectionProofs.principle selection])
      selection zero successor base method (.hyp 1) (.hyp 0) trivial trivial

/-- The ordinary induction statement, retaining the source conjunction of
the base case and the successor step. -/
def inductionPrinciple (zero : Term Const Γ number)
    (successor : Term Const Γ (number ⇒ number)) : Formula Const Γ :=
  .all (.imp (.and (.app (.var .vz) (weaken zero))
    (.all (.imp (.app (.var (.vs .vz)) (.var .vz))
      (.app (.var (.vs .vz)) (.app (weaken (weaken successor)) (.var .vz))))))
    (.all (.app (.var (.vs .vz)) (.var .vz))))

def inductionPremises (zero : Term Const Γ number)
    (successor : Term Const Γ (number ⇒ number))
    (predicate : Term Const Γ (number ⇒ .prop)) : Formula Const Γ :=
  .and (.app predicate zero)
    (.all (.imp (.app (weaken predicate) (.var .vz))
      (.app (weaken predicate) (.app (weaken successor) (.var .vz)))))

def inductionInstance (zero : Term Const Γ number)
    (successor : Term Const Γ (number ⇒ number))
    (predicate : Term Const Γ (number ⇒ .prop))
    (principle : ProofSyntax Const Δ (inductionPrinciple zero successor)) :
    ProofSyntax Const Δ (.imp (inductionPremises zero successor predicate)
      (.all (.app (weaken predicate) (.var .vz)))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE predicate principle)
  simp [inductionPremises, instantiate, HOL.subst, Subst.single, Subst.lift]
  rfl

theorem source_induction :
    inductionPrinciple (Const := NaturalFacts.Const) NaturalFacts.zero (.const .successor) =
      NaturalFacts.induction := rfl

/-- A result family is a predicate on the number and the represented result.
It may have empty fibres; no inhabitance assumption is added for them. -/
def holds (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (index : Term Const Γ number) (value : Term Const Γ result) : Formula Const Γ :=
  .app (.app family index) value

def methodPreserves (successor : Term Const Γ (number ⇒ number))
    (method : Term Const Γ (Method number result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop)) : Formula Const Γ :=
  .all (σ := number) (.all (σ := result)
    (.imp (holds (weaken (weaken family)) (.var (.vs .vz)) (.var .vz))
      (holds (weaken (weaken family))
        (.app (weaken (weaken successor)) (.var (.vs .vz)))
        (.app (.app (weaken (weaken method)) (.var .vz)) (.var (.vs .vz))))))

def graphPredicate (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (function : Term Const Γ (number ⇒ result)) : Term Const Γ (number ⇒ .prop) :=
  .lam (holds (weaken family) (.var .vz) (.app (weaken function) (.var .vz)))

@[simp] theorem rename_graphPredicate {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (function : Term Const Γ (number ⇒ result)) :
    HOL.rename ρ (graphPredicate family function) =
      graphPredicate (HOL.rename ρ family) (HOL.rename ρ function) := by
  simp [graphPredicate, holds, HOL.rename, weaken, HOL.rename_comp, Rename.lift, Rename.weaken]

@[simp] theorem rename_methodPreserves {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (successor : Term Const Γ (number ⇒ number))
    (method : Term Const Γ (Method number result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop)) :
    HOL.rename ρ (methodPreserves successor method family) =
      methodPreserves (HOL.rename ρ successor) (HOL.rename ρ method) (HOL.rename ρ family) := by
  simp [methodPreserves, holds, HOL.rename, weaken, HOL.rename_comp, Rename.lift, Rename.weaken]

@[simp] theorem rename_equations {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (function : Term Const Γ (number ⇒ result)) :
    HOL.rename ρ (equations zero successor base method function) =
      equations (HOL.rename ρ zero) (HOL.rename ρ successor) (HOL.rename ρ base)
        (HOL.rename ρ method) (HOL.rename ρ function) := by
  simp [equations, HOL.rename, weaken, HOL.rename_comp, Rename.lift, Rename.weaken]

def graphBeta (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (function : Term Const Γ (number ⇒ result)) (value : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (graphPredicate family function) value)
      (holds family value (.app function value))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta value (holds (weaken family) (.var .vz) (.app (weaken function) (.var .vz))))
  simp [graphPredicate, holds, instantiate, HOL.subst, Subst.single]

def preservedAt (successor : Term Const Γ (number ⇒ number))
    (method : Term Const Γ (Method number result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (index : Term Const Γ number) (value : Term Const Γ result)
    (preserves : ProofSyntax Const Δ (methodPreserves successor method family)) :
    ProofSyntax Const Δ (.imp (holds family index value)
      (holds family (.app successor index) (.app (.app method value) index))) := by
  have atIndex : ProofSyntax Const Δ (.all
      (.imp (holds (weaken family) (weaken index) (.var .vz))
        (holds (weaken family) (.app (weaken successor) (weaken index))
          (.app (.app (weaken method) (.var .vz)) (weaken index))))) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE index preserves)
    simp [holds, instantiate, HOL.subst, Subst.single, Subst.lift]
    rfl
  apply ProofSyntax.castIndices rfl ?_ (.allE value atIndex)
  simp [holds, instantiate, HOL.subst, Subst.single]

set_option backward.isDefEq.respectTransparency false in
/-- Lift the recursion equations to an arbitrary dependent predicate family.
The input induction proof and the two typing premises remain explicit.
All terms and proofs live in the same arbitrary ambient context. -/
def invariant (zero : Term Const Γ number)
    (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (function : Term Const Γ (number ⇒ result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (inductionProof : ProofSyntax Const Δ (inductionPrinciple zero successor))
    (computationProof : ProofSyntax Const Δ (equations zero successor base method function))
    (baseProof : ProofSyntax Const Δ (holds family zero base))
    (stepProof : ProofSyntax Const Δ (methodPreserves successor method family)) :
    ProofSyntax Const Δ (.all
      (holds (weaken family) (.var .vz) (.app (weaken function) (.var .vz)))) := by
  let predicate := graphPredicate family function
  have zeroTyped : ProofSyntax Const Δ (holds family zero (.app function zero)) :=
    .impE (.eqPropER (.eqAppArg (.app family zero) (.andEL computationProof))) baseProof
  have zeroPredicate : ProofSyntax Const Δ (.app predicate zero) :=
    .impE (.eqPropER (graphBeta family function zero)) zeroTyped
  have successorPredicate : ProofSyntax Const Δ
      (.all (.imp (.app (weaken predicate) (.var .vz))
        (.app (weaken predicate) (.app (weaken successor) (.var .vz))))) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let hypothesis := Term.app (weaken predicate) (.var .vz)
    have steps : ProofSyntax Const (hypothesis :: weakenHyps Δ)
        (methodPreserves (weaken successor) (weaken method) (weaken family)) := by
      apply ProofSyntax.castIndices rfl ?_
        (ProofSyntax.prepend hypothesis (stepProof.rename Rename.weaken))
      exact rename_methodPreserves _ _ _ _
    have equationsProof : ProofSyntax Const (hypothesis :: weakenHyps Δ)
        (equations (weaken zero) (weaken successor) (weaken base) (weaken method) (weaken function)) := by
      apply ProofSyntax.castIndices rfl ?_
        (ProofSyntax.prepend hypothesis (computationProof.rename Rename.weaken))
      exact rename_equations _ _ _ _ _ _
    have previous : ProofSyntax Const (hypothesis :: weakenHyps Δ)
        (holds (weaken family) (.var .vz) (.app (weaken function) (.var .vz))) := by
      apply ProofSyntax.impE (.eqPropEL (graphBeta (weaken family) (weaken function) (.var .vz)))
      apply ProofSyntax.castIndices rfl ?_
        (ProofSyntax.hyp (Const := Const) (Δ := hypothesis :: weakenHyps Δ) 0)
      simp [hypothesis, predicate, weaken]
    have next := ProofSyntax.impE
      (preservedAt (weaken successor) (weaken method) (weaken family)
        (.var .vz) (.app (weaken function) (.var .vz)) steps) previous
    have nextEquation : ProofSyntax Const (hypothesis :: weakenHyps Δ)
        (.eq (.app (weaken function) (.app (weaken successor) (.var .vz)))
          (.app (.app (weaken method) (.app (weaken function) (.var .vz))) (.var .vz))) := by
      apply ProofSyntax.castIndices rfl ?_ (.allE (.var .vz) (.andER equationsProof))
      simp [instantiate, HOL.subst, Subst.single]
    have nextTyped := ProofSyntax.impE
      (.eqPropER (.eqAppArg (.app (weaken family) (.app (weaken successor) (.var .vz)))
        nextEquation)) next
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (graphBeta (weaken family) (weaken function)
        (.app (weaken successor) (.var .vz)))) nextTyped)
    simp only [predicate, weaken, rename_graphPredicate]
  have every := ProofSyntax.impE (inductionInstance zero successor predicate inductionProof)
    (.andI zeroPredicate successorPredicate)
  apply ProofSyntax.allI
  have atIndex : ProofSyntax Const (weakenHyps Δ) (.app (weaken predicate) (.var .vz)) := by
    exact ContextualTrinity.instantiateFresh (every.rename Rename.weaken)
  apply ProofSyntax.impE (.eqPropEL (graphBeta (weaken family) (weaken function) (.var .vz)))
  apply ProofSyntax.castIndices rfl ?_ atIndex
  simp only [predicate, weaken, rename_graphPredicate]

set_option backward.isDefEq.respectTransparency false in
theorem invariant_free (zero : Term Const Γ number)
    (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (function : Term Const Γ (number ⇒ result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (inductionProof : ProofSyntax Const Δ (inductionPrinciple zero successor))
    (computationProof : ProofSyntax Const Δ (equations zero successor base method function))
    (baseProof : ProofSyntax Const Δ (holds family zero base))
    (stepProof : ProofSyntax Const Δ (methodPreserves successor method family))
    (inductionFree : inductionProof.FunctionExtensionalityFree)
    (computationFree : computationProof.FunctionExtensionalityFree)
    (baseFree : baseProof.FunctionExtensionalityFree)
    (stepFree : stepProof.FunctionExtensionalityFree) :
    (invariant zero successor base method function family
      inductionProof computationProof baseProof stepProof).FunctionExtensionalityFree := by
  simp [invariant, inductionInstance, graphBeta, preservedAt, ProofSyntax.prepend,
    ContextualTrinity.instantiateFresh, ContextualTrinity.castConclusion,
    ProofSyntax.FunctionExtensionalityFree, inductionFree, computationFree, baseFree, stepFree]

/-- Dependent result typing of the actual selected recursor, retaining all
five logical premises as proofs rather than semantic assumptions. -/
def dependent (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (statement zero successor result))
    (inductionProof : ProofSyntax Const Δ (inductionPrinciple zero successor))
    (baseProof : ProofSyntax Const Δ (holds family zero base))
    (stepProof : ProofSyntax Const Δ (methodPreserves successor method family)) :
    ProofSyntax Const Δ (.all (holds (weaken family) (.var .vz)
      (.app (weaken (recursor selection zero successor base method)) (.var .vz)))) :=
  invariant zero successor base method (recursor selection zero successor base method) family
    inductionProof (computation selection zero successor base method choice recursion) baseProof stepProof

def dependentImplication (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop)) :
    ProofSyntax Const [] (.imp (SelectionProofs.principle selection)
      (.imp (statement zero successor result) (.imp (inductionPrinciple zero successor)
        (.imp (holds family zero base) (.imp (methodPreserves successor method family)
          (.all (holds (weaken family) (.var .vz)
            (.app (weaken (recursor selection zero successor base method)) (.var .vz))))))))) :=
  .impI (.impI (.impI (.impI (.impI
    (dependent selection zero successor base method family (.hyp 4) (.hyp 3) (.hyp 2) (.hyp 1) (.hyp 0))))))

theorem dependentImplication_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (base : Term Const Γ result) (method : Term Const Γ (Method number result))
    (family : Term Const Γ (number ⇒ result ⇒ .prop)) :
    (dependentImplication selection zero successor base method family).FunctionExtensionalityFree := by
  simp only [dependentImplication, dependent, ProofSyntax.FunctionExtensionalityFree]
  exact invariant_free _ _ _ _ _ _ _ _ _ _ trivial
    (computation_free _ _ _ _ _ _ _ trivial trivial) trivial trivial

#print axioms invariant
#print axioms invariant_free
#print axioms source_induction
#print axioms dependent
#print axioms dependentImplication_free
#print axioms existence
#print axioms computation
#print axioms atZero
#print axioms atSuccessor
#print axioms source_statement
#print axioms zeroImplication_free
#print axioms successorImplication_free

end Mettapedia.Logic.HOL.NaturalRecursionProofs
