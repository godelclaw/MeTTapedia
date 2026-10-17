import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSemantics

/-! # Membership evidence retained by the actual request telescope -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyEvidence

open _root_.CategoryTheory
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers ContextualLocalUniverses
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations Arguments
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

universe u
variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

private def headEvidence {n m : Nat} {context : ContextExpr (symbols D) m}
    {target : D.Carrier} {sort : HSort} {entry : D.Carrier × TermExpr (symbols D) n}
    {remaining : List (D.Carrier × TermExpr (symbols D) n)}
    {mapping : Substitution (symbols D) n m}
    (step : ContinuationSyntax.Step vertex context target sort entry remaining mapping) :
    Derivation (Theory vertex) (.term (ContinuationSyntax.nextContext context entry mapping)
      (.var 0) (typingType entry.1 (.var 1) (entry.2.substitute (weakenTwice mapping)))) := by
  have tree := deriveList (.variable (ContinuationSyntax.nextContext context entry mapping) 0)
    (.cons step.formed .nil)
  change Derivation (Theory vertex) (.term (ContinuationSyntax.nextContext context entry mapping)
    (.var 0) ((ContinuationSyntax.membership entry mapping).rename Fin.succ)) at tree
  have same : (ContinuationSyntax.membership entry mapping).rename Fin.succ =
      typingType entry.1 (.var 1) (entry.2.substitute (weakenTwice mapping)) := by
    unfold ContinuationSyntax.membership typingType
    apply congrArg (TypeExpr.family (S := symbols D) (.typing entry.1))
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ position =>
        simp only [Fin.cases_succ, TermExpr.rename_substitute]
        rfl
  rw [same] at tree
  exact tree

private theorem weakenTwice_comp {n m k : Nat} (mapping : Substitution (symbols D) n m)
    (later : Substitution (symbols D) (m + 2) k) :
    composeSubstitution (weakenTwice mapping) later =
      composeSubstitution mapping
        (composeSubstitution (fun position : Fin m => (.var position.succ.succ : TermExpr (symbols D) (m + 2))) later) := by
  funext position
  simp only [composeSubstitution, weakenTwice, TermExpr.substitute_rename]
  rfl

private def Witnesses {n m : Nat} {context : ContextExpr (symbols D) m}
    {target : D.Carrier} {sort : HSort} {relies : List (D.Carrier × TermExpr (symbols D) n)}
    (mapping : Substitution (symbols D) n m)
    (result : ContinuationSyntax.Result vertex context target sort relies) : Type :=
  ∀ position : Fin relies.length, Σ evidence : TermExpr (symbols D) result.size,
    Derivation (Theory vertex) (.term result.scope evidence
      (typingType relies[position].1 (result.values position)
        (relies[position].2.substitute (composeSubstitution mapping result.projection))))

private def prependWitnesses {n m : Nat} {context : ContextExpr (symbols D) m}
    {target : D.Carrier} {sort : HSort} {entry : D.Carrier × TermExpr (symbols D) n}
    {remaining : List (D.Carrier × TermExpr (symbols D) n)}
    {mapping : Substitution (symbols D) n m}
    (step : ContinuationSyntax.Step vertex context target sort entry remaining mapping)
    (result : ContinuationSyntax.Result vertex (ContinuationSyntax.nextContext context entry mapping) target sort remaining)
    (rest : Witnesses vertex (weakenTwice mapping) result) :
    Witnesses vertex mapping (ContinuationSyntax.prepend vertex step result) := by
  intro position
  cases position using Fin.cases with
  | zero =>
      let proof := headEvidence vertex step
      have there := deriveList (.substituteTerm result.scope
        (ContinuationSyntax.nextContext context entry mapping) result.projection (.var 0)
        (typingType entry.1 (.var 1) (entry.2.substitute (weakenTwice mapping))))
        (.cons result.projectionTyped (.cons proof .nil))
      refine ⟨result.projection 0, ?_⟩
      change Derivation (Theory vertex) (.term result.scope (result.projection 0)
        ((typingType entry.1 (.var 1) (entry.2.substitute (weakenTwice mapping))).substitute result.projection)) at there
      rw [typingType_substitute, TermExpr.substitute_comp] at there
      change Derivation (Theory vertex) (.term result.scope (result.projection 0)
        (typingType entry.1 (result.projection 1)
          (entry.2.substitute (composeSubstitution (weakenTwice mapping) result.projection)))) at there
      rw [weakenTwice_comp] at there
      change Derivation (Theory vertex) (.term result.scope (result.projection 0)
        (typingType entry.1 (result.projection 1)
          (entry.2.substitute (composeSubstitution mapping
            (composeSubstitution (fun position : Fin m => (.var position.succ.succ : TermExpr (symbols D) (m + 2))) result.projection)))))
      exact there
  | succ position =>
      obtain ⟨evidence, typed⟩ := rest position
      refine ⟨evidence, ?_⟩
      change Derivation (Theory vertex) (.term result.scope evidence
        (typingType remaining[position].1 (result.values position)
          (remaining[position].2.substitute (composeSubstitution mapping
            (composeSubstitution (fun position : Fin m => (.var position.succ.succ : TermExpr (symbols D) (m + 2))) result.projection)))))
      rw [weakenTwice_comp] at typed
      exact typed

private def witnesses {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Substitution (symbols D) n m) {context : ContextExpr (symbols D) m}
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin relies.length, Derivation (Theory vertex)
      (.term context (relies[position].2.substitute mapping) (codeType relies[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex) (.term context function (continuationAt target sort relies mapping))) :
    Witnesses vertex mapping
      (ContinuationSyntax.openAll vertex target sort relies mapping formed classifiers function typed) := by
  cases relies with
  | nil => intro position; exact Fin.elim0 position
  | cons entry remaining =>
      let step := ContinuationSyntax.openHead vertex target sort entry remaining mapping formed classifiers function typed
      rw [ContinuationSyntax.openAll]
      exact prependWitnesses vertex step
          (ContinuationSyntax.openAll vertex target sort remaining (weakenTwice mapping)
            step.formed step.classifiers step.function step.typed)
          (witnesses target sort remaining (weakenTwice mapping)
            step.formed step.classifiers step.function step.typed)
termination_by relies.length

variable {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (interface : Interface D.Carrier)

noncomputable section

abbrev model := Classifier.Model.model operational algebra vertex
abbrev parameterScope := ContinuationSemantics.parameterScope operational algebra vertex interface
abbrev requestScope := ContinuationSemantics.requestScope operational algebra vertex interface
abbrev requests := ContinuationSemantics.requests operational algebra vertex interface

def parameterClassifierTerm (position : Fin interface.relies.length) :
    TermExpr (symbols D) (arity interface) :=
  ((relyArguments interface)[ContinuationSemantics.relyPosition interface position].2).substitute
    (ContinuationSyntax.initialMapping interface)

def parameterClassifierTyped (position : Fin interface.relies.length) :
    Derivation (Theory vertex) (.term (parameters interface)
      (parameterClassifierTerm interface position) (codeType interface.relies[position].1 (arity interface))) := by
  have tree := ContinuationSyntax.initialClassifiers vertex interface
    (ContinuationSemantics.relyPosition interface position)
  unfold parameterClassifierTerm
  rw [ContinuationSemantics.relyEntry]
  rw [ContinuationSemantics.relyEntry] at tree
  exact tree

def parameterClassifier (position : Fin interface.relies.length) :
    (parameterScope vertex operational algebra interface).1 ⟶ Carrier.presheaf operational interface.relies[position].1 :=
  sectionName operational interface.relies[position].1
    (ContinuationSemantics.codeSectionOf operational algebra vertex
      (parameterScope vertex operational algebra interface) (parameters interface)
      (ContinuationSemantics.parameters_read operational algebra vertex interface)
      interface.relies[position].1 (parameterClassifierTerm interface position)
      (parameterClassifierTyped vertex interface position))

theorem parameterClassifier_read (position : Fin interface.relies.length) :
    (model vertex operational algebra).evaluateTerm (parameterScope vertex operational algebra interface)
      (parameterClassifierTerm interface position) =
      some (codeValue operational interface.relies[position].1
        (parameterClassifier vertex operational algebra interface position)) :=
  ContinuationSemantics.codeSectionOf_evaluates operational algebra vertex
    (parameterScope vertex operational algebra interface) (parameters interface)
    (ContinuationSemantics.parameters_read operational algebra vertex interface)
    interface.relies[position].1 (parameterClassifierTerm interface position)
    (parameterClassifierTyped vertex interface position)

def requestClassifierTerm (position : Fin interface.relies.length) :=
  (parameterClassifierTerm interface position).substitute
    (ContinuationSemantics.requestSyntax vertex interface).projection

def evidence (position : Fin interface.relies.length) :
    Σ term : TermExpr (symbols D) (ContinuationSemantics.requestSyntax vertex interface).size,
    Derivation (Theory vertex) (.term (ContinuationSemantics.requestSyntax vertex interface).scope term
      (typingType interface.relies[position].1 (ContinuationSemantics.relyValueTerm vertex interface position)
        (requestClassifierTerm vertex interface position))) := by
  have pair := witnesses vertex interface.target interface.resultSort (relyArguments interface)
    (ContinuationSyntax.initialMapping interface) (parametersFormed vertex interface)
    (ContinuationSyntax.initialClassifiers vertex interface) (.var (ContinuationSyntax.targetPosition interface))
    (ContinuationSyntax.initialFunction vertex interface) (ContinuationSemantics.relyPosition interface position)
  rcases pair with ⟨term, typed⟩
  refine ⟨term, ?_⟩
  rw [ContinuationSemantics.relyEntry] at typed
  have same : requestClassifierTerm vertex interface position =
      (classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length))).substitute
          (composeSubstitution (ContinuationSyntax.initialMapping interface)
            (ContinuationSemantics.requestSyntax vertex interface).projection) := by
    unfold requestClassifierTerm parameterClassifierTerm
    rw [ContinuationSemantics.relyEntry]
    exact TermExpr.substitute_comp _ _ _
  rw [same]
  exact typed

theorem requestClassifier_read (position : Fin interface.relies.length) :
    (model vertex operational algebra).evaluateTerm (requestScope vertex operational algebra interface)
      (requestClassifierTerm vertex interface position) =
      some (codeValue operational interface.relies[position].1
        ((requests vertex operational algebra interface).project ≫
          parameterClassifier vertex operational algebra interface position)) := by
  have read := (model vertex operational algebra).evaluateTerm_substitute
    (NativeLocalTypeOperations.products_substitution W) (parameterClassifierTerm interface position)
    (requestScope vertex operational algebra interface) (parameterScope vertex operational algebra interface)
    (ContinuationSemantics.requestSyntax vertex interface).projection
    (ModelSubstitution.ofEvaluated _ _ _ _ _ (ContinuationSemantics.projection_read operational algebra vertex interface))
    _ (parameterClassifier_read vertex operational algebra interface position)
  rw [Vectors.codeValue_substitution] at read
  exact read

/-- Every native request carries actual evidence for its rely code. -/
theorem rely_member (position : Fin interface.relies.length) (world : Wᵒᵖ)
    (request : (requestScope vertex operational algebra interface).1.obj world) :
    Code.Member (((requests vertex operational algebra interface).relies position).app world request)
      ((parameterClassifier vertex operational algebra interface position).app world
        ((requests vertex operational algebra interface).project.app world request)) := by
  let actual := requests vertex operational algebra interface
  let scope := requestScope vertex operational algebra interface
  have valueRead : (model vertex operational algebra).evaluateTerm scope
      (ContinuationSemantics.relyValueTerm vertex interface position) =
      some (codeValue operational interface.relies[position].1 (actual.relies position)) :=
    ContinuationSemantics.relyValue_evaluates operational algebra vertex interface position
  have memberRead := Classifier.Realization.typing_read operational algebra vertex scope interface.relies[position].1
    _ _ (actual.relies position)
    (actual.project ≫ parameterClassifier vertex operational algebra interface position)
    valueRead (requestClassifier_read vertex operational algebra interface position)
  obtain ⟨memberSection, _⟩ :=
    ((evidence vertex interface position).2.native_sound (model vertex operational algebra)
      (Classifier.Realization.realization operational algebra vertex)).termAt scope _
      (ContinuationSemantics.requests_read operational algebra vertex interface) memberRead
  exact (typingAt_inhabited_iff operational interface.relies[position].1 (actual.relies position)
    (actual.project ≫ parameterClassifier vertex operational algebra interface position) world request).mp
    ⟨memberSection.val ⟨world, request⟩⟩

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyEvidence
