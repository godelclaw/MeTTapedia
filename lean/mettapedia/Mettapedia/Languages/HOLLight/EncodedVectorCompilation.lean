import Mettapedia.Logic.HOL.ConstructorInjectivity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorEncodedConstructor
import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Native certificates for the encoded Vec constructor and computation rows

Full raw-constructor injectivity is reduced to the field interface once.
The encoded constructor's field theorem is compiled separately so callers
can cache and reuse it when discharging the original Vec rows. Every output
retains its exact hypotheses until checked source facts discharge them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.EncodedVectorCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows
open RetainedCompilation ReverseTranslation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated

variable (raw : HOL.RawVectorConstructors.Signature AtomicTy Symbol)
  (interface : EncodedConstructor.Interface raw)

@[irreducible, noinline] def constructorFields :
    Compiled emptyAxiomPolicy Naming.empty []
      (HOL.ImpredicativeConnectives.expand (.imp (HOL.ConstructorInjectivity.statement raw.construct)
        (HOL.ConstructorProjections.fieldInjective raw.construct))) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (HOL.ConstructorInjectivity.fields raw.construct (Δ := []))
    (HOL.ConstructorInjectivity.fields_free raw.construct) Naming.empty ("constructor-field-injectivity", 0)

@[irreducible, noinline] def vectorFields :
    Compiled emptyAxiomPolicy Naming.empty ((raw.assumptions []).map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (HOL.ConstructorProjections.fieldInjective raw.cons)) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy raw.field_injective raw.field_injective_free
    Naming.empty ("encoded-vector-field-injectivity", 0)

@[irreducible, noinline] def row (selected : Row)
    (names : Naming (selected.parameters (EncodedConstructor.operations raw interface))) :
    Compiled emptyAxiomPolicy names
      ((SelectedProjections.assumptions (EncodedConstructor.operations raw interface)
        (EncodedConstructor.choices raw interface) (selected.parameters (EncodedConstructor.operations raw interface))).map
          HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (.eq (selected.leftCode (EncodedConstructor.operations raw interface))
        (selected.rightCode (EncodedConstructor.operations raw interface)))) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (SelectedProjections.rowProof (EncodedConstructor.operations raw interface) (EncodedConstructor.choices raw interface) selected)
    (SelectedProjections.rowProof_free (EncodedConstructor.operations raw interface) (EncodedConstructor.choices raw interface) selected)
    names ("encoded-vector-computation", selected.address.val)

/-- Read both original source endpoints before applying the compiler's
primitive Boolean encoding. This does not inspect a compiled proof result. -/
def readRowConclusion? [DecidableEq AtomicTy] (operations : Operations AtomicTy Symbol) (selected : Row)
    (names : Naming (selected.parameters operations)) : Option CanonicalTerm := do
  let first ← AnnotatedPredicateReading.Reader.infer? operations.lexicalReading
    (selected.parameters operations) (liftTm (selected.rawLeft operations))
  let second ← AnnotatedPredicateReading.Reader.infer? operations.lexicalReading
    (selected.parameters operations) (liftTm (selected.rawRight operations))
  let left := reverseCanonical names (HOL.ImpredicativeConnectives.expand first.2)
  let right := reverseCanonical names (HOL.ImpredicativeConnectives.expand second.2)
  if same : left.ty.same right.ty = true then
    some (CanonicalTerm.equalityOfSameType left right ((Ty.same_eq_true_iff _ _).mp same))
  else none

theorem readRowConclusion_exact [DecidableEq AtomicTy] (operations : Operations AtomicTy Symbol) (selected : Row)
    (names : Naming (selected.parameters operations)) :
    readRowConclusion? operations selected names = some
      (reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (.eq (selected.leftCode operations) (selected.rightCode operations)))) := by
  unfold readRowConclusion?
  rw [AnnotatedPredicateReading.Reader.infer?_complete (selected.left_reads operations)]
  simp only [Bind.bind, Option.bind_some]
  rw [AnnotatedPredicateReading.Reader.infer?_complete (selected.right_reads operations)]
  simp only [Option.bind_some, reverseCanonical_ty, (Ty.same_eq_true_iff _ _).mpr rfl, dif_pos]
  rfl

theorem row_reader_agrees [DecidableEq AtomicTy] (selected : Row)
    (names : Naming (selected.parameters (EncodedConstructor.operations raw interface))) :
    readRowConclusion? (EncodedConstructor.operations raw interface) selected names =
      some (row raw interface selected names).proof.result.sequent.concl := by
  rw [(row raw interface selected names).conclusion_exact]
  exact readRowConclusion_exact _ _ _

/-- Logical equivalence of presentations is not literal equality of their
unexpanded source terms. -/
theorem unexpanded_truth_differs :
    reverseCanonical Naming.empty (HOL.Term.top : HOL.ClosedFormula Symbol) ≠
      reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand (HOL.Term.top : HOL.ClosedFormula Symbol)) := by
  decide +kernel

theorem constructorFields_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    (constructorFields raw).proof.result (constructorFields raw).proof.certificate = true :=
  (constructorFields raw).proof.accepted

theorem vectorFields_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    (vectorFields raw).proof.result (vectorFields raw).proof.certificate = true :=
  (vectorFields raw).proof.accepted

theorem row_accepted (selected : Row)
    (names : Naming (selected.parameters (EncodedConstructor.operations raw interface))) :
    (ProofSystem.checker emptyAxiomPolicy).check (row raw interface selected names).proof.result
      (row raw interface selected names).proof.certificate = true :=
  (row raw interface selected names).proof.accepted

theorem row_sequent (selected : Row)
    (names : Naming (selected.parameters (EncodedConstructor.operations raw interface))) :
    (row raw interface selected names).proof.result.sequent.hyp =
      reverseHypotheses names ((SelectedProjections.assumptions (EncodedConstructor.operations raw interface)
        (EncodedConstructor.choices raw interface) (selected.parameters (EncodedConstructor.operations raw interface))).map
          HOL.ImpredicativeConnectives.expand) ∧
    (row raw interface selected names).proof.result.sequent.concl =
      reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (.eq (selected.leftCode (EncodedConstructor.operations raw interface)) (selected.rightCode (EncodedConstructor.operations raw interface)))) :=
  ⟨(row raw interface selected names).hypotheses_exact, (row raw interface selected names).conclusion_exact⟩

theorem row_axioms_empty (selected : Row)
    (names : Naming (selected.parameters (EncodedConstructor.operations raw interface))) :
    (row raw interface selected names).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (row_accepted raw interface selected names)))

#print axioms constructorFields_accepted
#print axioms vectorFields_accepted
#print axioms row_accepted
#print axioms row_sequent
#print axioms row_axioms_empty
#print axioms readRowConclusion_exact
#print axioms row_reader_agrees
#print axioms unexpanded_truth_differs
end Mettapedia.Languages.HOLLight.EncodedVectorCompilation
