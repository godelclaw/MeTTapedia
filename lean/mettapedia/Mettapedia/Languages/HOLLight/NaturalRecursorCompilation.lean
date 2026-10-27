import Mettapedia.Logic.HOL.NaturalRecursionProofs
import Mettapedia.Languages.HOLLight.ModelInterpretation
import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Compiling selected natural-recursion equations to primitive certificates

The selection term uses the actual source selection constant and its exact
type instance. The number operations retain their resolved source identities.
The emitted theorems are conditional on selection and recursion; applying
them to retained source facts is a separate replay operation. Both conditional
proofs compile under the empty axiom policy and have empty hypothesis sets.
The dependent result theorem additionally retains induction and the base/step
predicate guards as antecedents; it does not assume that all fibres are inhabited.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.NaturalRecursorCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

private def selectionAt (operand : Ty) (type : HOL.Ty AtomicTy) (matching : operand.toHOL = type) :
    HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection type) :=
  .const (.constant ModelInterpretation.selectionConstant
    (ModelInterpretation.selectionType operand)
    (by rw [ModelInterpretation.selectionType_toHOL, matching]))

private theorem selectionAt_is_source (operand : Ty) (type : HOL.Ty AtomicTy)
    (matching : operand.toHOL = type) :
    HOL.SelectionProofs.principle (selectionAt operand type matching) =
      ModelInterpretation.selectionFormula operand := by
  cases matching
  simp [selectionAt, HOL.SelectionProofs.principle, HOL.SelectionProofs.instanceFormula,
    ModelInterpretation.selectionFormula, HOL.weaken, HOL.rename, HOL.Rename.weaken]

def selection (number result : Ty) :
    HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection (number.toHOL.arr result.toHOL)) :=
  selectionAt (.function number result) _ (Ty.toHOL_function number result)

theorem selection_is_source (number result : Ty) :
    HOL.SelectionProofs.principle (selection number result) =
      ModelInterpretation.selectionFormula (.function number result) :=
  selectionAt_is_source _ _ _

def zero (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL)) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (HOL.NaturalRecursionProofs.zeroImplication (selection number result)
      origin next base method)
    (HOL.NaturalRecursionProofs.zeroImplication_free _ _ _ _ _) Naming.empty ("natural-recursion-zero", 0)

def successor (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (value : HOL.ClosedTerm Symbol number.toHOL) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (HOL.NaturalRecursionProofs.successorImplication (selection number result)
      origin next base method value)
    (HOL.NaturalRecursionProofs.successorImplication_free _ _ _ _ _ _) Naming.empty
    ("natural-recursion-successor", 0)

theorem zero_accepted (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL)) :
    (ProofSystem.checker emptyAxiomPolicy).check (zero number origin next result base method).proof.result
      (zero number origin next result base method).proof.certificate = true :=
  (zero number origin next result base method).proof.accepted

theorem successor_accepted (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (value : HOL.ClosedTerm Symbol number.toHOL) :
    (ProofSystem.checker emptyAxiomPolicy).check (successor number origin next result base method value).proof.result
      (successor number origin next result base method value).proof.certificate = true :=
  (successor number origin next result base method value).proof.accepted

theorem zero_axioms_empty (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL)) :
    (zero number origin next result base method).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (zero_accepted number origin next result base method)))

theorem successor_axioms_empty (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (value : HOL.ClosedTerm Symbol number.toHOL) :
    (successor number origin next result base method value).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (successor_accepted number origin next result base method value)))

theorem zero_hypotheses_empty (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL)) :
    (zero number origin next result base method).proof.result.sequent.hyp = ∅ :=
  (zero number origin next result base method).hypotheses_exact

theorem successor_hypotheses_empty (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (value : HOL.ClosedTerm Symbol number.toHOL) :
    (successor number origin next result base method value).proof.result.sequent.hyp = ∅ :=
  (successor number origin next result base method value).hypotheses_exact

def dependent (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (family : HOL.ClosedTerm Symbol (number.toHOL.arr (result.toHOL.arr .prop))) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (HOL.NaturalRecursionProofs.dependentImplication (selection number result)
      origin next base method family)
    (HOL.NaturalRecursionProofs.dependentImplication_free _ _ _ _ _ _) Naming.empty
    ("natural-recursion-dependent", 0)

theorem dependent_accepted (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (family : HOL.ClosedTerm Symbol (number.toHOL.arr (result.toHOL.arr .prop))) :
    (ProofSystem.checker emptyAxiomPolicy).check (dependent number origin next result base method family).proof.result
      (dependent number origin next result base method family).proof.certificate = true :=
  (dependent number origin next result base method family).proof.accepted

theorem dependent_axioms_empty (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (family : HOL.ClosedTerm Symbol (number.toHOL.arr (result.toHOL.arr .prop))) :
    (dependent number origin next result base method family).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _
      (dependent_accepted number origin next result base method family)))

theorem dependent_hypotheses_empty (number : Ty) (origin : HOL.ClosedTerm Symbol number.toHOL)
    (next : HOL.ClosedTerm Symbol (number.toHOL.arr number.toHOL)) (result : Ty)
    (base : HOL.ClosedTerm Symbol result.toHOL)
    (method : HOL.ClosedTerm Symbol (HOL.NaturalRecursionProofs.Method number.toHOL result.toHOL))
    (family : HOL.ClosedTerm Symbol (number.toHOL.arr (result.toHOL.arr .prop))) :
    (dependent number origin next result base method family).proof.result.sequent.hyp = ∅ :=
  (dependent number origin next result base method family).hypotheses_exact

#print axioms dependent_accepted
#print axioms dependent_axioms_empty
#print axioms selection_is_source
#print axioms zero_accepted
#print axioms successor_accepted
#print axioms zero_axioms_empty
#print axioms successor_axioms_empty

end Mettapedia.Languages.HOLLight.NaturalRecursorCompilation
