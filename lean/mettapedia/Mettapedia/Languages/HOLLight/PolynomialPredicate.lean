import Mettapedia.Logic.HOL.PolynomialPredicate
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.InferenceOnlyReplay

/-!
# Empty-policy primitive proofs for polynomial predicate operators

Both programs quantify over constructor and child relations at two source type
variables. Monotonicity is generated from the actual positive operator body.
The fixed-point program instantiates the retained generic theorem and supplies
that generated proof. The resulting pointwise law has no external
monotonicity premise. These are primitive proof graphs, not native datatype
definition or recursive-function packages.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PolynomialPredicate
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def source : AtomicTy := ⟨.var (Name.global "PolynomialSource"), rfl, rfl⟩
def layer : AtomicTy := ⟨.var (Name.global "PolynomialLayer"), rfl, rfl⟩

def monotonicity := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PolynomialPredicate.monotonicity_schema (Const := Symbol) (.base source) (.base layer))
  (HOL.PolynomialPredicate.monotonicity_schema_functionExtensionalityFree (.base source) (.base layer))
  Naming.empty ("polynomial-predicate-monotonicity", 0)

def fixedPoint := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PolynomialPredicate.fixed_point_schema (Const := Symbol) (.base source) (.base layer))
  (HOL.PolynomialPredicate.fixed_point_schema_functionExtensionalityFree (.base source) (.base layer))
  Naming.empty ("polynomial-predicate-fixed-point", 0)

theorem monotonicity_accepted_empty : (ProofSystem.checker emptyAxiomPolicy).check
    monotonicity.proof.result monotonicity.proof.certificate = true := monotonicity.proof.accepted

theorem fixedPoint_accepted_empty : (ProofSystem.checker emptyAxiomPolicy).check
    fixedPoint.proof.result fixedPoint.proof.certificate = true := fixedPoint.proof.accepted

set_option maxRecDepth 65536 in
theorem monotonicity_inference_only :
    InferenceOnlyReplay.inferenceOnly monotonicity.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance _ _ monotonicity_accepted_empty

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem fixedPoint_inference_only :
    InferenceOnlyReplay.inferenceOnly fixedPoint.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance
    fixedPoint.proof.result fixedPoint.proof.certificate fixedPoint_accepted_empty

set_option maxRecDepth 65536 in
theorem monotonicity_axioms_empty : monotonicity.proof.result.axioms = ∅ := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem fixedPoint_axioms_empty : fixedPoint.proof.result.axioms = ∅ := by
  decide +kernel

def verdicts : List (String × Bool) :=
  [("polynomial monotonicity empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      monotonicity.proof.result monotonicity.proof.certificate),
   ("polynomial fixed point empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      fixedPoint.proof.result fixedPoint.proof.certificate),
   ("polynomial monotonicity physical inference graph", InferenceOnlyReplay.inferenceOnly monotonicity.proof.certificate.1),
   ("polynomial fixed point physical inference graph", InferenceOnlyReplay.inferenceOnly fixedPoint.proof.certificate.1),
   ("polynomial monotonicity no axiom dependencies", decide (monotonicity.proof.result.axioms = ∅)),
   ("polynomial fixed point no axiom dependencies", decide (fixedPoint.proof.result.axioms = ∅))]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem verdicts_all : ∀ result ∈ verdicts, result.2 = true := by
  intro result present
  simp only [verdicts, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact monotonicity_accepted_empty
  · exact fixedPoint_accepted_empty
  · exact monotonicity_inference_only
  · exact fixedPoint_inference_only
  · simpa using monotonicity_axioms_empty
  · simpa using fixedPoint_axioms_empty

set_option maxRecDepth 65536 in
theorem monotonicity_verdict : (ProofSystem.checker emptyAxiomPolicy).check
    monotonicity.proof.result monotonicity.proof.certificate = true :=
  verdicts_all
    ("polynomial monotonicity empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      monotonicity.proof.result monotonicity.proof.certificate)
    (by exact List.mem_cons_self)

#print axioms monotonicity_accepted_empty
#print axioms fixedPoint_accepted_empty
end Mettapedia.Languages.HOLLight.PolynomialPredicate
