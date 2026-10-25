import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.InferenceOnlyReplay

/-!
# Primitive HOL Light proofs of least-predicate induction and unfolding

The retained source proofs quantify over a predicate operator and compile to
actual primitive receipt graphs. Their physical nodes contain no axiom
requests, so the same graphs replay under the empty policy. The fixed-point
schema keeps its monotonicity premise. These logical schemas do not supply a
datatype-specific carrier definition or its generated monotonicity proof.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PredicateFixedPoint
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

/-- A source type variable, retained for ordinary native type instantiation. -/
def element : AtomicTy := ⟨.var (Name.global "DatatypeElement"), rfl, rfl⟩

def fixedPoint := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PredicateFixedPoint.fixed_point_schema (Const := Symbol) (.base element))
  (HOL.PredicateFixedPoint.fixed_point_schema_functionExtensionalityFree (.base element))
  Naming.empty ("least-predicate-fixed-point", 0)

def induction := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PredicateFixedPoint.induction_schema (Const := Symbol) (.base element))
  (HOL.PredicateFixedPoint.induction_schema_functionExtensionalityFree (.base element))
  Naming.empty ("least-predicate-induction", 0)

theorem fixedPoint_accepted_empty : (ProofSystem.checker emptyAxiomPolicy).check
    fixedPoint.proof.result fixedPoint.proof.certificate = true := fixedPoint.proof.accepted

theorem induction_accepted_empty : (ProofSystem.checker emptyAxiomPolicy).check
    induction.proof.result induction.proof.certificate = true := induction.proof.accepted

set_option maxRecDepth 32768 in
theorem fixedPoint_inference_only :
    InferenceOnlyReplay.inferenceOnly fixedPoint.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance _ _ fixedPoint_accepted_empty

set_option maxRecDepth 8192 in
theorem induction_inference_only :
    InferenceOnlyReplay.inferenceOnly induction.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance _ _ induction_accepted_empty

set_option maxRecDepth 32768 in
theorem fixedPoint_axioms_empty : fixedPoint.proof.result.axioms = ∅ := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem induction_axioms_empty : induction.proof.result.axioms = ∅ := by
  decide +kernel

/-- The retained source statements are translated exactly, including the guard. -/
theorem fixedPoint_sequent :
    fixedPoint.proof.result.sequent.hyp = ∅ ∧
      fixedPoint.proof.result.sequent.concl = reverseCanonical Naming.empty
        (HOL.ImpredicativeConnectives.expand
          (.all (.imp
            (HOL.PredicateFixedPoint.monotone
              (.var .vz : HOL.Term Symbol [HOL.PredicateFixedPoint.Operator (.base element)]
                (HOL.PredicateFixedPoint.Operator (.base element))))
            (HOL.PredicateFixedPoint.equation (.var .vz))))) :=
  ⟨fixedPoint.hypotheses_exact, fixedPoint.conclusion_exact⟩

namespace Controls

def betaSource : HOL.ProofSyntax Symbol ([] : List (HOL.ClosedFormula Symbol))
    (.eq (.app (.lam (.var .vz)) (.top : HOL.ClosedFormula Symbol)) .top) :=
  .beta .top (.var .vz)

theorem betaSource_free : HOL.ProofSyntax.FunctionExtensionalityFree betaSource := by
  trivial

def betaCompiled := compileWithoutFunctionExtensionality emptyAxiomPolicy
  betaSource betaSource_free Naming.empty ("policy-beta-control", 0)

theorem betaCompiled_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    betaCompiled.proof.result betaCompiled.proof.certificate = true :=
  compileWithoutFunctionExtensionality_accepted emptyAxiomPolicy
    betaSource betaSource_free Naming.empty ("policy-beta-control", 0)

theorem betaCompiled_sequent :
    betaCompiled.proof.result.sequent.hyp = ∅ ∧
      betaCompiled.proof.result.sequent.concl = reverseCanonical Naming.empty
        (HOL.ImpredicativeConnectives.expand
          (.eq (.app (.lam (.var .vz)) (.top : HOL.ClosedFormula Symbol)) .top)) :=
  compileWithoutFunctionExtensionality_sequent emptyAxiomPolicy
    betaSource betaSource_free Naming.empty ("policy-beta-control", 0)

/-- The proof route, rather than its possible semantic validity, selects eta authority. -/
theorem etaSource_not_free : ¬ HOL.ProofSyntax.FunctionExtensionalityFree
    (HOL.ProofSyntax.eta (Δ := [])
      (.lam (.var .vz) : HOL.ClosedTerm Symbol (.arr .prop .prop))) := by
  intro impossible
  exact impossible

end Controls

/-- Runtime replay and dependency checks for both generated logical schemas. -/
def verdicts : List (String × Bool) :=
  [("least fixed point empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      fixedPoint.proof.result fixedPoint.proof.certificate),
   ("least induction empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      induction.proof.result induction.proof.certificate),
   ("least fixed point physical inference nodes", InferenceOnlyReplay.inferenceOnly
      fixedPoint.proof.certificate.1),
   ("least induction physical inference nodes", InferenceOnlyReplay.inferenceOnly
      induction.proof.certificate.1),
   ("least fixed point no axiom dependencies", decide (fixedPoint.proof.result.axioms = ∅)),
   ("least induction no axiom dependencies", decide (induction.proof.result.axioms = ∅)),
   ("policy-restricted beta replay", (ProofSystem.checker emptyAxiomPolicy).check
      Controls.betaCompiled.proof.result Controls.betaCompiled.proof.certificate)]

set_option maxRecDepth 32768 in
theorem verdicts_all : verdicts.all Prod.snd = true := by
  simp only [verdicts, List.all_cons, List.all_nil, Bool.and_eq_true,
    fixedPoint_accepted_empty, induction_accepted_empty, fixedPoint_inference_only,
    induction_inference_only, fixedPoint_axioms_empty, induction_axioms_empty,
    decide_true, Controls.betaCompiled_accepted, and_self]

#print axioms fixedPoint_accepted_empty
#print axioms induction_accepted_empty
#print axioms fixedPoint_axioms_empty
#print axioms induction_axioms_empty
#print axioms fixedPoint_sequent
end Mettapedia.Languages.HOLLight.PredicateFixedPoint
