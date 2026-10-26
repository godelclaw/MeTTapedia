import Mettapedia.Languages.HOLLight.RecursiveSpacePredicateExamples

/-!
# Closed primitive-producer controls for positive predicate formulas

The recursive-space signature retains all five operation arguments at three
distinct source types. A second formula exercises disjunction and nested
quantifiers. Both monotonicity and fixed-point receipts use the empty policy;
changed conclusions are refused by the same checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpacePredicate.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

private theorem acceptance_transport (policy : AxiomPolicy) (first second : DecidablePred policy)
    (claim : Theorem) (certificate : ProofSystem.Certificate)
    (accepted : (@ProofSystem.checker policy first).check claim certificate = true) :
    (@ProofSystem.checker policy second).check claim certificate = true := by
  cases Subsingleton.elim first second
  exact accepted

def mixedMonotonicity := positiveMonotonicity mixedCode ("mixed-positive-monotonicity",0)

def mixedFixedPoint := positiveFixedPoint mixedCode ("mixed-positive-fixed-point",0)

def recursiveMonotoneProgram : HOL.ProofSyntax Symbol ([] : List (HOL.ClosedFormula Symbol))
    (HOL.PredicateFixedPoint.monotone signature.operator) := signature.code.operator_monotone

def recursiveFixedPointProgram : HOL.ProofSyntax Symbol ([] : List (HOL.ClosedFormula Symbol))
    (HOL.PredicateFixedPoint.equation signature.operator) := signature.code.fixed_point

theorem recursive_monotonicity_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    (monotonicity signature).proof.result (monotonicity signature).proof.certificate = true :=
  acceptance_transport _ _ _ _ _ (monotonicity_accepted signature)

theorem recursive_fixedPoint_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    (fixedPoint signature).proof.result (fixedPoint signature).proof.certificate = true :=
  acceptance_transport _ _ _ _ _ (fixedPoint_accepted signature)

theorem mixed_monotonicity_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    mixedMonotonicity.proof.result mixedMonotonicity.proof.certificate = true :=
  acceptance_transport _ _ _ _ _ mixedMonotonicity.proof.accepted

theorem mixed_fixedPoint_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    mixedFixedPoint.proof.result mixedFixedPoint.proof.certificate = true :=
  acceptance_transport _ _ _ _ _ mixedFixedPoint.proof.accepted

def proofs : List (String × RetainedCompilation.CheckedProof emptyAxiomPolicy) :=
  [("recursive-monotonicity",(monotonicity signature).proof),
   ("recursive-fixed-point",(fixedPoint signature).proof),
   ("mixed-monotonicity",mixedMonotonicity.proof),
   ("mixed-fixed-point",mixedFixedPoint.proof)]

def forged (proof : RetainedCompilation.CheckedProof emptyAxiomPolicy) : Theorem :=
  {proof.result with sequent := ⟨∅,CanonicalTerm.free ⟨Name.global "forged_positive_conclusion",Ty.bool⟩⟩}

def verdicts : List (String × Bool) := proofs.flatMap fun (name,proof) =>
  [(name ++ "/accepted",(ProofSystem.checker emptyAxiomPolicy).check proof.result proof.certificate),
   (name ++ "/forged-refused",!(ProofSystem.checker emptyAxiomPolicy).check (forged proof) proof.certificate)]

#print axioms recursive_monotonicity_accepted
#print axioms recursive_fixedPoint_accepted
#print axioms mixed_monotonicity_accepted
#print axioms mixed_fixedPoint_accepted

end Mettapedia.Languages.HOLLight.RecursiveSpacePredicate.Controls
