import Mettapedia.Logic.HOL.RecursiveSpacePredicate
import Mettapedia.Languages.HOLLight.RecursiveSpaceSourceReadback
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.InferenceOnlyReplay

/-!
# Primitive proof production for guarded recursive-space predicates

The signature takes the actual source bottom and constructor operations and
explicit shape, activity and edge predicates. Positive syntax generates its
monotonicity and fixed-point proofs. Both compile to the existing primitive
checker with an empty axiom policy. The datatype-specific guard definitions
remain separate source inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RecursiveSpacePredicate

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def fromSource (operations : RecursiveSpaceSourceReadback.Operations)
    (validShape : HOL.ClosedTerm Symbol (operations.number.toHOL.arr (operations.payload.toHOL.arr .prop)))
    (active : HOL.ClosedTerm Symbol (operations.payload.toHOL.arr (operations.number.toHOL.arr .prop)))
    (validEdge : HOL.ClosedTerm Symbol
      (operations.payload.toHOL.arr (operations.number.toHOL.arr (operations.space.toHOL.arr .prop)))) :
    HOL.RecursiveSpacePredicate.Signature Symbol where
  number := operations.number.toHOL
  payload := operations.payload.toHOL
  space := operations.space.toHOL
  bottom := operations.recursive.bottom
  construct := operations.recursive.construct
  validShape := validShape
  active := active
  validEdge := validEdge

def positiveMonotonicity {source : HOL.Ty AtomicTy}
    (code : HOL.PositivePredicate.Code Symbol source [source]) (origin : ProofExecution.Origin) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy (code.operator_monotone (assumptions := []))
    code.operator_monotone_functionExtensionalityFree Naming.empty origin

def positiveFixedPoint {source : HOL.Ty AtomicTy}
    (code : HOL.PositivePredicate.Code Symbol source [source]) (origin : ProofExecution.Origin) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy (code.fixed_point (assumptions := []))
    code.fixed_point_functionExtensionalityFree Naming.empty origin

def monotonicity (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :=
  positiveMonotonicity signature.code ("recursive-predicate-monotonicity",0)

def fixedPoint (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :=
  positiveFixedPoint signature.code ("recursive-predicate-fixed-point",0)

theorem monotonicity_accepted (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :
    (ProofSystem.checker emptyAxiomPolicy).check
      (monotonicity signature).proof.result (monotonicity signature).proof.certificate = true :=
  (monotonicity signature).proof.accepted

theorem fixedPoint_accepted (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :
    (ProofSystem.checker emptyAxiomPolicy).check
      (fixedPoint signature).proof.result (fixedPoint signature).proof.certificate = true :=
  (fixedPoint signature).proof.accepted

theorem monotonicity_axioms_empty (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :
    (monotonicity signature).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (monotonicity_accepted signature)))

theorem fixedPoint_axioms_empty (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :
    (fixedPoint signature).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ (fixedPoint_accepted signature)))

theorem monotonicity_hypotheses_empty (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :
    (monotonicity signature).proof.result.sequent.hyp = ∅ :=
  (monotonicity signature).hypotheses_exact

theorem fixedPoint_hypotheses_empty (signature : HOL.RecursiveSpacePredicate.Signature Symbol) :
    (fixedPoint signature).proof.result.sequent.hyp = ∅ :=
  (fixedPoint signature).hypotheses_exact

#print axioms monotonicity_accepted
#print axioms fixedPoint_accepted
#print axioms monotonicity_axioms_empty
#print axioms fixedPoint_axioms_empty

end Mettapedia.Languages.HOLLight.RecursiveSpacePredicate
