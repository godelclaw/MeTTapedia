import Mettapedia.Languages.HOLLight.PointedPredicate

/-!
# Native instantiation of a generic pointed-predicate witness

One retained witness over a type parameter and a predicate variable is
specialized by the original HOL Light `INST_TYPE` and `INST` rules. The
computed certificate has exactly the requested pointed-predicate application,
with no hypotheses and no logical axiom dependencies. Inhabitance of the
original predicate is not assumed.

This is a proof producer. Registered declaration formation and availability,
source closedness and freshness, and native implementation refinement remain
separate obligations. The controls include an empty predicate, a
function-valued carrier, and refusal of a changed conclusion.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PointedPredicateInstantiation
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

private abbrev alphaName : Name := Name.global "PointedCarrierElement"
private def alpha : AtomicTy := ⟨.var alphaName,by exact ⟨rfl,rfl⟩⟩
private abbrev element : HOL.Ty AtomicTy := .base alpha

private def propertyVariable : SourceVar :=
  ⟨Name.global "pointedCarrierProperty",Ty.function (.var alphaName) Ty.bool⟩

private def property : HOL.ClosedTerm Symbol (.arr element .prop) :=
  .const (.variable propertyVariable (by
    change (Ty.function (.var alphaName) Ty.bool).toHOL = HOL.Ty.arr (HOL.Ty.base alpha) HOL.Ty.prop
    rw [Ty.toHOL_function,Ty.toHOL_bool]
    exact congrArg (fun source => HOL.Ty.arr source HOL.Ty.prop) (Ty.toHOL_of_isAtomic alpha.property)))

private def template := PointedPredicate.compileWitness property

private theorem accepted_other_instance (policy : AxiomPolicy) (first second : DecidablePred policy)
    (proof : @RetainedCompilation.CheckedProof policy first) :
    (@ProofSystem.checker policy second).check
      (@RetainedCompilation.CheckedProof.result policy first proof)
      (@RetainedCompilation.CheckedProof.certificate policy first proof) = true := by
  have same : first = second := Subsingleton.elim _ _
  cases same
  exact @RetainedCompilation.CheckedProof.accepted policy first proof

private def specializationTypes (target : Ty) : TypeSubst := ⟨[(alphaName,target)]⟩

def specialization {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) : TypeCorrectTermSubstitution :=
  let expression := reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand property)
  let source := PrimitiveTransport.checkedSource expression
  { raw := ⟨specializationTypes (reverseTy target),
      [(⟨propertyVariable.name, reverseTy (.arr target .prop)⟩,source)]⟩
    typeCorrect := by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      change (PrimitiveTransport.checkedSource expression).ty = _
      have same := PrimitiveTransport.checkedSource_exact expression
      have types := congrArg CanonicalTerm.ty same
      exact types }

def specializedProof {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    RetainedCompilation.CheckedProof emptyAxiomPolicy :=
  RetainedCompilation.CheckedProof.unary template.proof
    (substituteTheorem (specialization property) template.proof.result)
    (PrimitiveTransport.substitutionBlock (specialization property) template.proof.result
      ("pointed-predicate-specialization",0))
    (PrimitiveTransport.substitutionBlock_checked emptyAxiomPolicy (specialization property)
      template.proof.result ("pointed-predicate-specialization",0))
    ("pointed-predicate-specialization",0)

theorem specializedProof_accepted {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    (ProofSystem.checker emptyAxiomPolicy).check
      (specializedProof property).result (specializedProof property).certificate = true :=
  accepted_other_instance _ _ _ (specializedProof property)

#print axioms specializedProof_accepted

theorem specialized_conclusion {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    (specializedProof property).result.sequent.concl =
      reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand
        (.app (HOL.PointedPredicate.predicate property) (HOL.PointedPredicate.none target))) := by
  change (specialization property).apply template.proof.result.sequent.concl = _
  rw [template.conclusion_exact]
  apply CanonicalTerm.ext_term
  change (specialization property).raw.applyDB _ = _
  simp only [HOL.PointedPredicate.predicate, HOL.PointedPredicate.admitted,
    HOL.PointedPredicate.present, HOL.PointedPredicate.none, HOL.PointedPredicate.some,
    HOL.ImpredicativeConnectives.expand, HOL.weaken, HOL.ImpredicativeConnectives.expand_rename]
  simp [reverseCanonical_term, reverseTerm, reverseTermWith,
    HOL.ImpredicativeConnectives.expand, PrimitiveTransport.checkedSource_exact,
    HOL.ImpredicativeConnectives.disjunction, HOL.ImpredicativeConnectives.conjunction,
    HOL.ImpredicativeConnectives.existential, HOL.ImpredicativeConnectives.falsity,
    reverseTermWith_rename, reverseTermWith_eq_reverseTermWith_empty,
    HOL.rename, HOL.Rename.weaken, VarEnv.lift, shiftLoose,
    specialization, specializationTypes, TermSubst.applyDB, TypeSubst.apply_op,
    TypeSubst.lookup, TypeSubst.applyVar, TermSubst.lookup,
    TermSubst.keySame, reverseSymbol, element, alpha,
    propertyVariable, PointedPredicateInstantiation.property, reverseTy,
    CanonicalTerm.equalityDB, Ty.equality, Ty.function, Ty.bool,
    ExcludedMiddle.forallDB, ExcludedMiddle.impAppDB, ExcludedMiddle.impDB,
    ExcludedMiddle.andDB, ExcludedMiddle.boolBinaryTy, PrimitiveSentences.truthDB,
    PrimitiveSentences.identityBool, sourceVarSame_eq_true_iff, List.map_cons, List.map_nil,
    Option.getD_some]

#print axioms specialized_conclusion

theorem specialized_hypotheses {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    (specializedProof property).result.sequent.hyp = ∅ := by
  change (specialization property).applyHypotheses template.proof.result.sequent.hyp = ∅
  rw [template.hypotheses_exact]
  simp [TypeCorrectTermSubstitution.applyHypotheses, reverseHypotheses]

theorem specialized_axioms {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    (specializedProof property).result.axioms = ∅ := by
  exact axioms_eq_empty_of_emptyAxiomPolicy
    (derives_shared emptyAxiomPolicy ((ProofSystem.checker_authority emptyAxiomPolicy).sound
      _ _ (specializedProof_accepted property)))

theorem specialized_application {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    CanonicalTerm.ApplicationSemantics (PointedPredicate.canonicalPredicate property)
      (PointedPredicate.canonicalPoint target) (specializedProof property).result.sequent.concl := by
  refine ⟨reverseTy (HOL.PointedPredicate.Carrier target), Ty.bool, ?_, rfl, ?_⟩
  · exact Ty.destFunction?_function _ _
  rw [specialized_conclusion]
  rfl

theorem specialized_boolean {target : HOL.Ty AtomicTy}
    (property : HOL.ClosedTerm Symbol (.arr target .prop)) :
    (specializedProof property).result.sequent.concl.IsBool := by
  rw [specialized_conclusion]
  rfl

#print axioms specialized_hypotheses
#print axioms specialized_axioms
#print axioms specialized_application
#print axioms specialized_boolean

namespace Controls

def falseProperty : HOL.ClosedTerm Symbol (.arr .prop .prop) := .lam .bot

def falseConclusion : CanonicalTerm :=
  reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand (HOL.Term.bot : HOL.ClosedFormula Symbol))

def changedClaim : Theorem :=
  { (specializedProof falseProperty).result with
    sequent := ⟨∅,falseConclusion⟩ }

theorem empty_predicate_has_pointed_witness :
    (ProofSystem.checker emptyAxiomPolicy).check
      (specializedProof falseProperty).result (specializedProof falseProperty).certificate = true :=
  specializedProof_accepted falseProperty

theorem false_conclusion_different :
    (specializedProof falseProperty).result.sequent.concl ≠ falseConclusion := by
  rw [specialized_conclusion]
  decide +kernel

theorem changed_conclusion_refused :
    (ProofSystem.checker emptyAxiomPolicy).check changedClaim
      (specializedProof falseProperty).certificate ≠ true := by
  intro accepted
  have same := RetainedCompilation.CheckedProof.checked_claim_eq (specializedProof falseProperty) changedClaim accepted
  have conclusion := congrArg (fun fact : Theorem => fact.sequent.concl) same
  exact false_conclusion_different conclusion.symm

def functionProperty : HOL.ClosedTerm Symbol (.arr (.arr .prop .prop) .prop) :=
  .lam (.app (.var .vz) .top)

theorem function_property_specialization :
    CanonicalTerm.ApplicationSemantics (PointedPredicate.canonicalPredicate functionProperty)
      (PointedPredicate.canonicalPoint (.arr .prop .prop))
      (specializedProof functionProperty).result.sequent.concl :=
  specialized_application functionProperty

theorem closed_empty_conclusion :
    (specializedProof falseProperty).result.sequent.concl =
      reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand
        (.app (HOL.PointedPredicate.predicate falseProperty) (HOL.PointedPredicate.none .prop))) :=
  specialized_conclusion falseProperty

theorem closed_empty_hypotheses : (specializedProof falseProperty).result.sequent.hyp = ∅ :=
  specialized_hypotheses falseProperty

theorem closed_empty_axioms : (specializedProof falseProperty).result.axioms = ∅ :=
  specialized_axioms falseProperty

theorem closed_empty_boolean : (specializedProof falseProperty).result.sequent.concl.IsBool :=
  specialized_boolean falseProperty

end Controls
#print axioms Controls.empty_predicate_has_pointed_witness
#print axioms Controls.changed_conclusion_refused
end Mettapedia.Languages.HOLLight.PointedPredicateInstantiation
