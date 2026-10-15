import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComposition
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneEvaluation

/-!
# Independent fixed-point meaning of arbitrary checked native operators

Induction and coinduction restrict the actual predicate context to its
pre-fixed or post-fixed guard. Hereditary monotonicity is earned by the
checked native proposition. Complete predicate naming proves the converse
inequalities against the independently defined lattice fixed points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComparison

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions NativeMonotoneReadout
open NativeMonotoneNaming NativeMonotoneBaseChange NativeMonotoneComposition NativeMonotoneEvaluation
open NativeFixedPointEncodings

universe u
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem transformed_action (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    transformed A operator = action (argumentType A)
      (weakenOperator A operator (totalProjection (predicate A).decoded)) (boundMembership A) := by
  rw [action, bound_body]
  change predicateBody (argumentType A) _ = predicateBody (argumentType A)
    (applyValue (predicate (argumentType A)) _
      (predicateName (argumentType A) (predicateBody (argumentType A) (generic A))))
  rw [predicateName_body]

theorem guarded_pre_closed (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    let guard := preGuard A operator
    operatorAtTwice A operator certified (totalProjection (predicate A).decoded) guard.ι
      ((boundMembership A).preimage (totalReindexMap guard.ι (argumentType A).decoded)) ≤
        (boundMembership A).preimage (totalReindexMap guard.ι (argumentType A).decoded) := by
  dsimp only
  change action ((argumentType A).reindex (preGuard A operator).ι)
    (weakenOperator (argumentType A) (weakenOperator A operator (totalProjection (predicate A).decoded))
      (preGuard A operator).ι) _ ≤ _
  rw [← action_substitution, ← transformed_action]
  have deduction := le_himp_iff.mp ((galois_preimage_forallAlong
    (totalProjection (argumentType A).decoded)).l_u_le
      (transformed A operator ⇨ boundMembership A))
  rw [← preGuard_body] at deduction
  intro world value held
  exact deduction world ⟨value.1.property,held⟩

theorem guarded_post_closed (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    let guard := postGuard A operator
    (boundMembership A).preimage (totalReindexMap guard.ι (argumentType A).decoded) ≤
      operatorAtTwice A operator certified (totalProjection (predicate A).decoded) guard.ι
        ((boundMembership A).preimage (totalReindexMap guard.ι (argumentType A).decoded)) := by
  dsimp only
  change _ ≤ action ((argumentType A).reindex (postGuard A operator).ι)
    (weakenOperator (argumentType A) (weakenOperator A operator (totalProjection (predicate A).decoded))
      (postGuard A operator).ι) _
  rw [← action_substitution, ← transformed_action]
  have deduction := le_himp_iff.mp ((galois_preimage_forallAlong
    (totalProjection (argumentType A).decoded)).l_u_le
      (boundMembership A ⇨ transformed A operator))
  rw [← postGuard_body] at deduction
  intro world value held
  exact deduction world ⟨value.1.property,held⟩

theorem inductive_guard (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    (leastEncoding (semanticOperator A operator certified)).preimage (FixedPointEvaluation.atomProjection A) ⊓
      (preGuard A operator).preimage (totalProjection (argumentType A).decoded) ≤ boundMembership A := by
  have restricted := least_induction
    (operatorAtTwice A operator certified (totalProjection (predicate A).decoded) (preGuard A operator).ι)
    ((boundMembership A).preimage (totalReindexMap (preGuard A operator).ι (argumentType A).decoded))
    (guarded_pre_closed A operator certified)
  rw [← least_local_substitution, ← NativeMonotoneBaseChange.least_substitution] at restricted
  intro world value held
  exact restricted world
    (show (⟨⟨value.1,held.2⟩,value.2⟩ :
      (totalSpace ((argumentType A).reindex (preGuard A operator).ι).decoded).obj world) ∈
        (((leastEncoding (semanticOperator A operator certified)).preimage
          (totalReindexMap (totalProjection (predicate A).decoded) A.decoded)).preimage
            (totalReindexMap (preGuard A operator).ι (argumentType A).decoded)).obj world from held.1)

theorem coinductive_guard (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    boundMembership A ⊓ (postGuard A operator).preimage (totalProjection (argumentType A).decoded) ≤
      (greatestEncoding (semanticOperator A operator certified)).preimage (FixedPointEvaluation.atomProjection A) := by
  have restricted := greatest_coinduction
    (operatorAtTwice A operator certified (totalProjection (predicate A).decoded) (postGuard A operator).ι)
    ((boundMembership A).preimage (totalReindexMap (postGuard A operator).ι (argumentType A).decoded))
    (guarded_post_closed A operator certified)
  rw [← greatest_local_substitution, ← NativeMonotoneBaseChange.greatest_substitution] at restricted
  intro world value held
  exact restricted world
    (show (⟨⟨value.1,held.2⟩,value.2⟩ :
      (totalSpace ((argumentType A).reindex (postGuard A operator).ι).decoded).obj world) ∈
        ((boundMembership A).preimage (totalReindexMap (postGuard A operator).ι (argumentType A).decoded)).obj
          world from held.1)

theorem preimage_meet {X Y : Cᵒᵖ ⥤ Type u} (left right : Subfunctor Y) (map : X ⟶ Y) :
    (left ⊓ right).preimage map = left.preimage map ⊓ right.preimage map := rfl

theorem tester_square (A : NativeType P) (value : A.decoded.sections) :
    sectionLift (argumentType A).decoded
      (ContextualLocalUniverses.substituteTerm (type := A) value
        (totalProjection (predicate A).decoded)) ≫ FixedPointEvaluation.atomProjection A =
      totalProjection (predicate A).decoded ≫ sectionLift A.decoded value :=
  Mettapedia.TypeTheory.ContextualTypeOperations.selfExtend_substitution
    (C := (NativeModel C).toCwf) (totalProjection (predicate A).decoded) value

theorem meaning_le_least (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections) :
    (leastEncoding (semanticOperator A operator certified)).preimage (sectionLift A.decoded value) ≤
      least A operator value := by
  apply (preimage_le_iff_le_forallAlong (totalProjection (predicate A).decoded) _ _).mp
  apply le_himp_iff.mpr
  have comparison := inductive_guard A operator certified
  let tester := sectionLift (argumentType A).decoded
    (ContextualLocalUniverses.substituteTerm (type := A) value (totalProjection (predicate A).decoded))
  have pulled : ((leastEncoding (semanticOperator A operator certified)).preimage
      (FixedPointEvaluation.atomProjection A) ⊓
        (preGuard A operator).preimage (totalProjection (argumentType A).decoded)).preimage tester ≤
          (boundMembership A).preimage tester := fun world _ held => comparison world held
  dsimp only [tester] at pulled
  simp only [preimage_meet, bound_tested, ← Subfunctor.preimage_comp,
    tester_square, projection_section] at pulled
  exact pulled

theorem greatest_le_meaning (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections) :
    greatest A operator value ≤
      (greatestEncoding (semanticOperator A operator certified)).preimage (sectionLift A.decoded value) := by
  apply (Subfunctor.image_le_iff _ (totalProjection (predicate A).decoded) _).mpr
  have comparison := coinductive_guard A operator certified
  let tester := sectionLift (argumentType A).decoded
    (ContextualLocalUniverses.substituteTerm (type := A) value (totalProjection (predicate A).decoded))
  have pulled : (boundMembership A ⊓
      (postGuard A operator).preimage (totalProjection (argumentType A).decoded)).preimage tester ≤
        ((greatestEncoding (semanticOperator A operator certified)).preimage
          (FixedPointEvaluation.atomProjection A)).preimage tester := fun world _ held => comparison world held
  dsimp only [tester] at pulled
  simp only [preimage_meet, bound_tested, ← Subfunctor.preimage_comp,
    tester_square, projection_section] at pulled
  rw [inf_comm]
  exact pulled

theorem named_operator (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : (predicate A).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨operatorType (argumentType A),weakenOperator A operator (totalProjection (predicate A).decoded)⟩ :
        NativeValue (totalSpace (predicate A).decoded))
      (sectionLift (predicate A).decoded candidate) = ⟨operatorType A,operator⟩ := by
  have normalized := operatorValue_substitution A operator (totalProjection (predicate A).decoded)
  exact (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
    Value.substitute (K := (NativeModel C).toCwf) value (sectionLift (predicate A).decoded candidate))
    normalized.symm).trans
      (value_weaken_beta (predicate A) (⟨operatorType A,operator⟩ : NativeValue P) candidate)

theorem named_application (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : (predicate A).decoded.sections) :
    (⟨predicate ((argumentType A).reindex (sectionLift (predicate A).decoded candidate)),
      weakenFunction (argumentType A)
        (applyValue (predicate (argumentType A))
          (weakenOperator A operator (totalProjection (predicate A).decoded)) (generic A))
        (sectionLift (predicate A).decoded candidate)⟩ : NativeValue P) =
      ⟨predicate A,applyValue (predicate A) operator candidate⟩ := by
  rw [operatorApplication_substitution]
  apply applyValue_values_equal
  · exact (operatorValue_substitution (argumentType A) _ _).symm.trans (named_operator A operator candidate)
  · exact weakened_generic_beta A candidate

theorem named_preGuard (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : Subfunctor (totalSpace A.decoded)) (closed : action A operator candidate ≤ candidate) :
    (preGuard A operator).preimage (sectionLift (predicate A).decoded (predicateName A candidate)) = ⊤ := by
  rw [preGuard, inclusionMeaning_substitution]
  have naming := inclusion_values_equal (named_argument_type A (predicateName A candidate))
    _ _ _ _ (named_application A operator (predicateName A candidate))
      (weakened_generic_beta A (predicateName A candidate))
  rw [naming, inclusionMeaning_top_iff, predicateBody_name]
  exact closed

theorem named_postGuard (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (candidate : Subfunctor (totalSpace A.decoded)) (closed : candidate ≤ action A operator candidate) :
    (postGuard A operator).preimage (sectionLift (predicate A).decoded (predicateName A candidate)) = ⊤ := by
  rw [postGuard, inclusionMeaning_substitution]
  have naming := inclusion_values_equal (named_argument_type A (predicateName A candidate))
    _ _ _ _ (weakened_generic_beta A (predicateName A candidate))
      (named_application A operator (predicateName A candidate))
  rw [naming, inclusionMeaning_top_iff, predicateBody_name]
  exact closed

theorem least_le_meaning (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections) :
    least A operator value ≤
      (leastEncoding (semanticOperator A operator certified)).preimage (sectionLift A.decoded value) := by
  let candidate := leastEncoding (semanticOperator A operator certified)
  let naming := sectionLift (predicate A).decoded (predicateName A candidate)
  have guard : (preGuard A operator).preimage naming = ⊤ :=
    named_preGuard A operator candidate (least_unfold (semanticOperator A operator certified)).le
  have application : (FixedPointEvaluation.testedMembership A value).preimage naming =
      candidate.preimage (sectionLift A.decoded value) := tested_reified A value candidate
  have deduction := (galois_preimage_forallAlong (totalProjection (predicate A).decoded)).l_u_le
    (preGuard A operator ⇨ FixedPointEvaluation.testedMembership A value)
  intro world parameter held
  have result : parameter ∈ ((preGuard A operator ⇨ FixedPointEvaluation.testedMembership A value).preimage
      naming).obj world := deduction world (show naming.app world parameter ∈
        ((least A operator value).preimage (totalProjection (predicate A).decoded)).obj world from held)
  rw [preimage_himp, guard, application, top_himp] at result
  exact result

theorem meaning_le_greatest (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections) :
    (greatestEncoding (semanticOperator A operator certified)).preimage (sectionLift A.decoded value) ≤
      greatest A operator value := by
  let candidate := greatestEncoding (semanticOperator A operator certified)
  let naming := sectionLift (predicate A).decoded (predicateName A candidate)
  have guard : (postGuard A operator).preimage naming = ⊤ :=
    named_postGuard A operator candidate (greatest_unfold (semanticOperator A operator certified)).ge
  have application : (FixedPointEvaluation.testedMembership A value).preimage naming =
      candidate.preimage (sectionLift A.decoded value) := tested_reified A value candidate
  intro world parameter held
  refine ⟨naming.app world parameter, ⟨?_,?_⟩,rfl⟩
  · change parameter ∈ ((postGuard A operator).preimage naming).obj world
    rw [guard]
    trivial
  · change parameter ∈ ((FixedPointEvaluation.testedMembership A value).preimage naming).obj world
    rw [application]
    exact held

theorem least_eq_meaning (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections) :
    least A operator value =
      (leastMeaning (semanticOperator A operator certified)).preimage (sectionLift A.decoded value) := by
  rw [← leastEncoding_eq_meaning]
  exact le_antisymm (least_le_meaning A operator certified value) (meaning_le_least A operator certified value)

theorem greatest_eq_meaning (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections) :
    greatest A operator value =
      (greatestMeaning (semanticOperator A operator certified)).preimage (sectionLift A.decoded value) := by
  rw [← greatestEncoding_eq_meaning]
  exact le_antisymm (greatest_le_meaning A operator certified value) (meaning_le_greatest A operator certified value)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComparison
