import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneReadout

/-!
# Complete predicate-pair names in the native monotonicity context

The two generic function variables specialize to any two supplied native
predicate sections. Their complete values and the carrier are retained by
the actual context maps, including the authored operator application.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneNaming

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes ContextualTypeOperations
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions NativeMonotoneReadout

universe u
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}

noncomputable def pairName (A : NativeType P) (first second : (predicate A).decoded.sections) :
    P ⟶ totalSpace (predicate (argumentType A)).decoded :=
  sectionLift (predicate A).decoded first ≫
    sectionLift (predicate (argumentType A)).decoded
      (weakenFunction A second (totalProjection (predicate A).decoded))

theorem generic_predicate_beta (A : NativeType P) (function : (predicate A).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (argumentType A),generic A⟩ : NativeValue (totalSpace (predicate A).decoded))
      (sectionLift (predicate A).decoded function) = ⟨predicate A,function⟩ := by
  have normalized := nativeValue_cast (predicate_reindex A (totalProjection (predicate A).decoded))
    ((NativeModel C).toCwf.vz (predicate A))
  exact (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
    Value.substitute (K := (NativeModel C).toCwf) value (sectionLift (predicate A).decoded function))
    normalized.symm).trans (generic_value_beta (predicate A) function)

theorem pair_carrier (A : NativeType P) (first second : (predicate A).decoded.sections) :
    (secondArgument A).reindex (pairName A first second) = A := by
  change ((argumentType A).reindex (totalProjection (predicate (argumentType A)).decoded)).reindex
    (pairName A first second) = A
  rw [← LocalType.reindex_comp]
  change (argumentType A).reindex
    ((sectionLift (predicate A).decoded first ≫
      sectionLift (predicate (argumentType A)).decoded
        (weakenFunction A second (totalProjection (predicate A).decoded))) ≫
          totalProjection (predicate (argumentType A)).decoded) = A
  rw [Category.assoc, projection_section, Category.comp_id]
  exact named_argument_type A first

theorem pair_first (A : NativeType P) (first second : (predicate A).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (secondArgument A),firstCandidate A⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairName A first second) = ⟨predicate A,first⟩ := by
  let next := weakenFunction A second (totalProjection (predicate A).decoded)
  let earlier : NativeValue (totalSpace (predicate A).decoded) :=
    ⟨predicate (argumentType A),generic A⟩
  have normalized := predicateValue_substitution (argumentType A) (generic A)
    (totalProjection (predicate (argumentType A)).decoded)
  rw [pairName, value_substitute_comp]
  have undo := (congrArg (fun value : NativeValue (totalSpace (predicate (argumentType A)).decoded) =>
      Value.substitute (K := (NativeModel C).toCwf) value
        (sectionLift (predicate (argumentType A)).decoded next)) normalized.symm).trans
      (value_weaken_beta (predicate (argumentType A)) earlier next)
  exact (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
    Value.substitute (K := (NativeModel C).toCwf) value (sectionLift (predicate A).decoded first)) undo).trans
      (generic_predicate_beta A first)

theorem pair_second (A : NativeType P) (first second : (predicate A).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (secondArgument A),secondCandidate A⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairName A first second) = ⟨predicate A,second⟩ := by
  let next := weakenFunction A second (totalProjection (predicate A).decoded)
  rw [pairName, value_substitute_comp]
  have inner := generic_predicate_beta (argumentType A) next
  have normalized := predicateValue_substitution A second (totalProjection (predicate A).decoded)
  exact (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
      Value.substitute (K := (NativeModel C).toCwf) value (sectionLift (predicate A).decoded first))
      (inner.trans normalized.symm)).trans
        (value_weaken_beta (predicate A) (⟨predicate A,second⟩ : NativeValue P) first)

theorem inclusion_values_equal {first second : NativeType P} (same : first = second)
    (beforeLeft beforeRight : (predicate first).decoded.sections)
    (afterLeft afterRight : (predicate second).decoded.sections)
    (left : (⟨predicate first,beforeLeft⟩ : NativeValue P) = ⟨predicate second,afterLeft⟩)
    (right : (⟨predicate first,beforeRight⟩ : NativeValue P) = ⟨predicate second,afterRight⟩) :
    inclusionMeaning first beforeLeft beforeRight = inclusionMeaning second afterLeft afterRight := by
  cases same
  have leftSame := eq_of_heq (Sigma.mk.inj left).2
  have rightSame := eq_of_heq (Sigma.mk.inj right).2
  rw [leftSame,rightSame]

theorem pair_inclusion (A : NativeType P) (first second : (predicate A).decoded.sections) :
    (inclusionMeaning (secondArgument A) (firstCandidate A) (secondCandidate A)).preimage
      (pairName A first second) = inclusionMeaning A first second := by
  rw [inclusionMeaning_substitution]
  apply inclusion_values_equal (pair_carrier A first second)
  · exact (predicateValue_substitution (secondArgument A) _ (pairName A first second)).symm.trans
      (pair_first A first second)
  · exact (predicateValue_substitution (secondArgument A) _ (pairName A first second)).symm.trans
      (pair_second A first second)

theorem pair_operator (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (first second : (predicate A).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨operatorType (secondArgument A),twiceOperator A operator⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairName A first second) = ⟨operatorType A,operator⟩ := by
  let earlier := weakenOperator A operator (totalProjection (predicate A).decoded)
  let next := weakenFunction A second (totalProjection (predicate A).decoded)
  have normalized := operatorValue_substitution (argumentType A) earlier
    (totalProjection (predicate (argumentType A)).decoded)
  rw [pairName, value_substitute_comp]
  have undo := (congrArg (fun value : NativeValue (totalSpace (predicate (argumentType A)).decoded) =>
      Value.substitute (K := (NativeModel C).toCwf) value
        (sectionLift (predicate (argumentType A)).decoded next)) normalized.symm).trans
      (value_weaken_beta (predicate (argumentType A))
        (⟨operatorType (argumentType A),earlier⟩ : NativeValue (totalSpace (predicate A).decoded)) next)
  have firstNormalized := operatorValue_substitution A operator (totalProjection (predicate A).decoded)
  exact (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
    Value.substitute (K := (NativeModel C).toCwf) value (sectionLift (predicate A).decoded first))
      (undo.trans firstNormalized.symm)).trans
        (value_weaken_beta (predicate A) (⟨operatorType A,operator⟩ : NativeValue P) first)

theorem paired_application (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (first second : (predicate A).decoded.sections)
    (selected : (predicate (secondArgument A)).decoded.sections)
    (returned : (predicate A).decoded.sections)
    (selectedRead : Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (secondArgument A),selected⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairName A first second) = ⟨predicate A,returned⟩) :
    (⟨predicate ((secondArgument A).reindex (pairName A first second)),
      weakenFunction (secondArgument A)
        (applyValue (predicate (secondArgument A)) (twiceOperator A operator) selected)
        (pairName A first second)⟩ : NativeValue P) =
      ⟨predicate A,applyValue (predicate A) operator returned⟩ := by
  rw [operatorApplication_substitution]
  apply applyValue_values_equal
  · exact (operatorValue_substitution (secondArgument A) _ (pairName A first second)).symm.trans
      (pair_operator A operator first second)
  · exact (predicateValue_substitution (secondArgument A) _ (pairName A first second)).symm.trans
      selectedRead

theorem pair_image_inclusion (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (first second : (predicate A).decoded.sections) :
    (inclusionMeaning (secondArgument A)
      (applyValue (predicate (secondArgument A)) (twiceOperator A operator) (firstCandidate A))
      (applyValue (predicate (secondArgument A)) (twiceOperator A operator) (secondCandidate A))).preimage
        (pairName A first second) =
      inclusionMeaning A (applyValue (predicate A) operator first) (applyValue (predicate A) operator second) := by
  rw [inclusionMeaning_substitution]
  apply inclusion_values_equal (pair_carrier A first second)
  · exact paired_application A operator first second (firstCandidate A) first (pair_first A first second)
  · exact paired_application A operator first second (secondCandidate A) second (pair_second A first second)

theorem monotonicity_specialization (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (first second : (predicate A).decoded.sections) :
    (monotonicityBody A operator).preimage (pairName A first second) =
      inclusionMeaning A first second ⇨
        inclusionMeaning A (applyValue (predicate A) operator first) (applyValue (predicate A) operator second) := by
  rw [monotonicityBody, preimage_himp, pair_inclusion, pair_image_inclusion]

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneNaming
