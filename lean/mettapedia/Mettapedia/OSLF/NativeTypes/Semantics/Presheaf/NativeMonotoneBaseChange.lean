import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneCertificate
import Mettapedia.GSLT.Topos.NativeFixedPointEncodings

/-!
# Checked native monotonicity at every base change

Generalized predicate names specialize the original two generic variables
along an arbitrary context map. The checked native proposition therefore
earns monotonicity of every reindexed actual operator. No monotonicity
component is supplied by the semantic model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneBaseChange

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions NativeMonotoneReadout
open NativeMonotoneNaming NativeMonotoneCertificate

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem generic_value_pairing (B : NativeType P) (substitution : Q ⟶ P)
    (value : (B.reindex substitution).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨B.reindex (totalProjection B.decoded),(NativeModel C).toCwf.vz B⟩ :
        NativeValue (totalSpace B.decoded))
      ((NativeModel C).toCwf.pair substitution B value) = ⟨B.reindex substitution,value⟩ := by
  apply Sigma.ext
  · change (B.reindex (totalProjection B.decoded)).reindex
      ((NativeModel C).toCwf.pair substitution B value) = B.reindex substitution
    rw [← LocalType.reindex_comp]
    exact congrArg (fun map => B.reindex map) ((NativeModel C).toCwf.wk_pair substitution B value)
  · exact (heq_of_eq ((NativeModel C).toCwf.vz_pair substitution B value)).trans (cast_heq _ _)

noncomputable def nameAlong (A : NativeType P) (substitution : Q ⟶ P)
    (function : (predicate (A.reindex substitution)).decoded.sections) :
    Q ⟶ totalSpace (predicate A).decoded :=
  (NativeModel C).toCwf.pair substitution (predicate A)
    (castTerm (predicate_reindex A substitution).symm function)

theorem nameAlong_projection (A : NativeType P) (substitution : Q ⟶ P)
    (function : (predicate (A.reindex substitution)).decoded.sections) :
    nameAlong A substitution function ≫ totalProjection (predicate A).decoded = substitution :=
  (NativeModel C).toCwf.wk_pair _ _ _

theorem nameAlong_carrier (A : NativeType P) (substitution : Q ⟶ P)
    (function : (predicate (A.reindex substitution)).decoded.sections) :
    (argumentType A).reindex (nameAlong A substitution function) = A.reindex substitution := by
  rw [← LocalType.reindex_comp]
  exact congrArg (fun map => A.reindex map) (nameAlong_projection A substitution function)

theorem nameAlong_generic (A : NativeType P) (substitution : Q ⟶ P)
    (function : (predicate (A.reindex substitution)).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (argumentType A),generic A⟩ : NativeValue (totalSpace (predicate A).decoded))
      (nameAlong A substitution function) = ⟨predicate (A.reindex substitution),function⟩ := by
  have normalized := nativeValue_cast (predicate_reindex A (totalProjection (predicate A).decoded))
    ((NativeModel C).toCwf.vz (predicate A))
  have beta := generic_value_pairing (predicate A) substitution
    (castTerm (predicate_reindex A substitution).symm function)
  exact (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
    Value.substitute (K := (NativeModel C).toCwf) value (nameAlong A substitution function))
    normalized.symm).trans
      (beta.trans (nativeValue_cast (predicate_reindex A substitution).symm function).symm)

theorem secondPredicate_reindex (A : NativeType P) (substitution : Q ⟶ P)
    (first : (predicate (A.reindex substitution)).decoded.sections) :
    (predicate (argumentType A)).reindex (nameAlong A substitution first) =
      predicate (A.reindex substitution) :=
  (predicate_reindex (argumentType A) _).trans
    (congrArg predicate (nameAlong_carrier A substitution first))

noncomputable def pairAlong (A : NativeType P) (substitution : Q ⟶ P)
    (first second : (predicate (A.reindex substitution)).decoded.sections) :
    Q ⟶ totalSpace (predicate (argumentType A)).decoded :=
  (NativeModel C).toCwf.pair (nameAlong A substitution first) (predicate (argumentType A))
    (castTerm (secondPredicate_reindex A substitution first).symm second)

theorem pairAlong_projection (A : NativeType P) (substitution : Q ⟶ P)
    (first second : (predicate (A.reindex substitution)).decoded.sections) :
    pairAlong A substitution first second ≫ totalProjection (predicate (argumentType A)).decoded =
      nameAlong A substitution first := (NativeModel C).toCwf.wk_pair _ _ _

theorem pairAlong_carrier (A : NativeType P) (substitution : Q ⟶ P)
    (first second : (predicate (A.reindex substitution)).decoded.sections) :
    (secondArgument A).reindex (pairAlong A substitution first second) = A.reindex substitution := by
  change ((argumentType A).reindex (totalProjection (predicate (argumentType A)).decoded)).reindex _ = _
  rw [← LocalType.reindex_comp]
  change (argumentType A).reindex
    (pairAlong A substitution first second ≫ totalProjection (predicate (argumentType A)).decoded) = _
  rw [pairAlong_projection]
  exact nameAlong_carrier A substitution first

theorem pairAlong_first (A : NativeType P) (substitution : Q ⟶ P)
    (first second : (predicate (A.reindex substitution)).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (secondArgument A),firstCandidate A⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairAlong A substitution first second) = ⟨predicate (A.reindex substitution),first⟩ := by
  have normalized := predicateValue_substitution (argumentType A) (generic A)
    (totalProjection (predicate (argumentType A)).decoded)
  have combined := (congrArg (fun value : NativeValue (totalSpace (predicate (argumentType A)).decoded) =>
      Value.substitute (K := (NativeModel C).toCwf) value (pairAlong A substitution first second))
      normalized.symm).trans (value_substitute_comp _ _ _).symm
  rw [pairAlong_projection] at combined
  exact combined.trans (nameAlong_generic A substitution first)

theorem pairAlong_second (A : NativeType P) (substitution : Q ⟶ P)
    (first second : (predicate (A.reindex substitution)).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (secondArgument A),secondCandidate A⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairAlong A substitution first second) = ⟨predicate (A.reindex substitution),second⟩ := by
  have normalized := nativeValue_cast
    (predicate_reindex (argumentType A) (totalProjection (predicate (argumentType A)).decoded))
      ((NativeModel C).toCwf.vz (predicate (argumentType A)))
  have beta := generic_value_pairing (predicate (argumentType A)) (nameAlong A substitution first)
    (castTerm (secondPredicate_reindex A substitution first).symm second)
  exact (congrArg (fun value : NativeValue (totalSpace (predicate (argumentType A)).decoded) =>
    Value.substitute (K := (NativeModel C).toCwf) value (pairAlong A substitution first second))
    normalized.symm).trans
      (beta.trans (nativeValue_cast (secondPredicate_reindex A substitution first).symm second).symm)

theorem pairAlong_operator (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (substitution : Q ⟶ P) (first second : (predicate (A.reindex substitution)).decoded.sections) :
    Value.substitute (K := (NativeModel C).toCwf)
      (⟨operatorType (secondArgument A),twiceOperator A operator⟩ :
        NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairAlong A substitution first second) =
        ⟨operatorType (A.reindex substitution),weakenOperator A operator substitution⟩ := by
  have normalized := operatorValue_substitution (argumentType A)
    (weakenOperator A operator (totalProjection (predicate A).decoded))
    (totalProjection (predicate (argumentType A)).decoded)
  have combined := (congrArg (fun value : NativeValue (totalSpace (predicate (argumentType A)).decoded) =>
      Value.substitute (K := (NativeModel C).toCwf) value (pairAlong A substitution first second))
      normalized.symm).trans (value_substitute_comp _ _ _).symm
  rw [pairAlong_projection] at combined
  have earlier := operatorValue_substitution A operator (totalProjection (predicate A).decoded)
  have outer := (congrArg (fun value : NativeValue (totalSpace (predicate A).decoded) =>
      Value.substitute (K := (NativeModel C).toCwf) value (nameAlong A substitution first))
      earlier.symm).trans (value_substitute_comp _ _ _).symm
  rw [nameAlong_projection] at outer
  exact combined.trans (outer.trans (operatorValue_substitution A operator substitution))

theorem along_application (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (substitution : Q ⟶ P) (first second : (predicate (A.reindex substitution)).decoded.sections)
    (selected : (predicate (secondArgument A)).decoded.sections)
    (returned : (predicate (A.reindex substitution)).decoded.sections)
    (selectedRead : Value.substitute (K := (NativeModel C).toCwf)
      (⟨predicate (secondArgument A),selected⟩ : NativeValue (totalSpace (predicate (argumentType A)).decoded))
      (pairAlong A substitution first second) = ⟨predicate (A.reindex substitution),returned⟩) :
    (⟨predicate ((secondArgument A).reindex (pairAlong A substitution first second)),
      weakenFunction (secondArgument A)
        (applyValue (predicate (secondArgument A)) (twiceOperator A operator) selected)
        (pairAlong A substitution first second)⟩ : NativeValue Q) =
      ⟨predicate (A.reindex substitution),
        applyValue (predicate (A.reindex substitution)) (weakenOperator A operator substitution) returned⟩ := by
  rw [operatorApplication_substitution]
  apply applyValue_values_equal
  · exact (operatorValue_substitution (secondArgument A) _ (pairAlong A substitution first second)).symm.trans
      (pairAlong_operator A operator substitution first second)
  · exact (predicateValue_substitution (secondArgument A) _ (pairAlong A substitution first second)).symm.trans
      selectedRead

theorem monotonicity_along (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (substitution : Q ⟶ P) (first second : (predicate (A.reindex substitution)).decoded.sections) :
    (monotonicityBody A operator).preimage (pairAlong A substitution first second) =
      inclusionMeaning (A.reindex substitution) first second ⇨
        inclusionMeaning (A.reindex substitution)
          (applyValue (predicate (A.reindex substitution)) (weakenOperator A operator substitution) first)
          (applyValue (predicate (A.reindex substitution)) (weakenOperator A operator substitution) second) := by
  rw [monotonicityBody, preimage_himp, inclusionMeaning_substitution, inclusionMeaning_substitution]
  apply congrArg₂ (fun (left right : Subfunctor Q) => left ⇨ right)
  · apply inclusion_values_equal (pairAlong_carrier A substitution first second)
    · exact (predicateValue_substitution (secondArgument A) _ _).symm.trans
        (pairAlong_first A substitution first second)
    · exact (predicateValue_substitution (secondArgument A) _ _).symm.trans
        (pairAlong_second A substitution first second)
  · apply inclusion_values_equal (pairAlong_carrier A substitution first second)
    · exact along_application A operator substitution first second _ _ (pairAlong_first A substitution first second)
    · exact along_application A operator substitution first second _ _ (pairAlong_second A substitution first second)

theorem reindexed_operator_monotone (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    Monotone (action (A.reindex substitution) (weakenOperator A operator substitution)) := by
  intro first second below
  have specialized := monotonicity_along A operator substitution
    (predicateName (A.reindex substitution) first) (predicateName (A.reindex substitution) second)
  rw [monotonicityMeaning_body A operator certified, preimage_top'] at specialized
  have implication := himp_eq_top_iff.mp specialized.symm
  have antecedent : inclusionMeaning (A.reindex substitution)
      (predicateName (A.reindex substitution) first) (predicateName (A.reindex substitution) second) = ⊤ := by
    apply (inclusionMeaning_top_iff _ _ _).mpr
    simpa only [predicateBody_name] using below
  have consequent : inclusionMeaning (A.reindex substitution)
      (applyValue (predicate (A.reindex substitution)) (weakenOperator A operator substitution)
        (predicateName (A.reindex substitution) first))
      (applyValue (predicate (A.reindex substitution)) (weakenOperator A operator substitution)
        (predicateName (A.reindex substitution) second)) = ⊤ := by
    apply top_unique
    rw [← antecedent]
    exact implication
  exact (inclusionMeaning_top_iff _ _ _).mp consequent

noncomputable def semanticOperator (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) :
    Subfunctor (totalSpace A.decoded) →o Subfunctor (totalSpace A.decoded) where
  toFun := action A operator
  monotone' := native_operator_monotone A operator certified

noncomputable def operatorAt (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    Subfunctor (totalSpace (A.reindex substitution).decoded) →o
      Subfunctor (totalSpace (A.reindex substitution).decoded) where
  toFun := action (A.reindex substitution) (weakenOperator A operator substitution)
  monotone' := reindexed_operator_monotone A operator certified substitution

theorem least_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    (NativeFixedPointEncodings.leastEncoding (semanticOperator A operator certified)).preimage
      (totalReindexMap substitution A.decoded) =
        NativeFixedPointEncodings.leastEncoding (operatorAt A operator certified substitution) :=
  NativeFixedPointEncodings.least_preimage _ _ _ (action_substitution A operator · substitution)

theorem greatest_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (substitution : Q ⟶ P) :
    (NativeFixedPointEncodings.greatestEncoding (semanticOperator A operator certified)).preimage
      (totalReindexMap substitution A.decoded) =
        NativeFixedPointEncodings.greatestEncoding (operatorAt A operator certified substitution) :=
  NativeFixedPointEncodings.greatest_preimage _ _ _ (action_substitution A operator · substitution)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneBaseChange
