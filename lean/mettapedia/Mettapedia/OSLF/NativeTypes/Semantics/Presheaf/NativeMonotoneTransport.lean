import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneComparison
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneStability

/-!
# Native fixed-point formula substitution and reindexing

The same checked native proposition remains valid after every base map.
Independent fixed-point comparison, actual operator application naturality
and the dependent argument square prove substitution of both emitted formulas.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneTransport

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables NativeMonotoneFunctions NativeMonotoneReadout
open NativeMonotoneBaseChange NativeMonotoneStability NativeMonotoneEvaluation NativeMonotoneComparison
open NativeFixedPointEncodings

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

theorem least_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections)
    (substitution : Q ⟶ P) :
    (least A operator value).preimage substitution =
      least (A.reindex substitution) (weakenOperator A operator substitution)
        (ContextualLocalUniverses.substituteTerm (type := A) value substitution) := by
  rw [least_eq_meaning A operator certified value,
    least_eq_meaning (A.reindex substitution) (weakenOperator A operator substitution)
      (checked_monotonicity_reindex A operator certified substitution),
    ← leastEncoding_eq_meaning, ← leastEncoding_eq_meaning]
  change _ = (leastEncoding (operatorAt A operator certified substitution)).preimage _
  rw [← NativeMonotoneBaseChange.least_substitution]
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp]
  exact congrArg (fun map => (leastEncoding (semanticOperator A operator certified)).preimage map)
    (Mettapedia.TypeTheory.ContextualTypeOperations.selfExtend_substitution
      (C := (NativeModel C).toCwf) substitution value).symm

theorem greatest_substitution (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (certified : monotonicityMeaning A operator = ⊤) (value : A.decoded.sections)
    (substitution : Q ⟶ P) :
    (greatest A operator value).preimage substitution =
      greatest (A.reindex substitution) (weakenOperator A operator substitution)
        (ContextualLocalUniverses.substituteTerm (type := A) value substitution) := by
  rw [greatest_eq_meaning A operator certified value,
    greatest_eq_meaning (A.reindex substitution) (weakenOperator A operator substitution)
      (checked_monotonicity_reindex A operator certified substitution),
    ← greatestEncoding_eq_meaning, ← greatestEncoding_eq_meaning]
  change _ = (greatestEncoding (operatorAt A operator certified substitution)).preimage _
  rw [← NativeMonotoneBaseChange.greatest_substitution]
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp]
  exact congrArg (fun map => (greatestEncoding (semanticOperator A operator certified)).preimage map)
    (Mettapedia.TypeTheory.ContextualTypeOperations.selfExtend_substitution
      (C := (NativeModel C).toCwf) substitution value).symm

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneTransport
