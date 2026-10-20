import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRestriction
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Structural conversion certificates in operational logical form

The original scoped structural steps generate a bidirectional conversion
theory. Its terms remain the original terms; finite paths are compared with
the independently defined conversion relation and maintained code checker.
The equation policy of this observation theory is syntax equality. Object
conversion is visible path data, rather than quotienting away every edge.

This is the conversion-evidence observation, not the evaluator's directional
execution, a formed typing judgment, or a new dependent foundation. An accepted
formed request also has a finite dependency-supported rule restriction. That
restriction still needs its own computational admission and executable decoder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveCheckingOSLF

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {Head : Type} {n : Nat}

/-- Each conversion edge exposes an original structural step and orientation. -/
abbrev theory (R : Rules Head) (n : Nat) : GSLT :=
  conversionTheory (fun left right : Tm Head n => Step R.headEq left right R.computation)

/-- Reachability is exactly the authored symmetric-transitive conversion. -/
theorem path_iff_conversion (R : Rules Head) (left right : Tm Head n) :
    (theory R n).MultiStep left right ↔ Conv R.headEq left right R.computation :=
  conversionTheory_path_iff _ left right

def conversionNativeType (R : Rules Head) (target : Tm Head n) :
    GSLTNativeType (theory R n) :=
  IndexedOperational.conversionNativeType
    (fun left right => Step R.headEq left right R.computation) target

/-- The generated native type characterizes the independently authored
conversion relation; it does not decide whether a path can be found. -/
theorem satisfies_iff_conversion (R : Rules Head) (left right : Tm Head n) :
    (gsltOSLF (theory R n)).satisfies (S := ()) left
      (conversionNativeType R right).pred ↔ Conv R.headEq left right R.computation :=
  satisfies_conversionNativeType_iff _ left right

section Checking

variable {R : Rules Head} [DecidableEq Head] [DecidableRel R.headEq]

/-- Finite conversion checking and the conversion-native OSLF observation
have exactly the same authority. The finite evidence remains explicit. -/
theorem satisfies_iff_checked (decoder : StructuralConversionCode.RootDecoder R.computation)
    (left right : Tm Head n) :
    (gsltOSLF (theory R n)).satisfies (S := ()) left
      (conversionNativeType R right).pred ↔
    ∃ code : StructuralConversionCode.Code Head decoder.Code n,
      code.check R.headEq decoder.decode left right = true :=
  (satisfies_iff_conversion R left right).trans
    (StructuralConversionCode.Code.conversion_iff_checked decoder)

end Checking

/-- Dependency restriction gives an actual forward route on conversion
steps. Global backward coverage is deliberately not asserted. -/
def restrictionRoute {R : Rules Head}
    {requirements : List (FormationSensitive.Dependencies.Requirement Head)}
    (valid : FormationSensitive.Dependencies.HoldsAll R requirements) (n : Nat) :
    OperationalTranslation
      (theory (FormationSensitive.Dependencies.restrict R requirements) n) (theory R n) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := by
    intro first last edge
    have transfer {first last : Tm Head n}
        (step : Step (FormationSensitive.Dependencies.restrict R requirements).headEq
          first last (FormationSensitive.Dependencies.restrict R requirements).computation) :
        Step R.headEq first last R.computation := by
      obtain ⟨needed, admitted, replay⟩ := FormationSensitive.Dependencies.step_supported step
      exact replay R (fun requirement member =>
        FormationSensitive.Dependencies.requirement_reflects valid requirement (admitted requirement member))
    exact edge.elim (fun step => .inl (transfer step)) (fun step => .inr (transfer step))

section Requests

variable {R : Rules Head} [DecidableEq Head] [DecidableRel R.headTyping]
    [DecidablePred R.isUniverse] [∀ u v w, Decidable (R.join u v w)]
    [DecidableRel R.cumulative] [DecidableRel R.headEq]

/-- An existing higher-profile request determines a finite sufficient lower
rule package. The original contexts and terms survive, and every judgment
of that restriction reflects to the source. No minimality is claimed. -/
theorem checked_request_has_restriction
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    {claim : FormationSensitiveRuleSignature.Judgment Head}
    (request : FormationSensitiveChecking.Request decoder claim)
    (accepted : request.check decoder = true) :
    ∃ requirements : List (FormationSensitive.Dependencies.Requirement Head),
      FormationSensitive.Dependencies.HoldsAll R requirements ∧
      FormationSensitive.Judgment (FormationSensitive.Dependencies.restrict R requirements)
        claim.context claim.subject claim.type ∧
      ∀ {m : Nat} {context : Ctx Head m} {term type : Tm Head m},
        FormationSensitive.Judgment (FormationSensitive.Dependencies.restrict R requirements)
          context term type → FormationSensitive.Judgment R context term type :=
  FormationSensitive.Dependencies.exists_restriction_with_reflection
    (request.sound decoder accepted)

end Requests
end FormationSensitiveCheckingOSLF
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
