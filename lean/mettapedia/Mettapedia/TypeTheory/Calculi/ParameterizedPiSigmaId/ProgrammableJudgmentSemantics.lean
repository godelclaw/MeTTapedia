import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitivePresheafSemantics

/-!
# Programmable rules and conversion in the existing contextual interpretation

The retained section interprets the actual typed term. Its conversion-valued
observation is the existing formed quotient, not a newly chosen semantics.
Checked conversion preserves that value under every admitted substitution.
Closing and applying a rule constructs its typing and the beta certificate;
its observed result is the reindexed value of the original open body.

Only the local root decoder and the calculus's universe capabilities are
parameters. No whole-program soundness or equality-reflection field is used.
The observation forgets convertible syntax; retained sections still have the
original code, and no C implementation refinement follows from these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ProgrammableJudgmentSemantics

open FormationSensitive FormationSensitiveContextual
open StructuralConversionCode TelescopeAbstraction

variable {Head : Type} {R : Rules Head} [DecidableEq Head] [DecidableRel R.headEq]
variable (decoder : RootDecoder R.computation)

theorem checked_value_eq {context : Context R} {type : TypeOver context}
    (left right : Term context type) (code : Code Head decoder.Code context.arity)
    (accepted : code.check R.headEq decoder.decode left.code right.code = true) :
    TermFibre.mk left = TermFibre.mk right :=
  (TermFibre.mk_eq_iff left right).mpr (Code.check_sound decoder accepted)

/-- The represented sections are recovered before observing conversion.
This relates the actual supplied terms, not independently chosen values. -/
theorem checked_section_observation {context : Context R} {type : TypeOver context}
    (left right : Term context type) (code : Code Head decoder.Code context.arity)
    (accepted : code.check R.headEq decoder.decode left.code right.code = true) :
    PresheafSemantics.observeSection (PresheafSemantics.termEquiv type left) =
      PresheafSemantics.observeSection (PresheafSemantics.termEquiv type right) := by
  rw [PresheafSemantics.observe_interpret, PresheafSemantics.observe_interpret]
  exact checked_value_eq decoder left right code accepted

theorem checked_reindexed_value {source target : Context R} {type : TypeOver source}
    (left right : Term source type) (code : Code Head decoder.Code source.arity)
    (accepted : code.check R.headEq decoder.decode left.code right.code = true)
    (arguments : Hom target source) :
    TermFibre.mk (left.reindex arguments) = TermFibre.mk (right.reindex arguments) := by
  apply (TermFibre.mk_eq_iff _ _).mpr
  exact (Code.check_sound decoder accepted).substitute arguments.substitution

/-- A successful bounded converter preserves the interpreted value. A
missing result supplies no such certificate and no proof of inequality. -/
theorem converter_value_eq
    (search : {n : Nat} → Tm Head n → Option (decoder.Code n)) (fuel : Nat)
    {context : Context R} {type : TypeOver context} (left right : Term context type)
    (code : Code Head decoder.Code context.arity)
    (produced : StructuralConversionSearch.compare decoder search (headEq := R.headEq)
      fuel left.code right.code = some code) : TermFibre.mk left = TermFibre.mk right :=
  checked_value_eq decoder left right code
    (StructuralConversionPrograms.compare_checked decoder search fuel left.code right.code code produced)

variable (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)

/-- Build the actual closed-lambda call using the existing typed context
morphism. The result typing is derived from the source rule's typing. -/
def application {source target : Context R} {type : TypeOver source}
    (body : Term source type) (arguments : Hom target source) : Term target (type.reindex arguments) where
  code := applyClosed source.raw arguments.substitution (liftClosed (closeTerm source.raw body.code))
  typed := FormationCheckedTelescopePrograms.apply_typed arguments.typed
    (FormationCheckedTelescopePrograms.close_into_target universes joins body.judgment)

include decoder in
theorem application_value {source target : Context R} {type : TypeOver source}
    (body : Term source type) (arguments : Hom target source) :
    TermFibre.mk (application universes joins body arguments) =
      (TermFibre.mk body).reindex arguments := by
  change TermFibre.mk (application universes joins body arguments) = TermFibre.mk (body.reindex arguments)
  exact checked_value_eq decoder _ _
    (FormationCheckedTelescopePrograms.applicationCodeIn source.raw arguments.substitution body.code)
    (FormationCheckedTelescopePrograms.applicationCodeIn_checked R.headEq decoder.decode
      source.raw arguments.substitution body.code)

include decoder in
theorem application_section_observation {source target : Context R} {type : TypeOver source}
    (body : Term source type) (arguments : Hom target source) :
    PresheafSemantics.observeSection
        (PresheafSemantics.termEquiv (type.reindex arguments) (application universes joins body arguments)) =
      (PresheafSemantics.observeSection (PresheafSemantics.termEquiv type body)).reindex arguments := by
  rw [PresheafSemantics.observe_interpret, PresheafSemantics.observe_interpret]
  exact application_value decoder universes joins body arguments

#print axioms checked_reindexed_value
#print axioms converter_value_eq
#print axioms application_value
#print axioms application_section_observation

end ProgrammableJudgmentSemantics
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
