import Mettapedia.OSLF.Framework.RhoGeneratedScopeDecisionInterpretation
import Mettapedia.OSLF.Framework.RhoGeneratedScopeControls
import Mettapedia.OSLF.Framework.RhoScopeSeedReadings
import Mettapedia.OSLF.Framework.RhoFiniteQuotationOriginTransport
import Mettapedia.OSLF.Framework.RhoGeneratedScopeInventory

/-!
# Positive and negative controls for complete atomic-scope decisions

The displayed atomic-part scope admits an actual quoted output and excludes
the quoted null. Unseeded least scopes reject despite their source-equation
self-loops. A current open name can be excluded and admitted after a supplied
future substitution, separating static equation invariance from preservation
of negative answers across future contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeDecisionControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates
open RhoSchema.IntrinsicEncoding
open RhoEquationGeneratedScope RhoGeneratedScopeStrata RhoGeneratedScopeSubstitution
open RhoGeneratedScopeDecision RhoScopeCanonicalSizeBound RhoGeneratedScopeInventory

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  RhoIntrinsicReadback.equationClassDecision context Srt.pr

local instance displayedLeftDecision : DecidablePred RhoScopeSeedReadings.leftAtom :=
  fun process => show Decidable (process = zero []) from inferInstance

local instance displayedRightDecision : DecidablePred RhoScopeSeedReadings.rightAtom :=
  fun process => show Decidable (process = visible) from inferInstance

theorem displayed_output_accepted :
    guard RhoScopeSeedReadings.leftAtom RhoScopeSeedReadings.rightAtom (quote visible) = true := by
  apply (guard_true_iff _ _ _).mpr
  obtain ⟨certificate, _⟩ := (RhoScopeSeedReadings.displayed_zero_stage (quote visible)).mpr rfl
  exact certificate_sound certificate

theorem displayed_null_rejected :
    guard RhoScopeSeedReadings.leftAtom RhoScopeSeedReadings.rightAtom (quote (zero [])) = false := by
  apply (guard_false_iff _ _ _).mpr
  have excluded := RhoScopeSeedReadings.displayed_excludes_null (fun _ _ => False)
  rw [RhoScopeSeedReadings.displayed_readout] at excluded
  exact excluded

local instance emptyAtomDecision : DecidablePred RhoGeneratedScopeControls.unseededAtom :=
  fun _ => isFalse id

local instance zeroAtomDecision : DecidablePred RhoScopeQuotientControls.leftScope :=
  fun process => show Decidable (process = zero []) from inferInstance

theorem self_loops_do_not_create_membership (name : Name []) :
    (step RhoGeneratedScopeControls.unseededAtom RhoScopeQuotientControls.leftScope).gfp name ∧
    guard RhoGeneratedScopeControls.unseededAtom RhoScopeQuotientControls.leftScope name = false :=
  ⟨RhoGeneratedScopeControls.unseeded_greatest_scope_admits_every_name name,
    (guard_false_iff _ _ _).mpr (RhoGeneratedScopeControls.unseeded_least_scope_empty name)⟩

def outputAtom {context : Ctx sig} (process : Process context) : Prop :=
  0 < RhoSourceOutputPredicate.count process

local instance outputAtomDecision (context : Ctx sig) : DecidablePred (outputAtom (context := context)) :=
  fun process => show Decidable (0 < RhoSourceOutputPredicate.count process) from inferInstance

def currentName : Name [Srt.nm] := RhoFiniteQuotationOrigins.openName

def futureName : Name [] := quote (join visible visible)

def futureEnvironment : Environment sig (TermQ rhoSourceE) [Srt.nm] [] :=
  fun _ position => match position with
    | .zero => futureName
    | .succ impossible => nomatch impossible

theorem current_name_substitution :
    model.substitution.substitute futureEnvironment currentName = futureName := by
  change model.substitution.substitute futureEnvironment (model.substitution.injectVar .zero) = _
  exact model.substitution.substitute_var futureEnvironment .zero

theorem current_open_name_rejected : guard outputAtom outputAtom currentName = false := by
  apply (guard_false_iff _ _ _).mpr
  intro member
  have positive := generated_retains_output outputAtom currentName member
  change (0 : Nat) < 0 at positive
  exact Nat.lt_irrefl 0 positive

def futureCertificate : Certificate outputAtom outputAtom futureName :=
  .atoms visible visible (by exact Nat.zero_lt_one) (by exact Nat.zero_lt_one)

theorem future_name_accepted : guard outputAtom outputAtom futureName = true :=
  (guard_true_iff _ _ _).mpr (certificate_sound futureCertificate)

theorem current_rejection_can_become_future_acceptance :
    guard outputAtom outputAtom currentName = false ∧
    guard outputAtom outputAtom (model.substitution.substitute futureEnvironment currentName) = true := by
  rw [current_name_substitution]
  exact ⟨current_open_name_rejected, future_name_accepted⟩

theorem future_acceptance_retains_two_atomic_occurrences :
    futureCertificate.atomicOrigins = [Sum.inl visible, Sum.inr visible] := rfl

theorem current_quotation_has_one_origin : (RhoFiniteQuotationOrigins.origins currentName).card = 1 :=
  RhoFiniteQuotationOrigins.bound_name_one_origin

end Mettapedia.OSLF.Framework.RhoScopeDecisionControls
