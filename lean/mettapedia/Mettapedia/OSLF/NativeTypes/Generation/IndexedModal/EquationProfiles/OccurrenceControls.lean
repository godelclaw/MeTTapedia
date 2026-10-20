import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Controls
import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierControls
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCertificate

/-!
# Collection-aware response families over actual COMM occurrences

Two requests use distinct program contexts. Their result classifiers inspect
the declared collection normal form, and the returned responses retain the
source receipt. These controls use the selected `GeneralRho.plan` occurrence
semantics; they do not assert correspondence to every reference rho equation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.OccurrenceControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier Complete


def source : Bool → Pattern
  | false => GeneralRho.FrontierControls.rootSource
  | true => GeneralRho.FrontierControls.parallelSource

def target : Bool → Pattern
  | false => GeneralRho.FrontierControls.rootTarget
  | true => GeneralRho.FrontierControls.parallelTarget

def request (input : Bool) : Request := GeneralRho.FrontierControls.actualRequest (source input)

def targetTest (input : Bool) : Test (request input) :=
  collectionTest (by rfl)
    (fun first second equation =>
      (GeneralOccurrenceFrontier.LocalEquationFree.equation_impossible
        (request := request input) GeneralRho.compilation_has_no_equations first second equation).elim)
    (fun value => value == CanonicalBags.lawNormal (Normalized.laws GeneralRho.plan) (target input))

theorem target_accepted (input : Bool) : (targetTest input).accepts (target input) = true := by
  change (CanonicalBags.lawNormal (Normalized.laws GeneralRho.plan) (target input) ==
    CanonicalBags.lawNormal (Normalized.laws GeneralRho.plan) (target input)) = true
  exact beq_self_eq_true _

def parameters : FamilyParameters Bool := ⟨[false, true], request, targetTest⟩

def states : parameters.States := fun input =>
  run (request input) (if input then 60 else 40) (start (request input))

theorem target_list (input : Bool) : targets (request input) (states input) = [target input] := by
  cases input with
  | false =>
    have read := congrArg (List.map GeneralRho.FrontierControls.Readout.target) GeneralRho.FrontierControls.actual_received_drop
    simpa only [GeneralRho.FrontierControls.readouts, List.map_map, List.map_cons, List.map_nil,
      targets, request, states, source, target, GeneralRho.FrontierControls.rawReadout, Function.comp_def,
      Bool.false_eq_true, if_false, if_true] using read
  | true =>
    have read := congrArg (List.map GeneralRho.FrontierControls.Readout.target) GeneralRho.FrontierControls.actual_parallel_context
    simpa only [GeneralRho.FrontierControls.readouts, List.map_map, List.map_cons, List.map_nil,
      targets, request, states, source, target, GeneralRho.FrontierControls.rawReadout, Function.comp_def,
      Bool.false_eq_true, if_false, if_true] using read

theorem checked : parameters.check states = true := by
  apply List.all_eq_true.mpr
  intro input member
  apply (parameters.response?_exact states input).mpr
  change (targets (request input) (states input)).any (targetTest input).accepts = true
  rw [target_list]
  simpa only [List.any_cons, List.any_nil, Bool.or_false] using target_accepted input

theorem member : parameters.Meaning := parameters.check_sound states checked

theorem executable_family : (parameters.membership? states).isSome = true :=
  (parameters.membership?_exact states).mpr checked

def family : parameters.Family states := (parameters.membership? states).get executable_family

/-- The actual under-parallel context survives the native response, rather
than being replaced with a target-only certificate. -/
theorem parallel_origin :
    (family.respond true (by simp [parameters])).answer.val.firing.job.site.address = [1] := by
  let response := family.respond true (by simp [parameters])
  have present : GeneralRho.FrontierControls.rawReadout response.answer.val ∈
      GeneralRho.FrontierControls.readouts (GeneralRho.FrontierControls.actualRequest GeneralRho.FrontierControls.parallelSource) 60 :=
    List.mem_map.mpr ⟨response.answer.val, List.mem_map.mpr ⟨response.answer, response.retained, rfl⟩, rfl⟩
  rw [GeneralRho.FrontierControls.actual_parallel_context, List.mem_singleton] at present
  exact congrArg GeneralRho.FrontierControls.Readout.address present

def dependentFailure : FamilyParameters Bool where
  inputs := parameters.inputs
  request := request
  target input := if input then ⟨fun _ => false, fun _ _ _ => rfl⟩ else targetTest input

theorem dependent_target_refutes : ¬ dependentFailure.Meaning := by
  intro meaning
  have response := meaning true (by simp [dependentFailure, parameters])
  obtain ⟨candidate, _, holds⟩ :=
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec _ _ _).mp response
  change false = true at holds
  cases holds

theorem partial_family_rejected : dependentFailure.check states = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  exact dependent_target_refutes (dependentFailure.check_sound states checked)

#guard parameters.check states
#guard (parameters.membership? states).isSome
#guard !dependentFailure.check states

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.OccurrenceControls
