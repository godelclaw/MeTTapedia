import Mettapedia.OSLF.NativeTypes.Semantics.Checking
import Mettapedia.OSLF.NativeTypes.Semantics.Generated
import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls
import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls
import Mettapedia.OSLF.NativeTypes.Semantics.Display
import Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl
import Mettapedia.OSLF.NativeTypes.Generation.BudgetControls
import Mettapedia.GSLT.Core.ProofRelevantGSLT

open Mettapedia.OSLF.Framework

/-!
# Executed native-output and comprehension controls

Original rho COMM supplies both a positive native membership and an actual
counterexample to an outgoing universal question. An exhausted run remains
unknown. Equal endpoint observations retain distinct native receipts, so
the refinement projection cannot recover their dependent comprehension.

The lambda consumer exercises the actual native modal compiler and its
connective gate, without substituting an identity or empty generator.

The family comparison changes both state and receipt representations while
retaining a repeated origin. Its negative control has the right predicate
support but loses a receipt, so no family equivalence exists.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Semantics.Operational
open Mettapedia.OSLF.NativeTypes.Semantics.Checking Mettapedia.OSLF.NativeTypes.Semantics.Generated
open Mettapedia.OSLF.NativeTypes.Semantics.Families GSLTTypeSynthesis

def anyTarget {request : GeneralOccurrenceFrontier.Request} : InvariantTest request :=
  {accepts := fun _ => true, invariant := fun _ _ _ => rfl}

def noTarget {request : GeneralOccurrenceFrontier.Request} : InvariantTest request :=
  {accepts := fun _ => false, invariant := fun _ _ _ => rfl}

def rhoPositive (budget : Nat) :=
  run Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated [] (.base "Proc") GeneralRho.FrontierControls.rootSource
    .possibility anyTarget budget

def rhoNegative :=
  run Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated [] (.base "Proc") GeneralRho.FrontierControls.rootSource
    .outgoingUniversal noTarget 40

#guard (rhoPositive 40).verdict.readout == .decided true
#guard (rhoPositive 0).verdict.readout == .unknown
#guard (rhoPositive 40).answerFamilies.length == 1
#guard (rhoPositive 0).answerFamilies.isEmpty
#guard rhoNegative.verdict.readout == .decided false
#guard rhoNegative.counterexampleFamilies.length == 1
#guard rhoNegative.answerFamilies.isEmpty

theorem actual_COMM_step :
    (theory Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated [] (.base "Proc")).Step
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc") GeneralRho.FrontierControls.rootSource).root
      (GeneralRho.PaidControls.occurrence false ⟨0, by decide⟩).val.target := by
  change (GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.plan [] (.base "Proc")).Step
    GeneralRho.FrontierControls.rootSource.eraseBinderMetadata _
  rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.actual_plan]
  exact GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _
    (GeneralRho.PaidControls.occurrence false ⟨0, by decide⟩).property

theorem executed_COMM_native_membership :
    (gsltOSLF (theory Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated [] (.base "Proc"))).satisfies
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc") GeneralRho.FrontierControls.rootSource).root
      (questionType .possibility
        (Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc") GeneralRho.FrontierControls.rootSource)
        anyTarget).pred := by
  apply (gsltDiamond_spec (theory Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated [] (.base "Proc"))
    (continuationPredicate _ anyTarget) _).mpr
  exact ⟨_, actual_COMM_step, rfl⟩

theorem executed_COMM_native_refutation :
    ¬ (gsltOSLF (theory Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated [] (.base "Proc"))).satisfies
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc") GeneralRho.FrontierControls.rootSource).root
      (questionType .outgoingUniversal
        (Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated.request [] (.base "Proc") GeneralRho.FrontierControls.rootSource)
        noTarget).pred := by
  intro universal
  have impossible := universal _ actual_COMM_step
  exact Bool.false_ne_true impossible

theorem unfinished_native_output_can_hide_a_step :
    (run Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.generated [] Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier
      Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other .possibility
      (Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.anyTarget Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other) 0).verdict.readout = .unknown ∧
    (GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.runtimePlan [] Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier).Step
      Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.other Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha := by
  rw [run_readout]
  exact Mettapedia.OSLF.NativeTypes.Generation.BudgetControls.unknown_does_not_certify_absence

namespace Origins

open GeneralRho.PaidControls

def output := possibilityOutput (request true).plan (request true).bound (request true).expected
  (Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls.Rho.postcondition true)

/-- An observation class is not a replacement for the chosen native receipt.
The two primitive COMM matcher origins are lost by predicate projection. -/
theorem refinement_projection_is_not_injective : ¬ Function.Injective output.project := by
  intro injective
  have singleton := (NativeOutput.project_injective_iff output).mp injective (request true).root
  exact Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls.Rho.equal_targets_distinct_native_receipts.2
    (singleton.elim (Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls.Rho.family true ⟨0, by decide⟩)
      (Mettapedia.OSLF.NativeTypes.Semantics.Modal.Controls.Rho.family true ⟨1, by decide⟩))

end Origins

namespace Lambda

open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated)
open Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls (schema codes)

theorem actual_native_former_is_computed :
    (generated.nativeModalFormer? schema codes.actualInputs).isSome = true := by
  rw [native_modal_formation_exact]
  exact Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.selected_former_is_actual

def disabled : Generated :=
  {generated with logicFragment := {generated.logicFragment with core :=
    {generated.logicFragment.core with modal := false}}}

theorem disabling_modal_removes_native_output :
    disabled.nativeModalFormer? schema codes.actualInputs = none :=
  native_modal_refusal (generated := disabled) codes.actualInputs
    (disabled_modal_fragment_has_no_code (generated := disabled) codes.actualInputs rfl)

end Lambda

namespace FamilyTransport

open Mettapedia.GSLT.ProofRelevant.Canary (boolOptionEquiv)

def sourceSystem := equalityGSLT Bool (fun source target => source = false ∧ target = true)

def targetSystem := equalityGSLT Bool (fun source target => source = true ∧ target = false)

/-- The source records two independently selectable rule origins at its
initial state, and has no completed output at its final state. -/
def sourceOutput : NativeOutput sourceSystem where
  predicate := invariantPredicate sourceSystem (fun term => term = false) (by
    rintro _ _ rfl
    rfl)
  Family term := {origin : Bool // term = false}
  supportExact _ := ⟨fun ⟨witness⟩ => witness.property,
    fun supported => ⟨⟨false, supported⟩⟩⟩

/-- The target has a distinct state encoding and a distinct representation
of origins. Its predicate is stated directly on target states. -/
def targetOutput : NativeOutput targetSystem where
  predicate := invariantPredicate targetSystem (fun term => term = true) (by
    rintro _ _ rfl
    rfl)
  Family term := {origin : Option Unit // term = true}
  supportExact _ := ⟨fun ⟨witness⟩ => witness.property,
    fun supported => ⟨⟨none, supported⟩⟩⟩

def fibreEquiv (term : Bool) : sourceOutput.Family term ≃ targetOutput.Family (!term) where
  toFun witness := ⟨boolOptionEquiv witness.val, by
    change (!term) = true
    rw [witness.property]
    rfl⟩
  invFun witness := ⟨boolOptionEquiv.symm witness.val, by
    have supported : (!term) = true := witness.property
    cases term with
    | false => rfl
    | true => cases supported⟩
  left_inv witness := Subtype.ext (boolOptionEquiv.symm_apply_apply witness.val)
  right_inv witness := Subtype.ext (boolOptionEquiv.apply_symm_apply witness.val)

theorem native_membership_transport (term : Bool) :
    (gsltOSLF sourceSystem).satisfies (S := ()) term sourceOutput.nativeType.pred ↔
      (gsltOSLF targetSystem).satisfies (S := ()) (!term) targetOutput.nativeType.pred :=
  NativeOutput.nativeType_iff sourceOutput targetOutput Bool.not fibreEquiv term

theorem accepts_start_refuses_final :
    sourceOutput.predicate false ∧ ¬ sourceOutput.predicate true ∧
      targetOutput.predicate true ∧ ¬ targetOutput.predicate false := by
  exact ⟨rfl, Bool.noConfusion, rfl, Bool.noConfusion⟩

def origins : List (sourceOutput.Family false) := [⟨false, rfl⟩, ⟨true, rfl⟩, ⟨false, rfl⟩]

/-- Encoding changes the representation while keeping both the order and
the repeated first origin. -/
theorem encoded_origins :
    (origins.map (fibreEquiv false)).map Subtype.val = [none, some (), none] := rfl

theorem decoded_origins :
    (origins.map (fibreEquiv false)).map (fun witness => boolOptionEquiv.symm witness.val) =
      origins.map Subtype.val :=
  NativeOutput.ordered_readout_eq sourceOutput targetOutput Bool.not fibreEquiv false
    Subtype.val (fun witness => boolOptionEquiv.symm witness.val)
    (fun witness => boolOptionEquiv.symm_apply_apply witness.val) origins

theorem universal_origin_transport :
    (∀ witness : sourceOutput.Family false, witness.val = false) ↔
      (∀ witness : targetOutput.Family true, witness.val = none) := by
  apply NativeOutput.forall_evidence_iff sourceOutput targetOutput Bool.not fibreEquiv false
    (fun witness => witness.val = false) (fun witness => witness.val = none)
  rintro ⟨origin, _⟩
  cases origin with
  | false =>
      change (false = false) ↔ ((none : Option Unit) = none)
      simp
  | true =>
      change (true = false) ↔ ((some () : Option Unit) = none)
      simp

/-- Both sides retain the second origin that refutes the universal claim. -/
theorem universal_origin_refuted :
    ¬ (∀ witness : sourceOutput.Family false, witness.val = false) ∧
      ¬ (∀ witness : targetOutput.Family true, witness.val = none) := by
  have sourceRefuted : ¬ (∀ witness : sourceOutput.Family false, witness.val = false) := by
    intro universal
    exact Bool.false_ne_true (universal ⟨true, rfl⟩).symm
  exact ⟨sourceRefuted, fun targetUniversal =>
    sourceRefuted (universal_origin_transport.mpr targetUniversal)⟩

def collapsedOutput : NativeOutput targetSystem where
  predicate := invariantPredicate targetSystem (fun term => term = true) (by
    rintro _ _ rfl
    rfl)
  Family term := {origin : Unit // term = true}
  supportExact _ := ⟨fun ⟨witness⟩ => witness.property,
    fun supported => ⟨⟨(), supported⟩⟩⟩

/-- Keeping exactly the same predicate does not make a collapsed receipt
family a valid evidence-preserving compilation. -/
theorem collapse_keeps_support_loses_evidence :
    (∀ term, collapsedOutput.predicate term ↔ targetOutput.predicate term) ∧
      ¬ Nonempty (sourceOutput.Family false ≃ collapsedOutput.Family true) := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  rintro ⟨comparison⟩
  have same : comparison ⟨false, rfl⟩ = comparison ⟨true, rfl⟩ :=
    Subtype.ext (Subsingleton.elim _ _)
  exact Bool.false_ne_true (congrArg Subtype.val (comparison.injective same))

end FamilyTransport

end Mettapedia.OSLF.NativeTypes.Semantics.Controls
