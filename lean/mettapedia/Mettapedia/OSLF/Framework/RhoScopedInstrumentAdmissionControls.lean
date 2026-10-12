import Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission
import Mettapedia.OSLF.Syntax.RhoScopedFiringSubstitutionControls
import Mettapedia.OSLF.Syntax.RhoScopedEquationBindingControls

/-!
# Original reactions, dependent binder tests and a partial observation ceiling

The original COMM and separately admitted Drop rule are proper actions of
the binding instrument system. An input test returns the actual enclosing
name beneath its binder. Its characteristic postcondition rejects capture
even modulo the original equations.

The complete kit transports equation-compatible replacement through an
actual input frame. With no structural instruments, all names at a fixed
interface are bisimilar; this observation does not license their capture.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmissionControls

open _root_.CategoryTheory Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open ScopedEncoding ScopedInstruments RhoScopedInstrumentProperBase
open RhoScopedInstrumentAdmission RhoScopedParallelEvents RhoScopedParallelReactiveSystem
open RhoScopedParallelReactiveControls RhoScopedEquationEventControls
open ScopedInstruments.Controls (rhoTheory rho_equation_iff rhoInput inputArguments enclosingBody)

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def completeKit : Constructor sig → Prop := fun _ => True
def noStructuralInstruments : Constructor sig → Prop := fun _ => False

theorem original_comm_is_proper :
    Act (base core) noStructuralInstruments
      (.proper ⟨[], project RhoSourceOutputPredicate.output⟩)
      (.term waitingInput) (.term (null : Term sig [] Srt.pr)) :=
  .proper ((proper_iff_original core _ _ _).mpr actual_comm_transition)

theorem original_drop_is_proper :
    Act (base withReflection) noStructuralInstruments (.proper ⟨[], zero []⟩)
      (.term dropChan) (.term (null : Term sig [] Srt.pr)) :=
  .proper ((identity_proper_iff_original_event withReflection _ _).mpr actual_drop_step)

def inputClauses (position : Fin ((signature sig).arity rhoInput)) :
    ScopedInstruments.Formula sig (base core).Atom (base core).Label
      ((signature sig).input rhoInput position) :=
  SortedInstrumentCongruence.characteristic (encode (readArguments rhoInput inputArguments position))

theorem each_input_postcondition_is_satisfied (position : Fin ((signature sig).arity rhoInput)) :
    ScopedInstruments.Holds (base core) (inputClauses position)
      (readArguments rhoInput inputArguments position) :=
  (ScopedInstruments.characteristic_iff (base core) _ _).mpr (rhoTheory.reflexive _)

def inputTest : ScopedInstruments.Formula sig (base core).Atom (base core).Label ([Srt.nm], Srt.pr) :=
  @SortedInstrumentCongruence.Formula.node (signature sig) (base core).Atom (base core).Label
    rhoInput inputClauses

theorem input_test_is_satisfied :
    ScopedInstruments.Holds (base core) inputTest
      RhoScopedEquationBindingControls.expectedOpenTarget :=
  ⟨inputArguments, rhoTheory.reflexive _, each_input_postcondition_is_satisfied⟩

theorem input_test_has_actual_ask_get_trace :
    ∃ arguments : Arguments rhoInput,
      Act (base core) completeKit (.ask rhoInput)
        (.term RhoScopedEquationBindingControls.expectedOpenTarget) (.bundle rhoInput arguments) ∧
      ∀ position, ∃ projected : Term sig ((signature sig).input rhoInput position).1
          ((signature sig).input rhoInput position).2,
        Act (base core) completeKit (.get rhoInput position)
          (.bundle rhoInput arguments) (.term projected) ∧
        ScopedInstruments.Holds (base core) (inputClauses position) projected :=
  (original_structural_test_is_interactive core rhoInput (show completeKit rhoInput from trivial)
    inputClauses _).mp input_test_is_satisfied

theorem input_returns_actual_enclosing_name :
    Act (base core) completeKit (.get rhoInput 1)
      (.bundle rhoInput inputArguments) (.term enclosingBody) :=
  .get rhoInput trivial 1 (rhoTheory.reflexive _)

def capturedBody : Term sig [Srt.nm, Srt.nm] Srt.pr :=
  .op Op.drp (.cons (.var .zero) .nil)

theorem original_body_not_captured_modulo_equations :
    ¬ EqClosure rhoSourceE enclosingBody capturedBody := by
  intro equation
  have encoded := congrArg RhoSchema.IntrinsicEncoding.encodeEquationClass (Quotient.sound equation)
  change RhoSchema.IntrinsicEncoding.encodeEquationClass (project enclosingBody) =
    RhoSchema.IntrinsicEncoding.encodeEquationClass (project capturedBody) at encoded
  exact (by decide +kernel :
    RhoSchema.IntrinsicEncoding.encodeEquationClass (project enclosingBody) ≠
      RhoSchema.IntrinsicEncoding.encodeEquationClass (project capturedBody)) encoded

theorem body_postcondition_rejects_capture :
    ¬ ScopedInstruments.Holds (base core) (inputClauses 1) capturedBody := by
  intro holds
  have related := (ScopedInstruments.characteristic_iff (base core) enclosingBody capturedBody).mp holds
  exact original_body_not_captured_modulo_equations
    (EqClosure.symm ((rho_equation_iff _ _).mp related))

theorem complete_kit_rejects_capture :
    ¬ ScopedInstruments.Bisimilar (base core) completeKit (.term enclosingBody) (.term capturedBody) :=
  fun related => original_body_not_captured_modulo_equations
    ((instrumented_reconstruction core (fun _ => trivial) _ _).mp related)

theorem complete_kit_replacement_under_actual_input :
    ScopedInstruments.Bisimilar (base withReflection) completeKit
      (.term (fillContext RhoScopedEquationBindingControls.inputBodyContext
        (parallel enclosingBody null)))
      (.term (fillContext RhoScopedEquationBindingControls.inputBodyContext enclosingBody)) :=
  complete_context_congruence core withReflection (fun _ => trivial) (fun _ => trivial)
    RhoScopedEquationBindingControls.inputBodyContext
    ((instrumented_reconstruction core (fun _ => trivial) _ _).mpr
      (parallel_null_equation enclosingBody))

theorem name_has_no_instrument_step (admitted : SourceRule → Prop)
    {context : Ctx sig} (name : Term sig context Srt.nm)
    (label : ScopedInstruments.Label sig (base admitted).Label) (target : ScopedInstruments.State sig) :
    ¬ Act (base admitted) noStructuralInstruments label (.term name) target := by
  intro step
  generalize sourceRead : (ScopedInstruments.State.term name : ScopedInstruments.State sig) = source at step
  cases step with
  | @proper label sourceScope targetScope start next fired =>
      have sourceInterface := congrArg (fun state : ScopedInstruments.State sig =>
        match state with
        | @ScopedInstruments.State.term _ context sort _ => some (context, sort)
        | .bundle _ _ => none) sourceRead
      have sourceSort := congrArg Prod.snd (Option.some.inj sourceInterface)
      have requiredSort := congrArg Prod.snd
        (proper_interface admitted label (source := sourceScope) (target := targetScope) start next fired).1
      change Srt.nm = sourceScope.2 at sourceSort
      rw [← sourceSort] at requiredSort
      cases requiredSort
  | ask _ allowed _ => exact allowed
  | get _ allowed _ _ => exact allowed
  | build _ allowed _ => exact allowed

def nameRelation (context : Ctx sig) (first second : ScopedInstruments.State sig) : Prop :=
  ∃ before after : Term sig context Srt.nm, first = .term before ∧ second = .term after

theorem names_related_with_no_structural_instruments (admitted : SourceRule → Prop)
    {context : Ctx sig} (before after : Term sig context Srt.nm) :
    ScopedInstruments.Bisimilar (base admitted) noStructuralInstruments (.term before) (.term after) := by
  refine ⟨nameRelation context, ⟨?_, ?_, ?_⟩, before, after, rfl, rfl⟩
  · rintro _ _ ⟨first, second, rfl, rfl⟩ label target step
    exact False.elim (name_has_no_instrument_step admitted first label target step)
  · rintro _ _ ⟨first, second, rfl, rfl⟩ label target step
    exact False.elim (name_has_no_instrument_step admitted second label target step)
  · rintro _ _ ⟨first, second, rfl, rfl⟩ atom
    cases atom with
    | inl scope => exact Iff.rfl
    | inr impossible => exact impossible.elim

theorem different_names_have_the_same_empty_kit_answers :
    ScopedInstruments.LogicallyEquivalent (base core) noStructuralInstruments
      (.var (.zero : Var [Srt.nm, Srt.nm] Srt.nm)) (.var (.succ .zero)) :=
  (instrumented_partial_adequacy core noStructuralInstruments _ _).mpr
    (names_related_with_no_structural_instruments core _ _)

theorem different_names_are_distinct_original_classes :
    project (.var (.zero : Var [Srt.nm, Srt.nm] Srt.nm)) ≠ project (.var (.succ .zero)) :=
  RhoScopedFiringSubstitutionControls.original_names_distinct

end Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmissionControls
