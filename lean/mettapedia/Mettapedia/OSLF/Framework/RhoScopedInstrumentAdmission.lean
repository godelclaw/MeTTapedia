import Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase
import Mettapedia.OSLF.Framework.ScopedBindingInstrumentAdmission
import Mettapedia.OSLF.Syntax.ScopedBindingEquationContextAction
import Mettapedia.OSLF.Syntax.RhoScopedFiringSubstitution

/-!
# Binding and equation admission for original operational rho instruments

The actual original least-label base admits arbitrary partial structural
kits with their precise infinitary logical characterization. Complete kits
recover the source equation classes, and therefore earn replacement through
all retained binding paths and capture-avoiding substitutions.

Proper firing substitution is a different comparison. Every supplied firing
gives a mapped saturated event; identity labels also remain original IPO
labels without further hypotheses. Nonempty least labels retain their
separate mapped-inventory admission condition.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission

open _root_.CategoryTheory Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open ScopedEncoding ScopedInstruments RhoScopedInstrumentProperBase
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem
open ScopedInstruments.Controls (rhoTheory rho_equation_iff)

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

theorem complete_context_congruence (sourceProfile targetProfile : SourceRule → Prop)
    {sourceKit targetKit : Constructor sig → Prop}
    (sourceComplete : ∀ constructor, sourceKit constructor)
    (targetComplete : ∀ constructor, targetKit constructor)
    {source destination : Scope sig}
    (context : BindingContext sig source destination)
    {before after : Term sig source.1 source.2}
    (related : ScopedInstruments.Bisimilar (base sourceProfile) sourceKit (.term before) (.term after)) :
    ScopedInstruments.Bisimilar (base targetProfile) targetKit
      (.term (fillContext context before)) (.term (fillContext context after)) :=
  (instrumented_reconstruction targetProfile targetComplete _ _).mpr
    (ScopedEquationContexts.path_respects rhoSourceE context
      ((instrumented_reconstruction sourceProfile sourceComplete before after).mp related))

theorem complete_substitution_congruence (sourceProfile targetProfile : SourceRule → Prop)
    {sourceKit targetKit : Constructor sig → Prop}
    (sourceComplete : ∀ constructor, sourceKit constructor)
    (targetComplete : ∀ constructor, targetKit constructor)
    {context destination : Ctx sig} {sort : Srt} (change : Sub sig context destination)
    {before after : Term sig context sort}
    (related : ScopedInstruments.Bisimilar (base sourceProfile) sourceKit (.term before) (.term after)) :
    ScopedInstruments.Bisimilar (base targetProfile) targetKit
      (.term (bind change before)) (.term (bind change after)) := by
  have equation := (instrumented_reconstruction sourceProfile sourceComplete before after).mp related
  have admitted := (rho_equation_iff before after).mpr equation
  exact (instrumented_reconstruction targetProfile targetComplete _ _).mpr
    ((rho_equation_iff _ _).mp (rhoTheory.bind_relation change admitted))

theorem complete_context_logical_congruence (sourceProfile targetProfile : SourceRule → Prop)
    {sourceKit targetKit : Constructor sig → Prop}
    (sourceComplete : ∀ constructor, sourceKit constructor)
    (targetComplete : ∀ constructor, targetKit constructor)
    {source destination : Scope sig} (context : BindingContext sig source destination)
    {before after : Term sig source.1 source.2}
    (same : ScopedInstruments.LogicallyEquivalent (base sourceProfile) sourceKit before after) :
    ScopedInstruments.LogicallyEquivalent (base targetProfile) targetKit
      (fillContext context before) (fillContext context after) :=
  (instrumented_partial_adequacy targetProfile targetKit _ _).mpr
    (complete_context_congruence sourceProfile targetProfile sourceComplete targetComplete context
      ((instrumented_partial_adequacy sourceProfile sourceKit before after).mp same))

theorem original_structural_test_is_interactive (admitted : SourceRule → Prop)
    {opened : Constructor sig → Prop} (constructor : Constructor sig) (allowed : opened constructor)
    (clauses : (position : Fin ((signature sig).arity constructor)) →
      ScopedInstruments.Formula sig (base admitted).Atom (base admitted).Label
        ((signature sig).input constructor position))
    (value : Term sig ((signature sig).output constructor).1 ((signature sig).output constructor).2) :
    ScopedInstruments.Holds (base admitted) (.node constructor clauses) value ↔
      ∃ arguments : Arguments constructor,
        Act (base admitted) opened (.ask constructor) (.term value) (.bundle constructor arguments) ∧
        ∀ position, ∃ projected : Term sig ((signature sig).input constructor position).1
            ((signature sig).input constructor position).2,
          Act (base admitted) opened (.get constructor position) (.bundle constructor arguments) (.term projected) ∧
          ScopedInstruments.Holds (base admitted) (clauses position) projected :=
  ScopedInstruments.Admission.structural_iff_interactions (base admitted) constructor allowed clauses value

theorem proper_substitution_keeps_enabled_event (admitted : SourceRule → Prop)
    {context destination : Ctx sig} (change : Sub sig context destination)
    (label : Process context) {before after : Term sig context Srt.pr}
    (proper : (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, label⟩ before after) :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := admitted)
      (join (bindQ change (project before)) (bindQ change label)) (bindQ change (project after)) := by
  obtain ⟨receipt⟩ := (proper_iff_complete_firing admitted label before after).mp proper
  exact RhoScopedFiringSubstitution.enabled_after_filling_mapped_label change receipt

theorem identity_proper_substitution (admitted : SourceRule → Prop)
    {context destination : Ctx sig} (change : Sub sig context destination)
    {before after : Term sig context Srt.pr}
    (proper : (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, zero context⟩ before after) :
    (base admitted).act (source := (destination, Srt.pr)) (target := (destination, Srt.pr))
      ⟨destination, zero destination⟩ (bind change before) (bind change after) := by
  apply (identity_proper_iff_original_event admitted _ _).mpr
  exact RhoScopedParallelEvents.step_substitution change
    ((identity_proper_iff_original_event admitted before after).mp proper)

end Mettapedia.OSLF.Framework.RhoScopedInstrumentAdmission
