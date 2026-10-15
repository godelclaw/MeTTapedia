import Mettapedia.OSLF.Framework.ScopedBindingInstrumentControls
import Mettapedia.OSLF.Syntax.RhoScopedFiniteSuccessors
import Mettapedia.OSLF.Syntax.RhoScopedParallelSourceAdequacy

/-!
# Original least-context rho transitions as a binding-instrument base

The proper label stores the actual ambient variable context and an original
process class. Its action consults the independently authored original IPO
relation. The argument and result interfaces are checked by equality of
complete sorted equation-class readings, so proper reactions cannot turn
name-valued inputs into process-valued ones.

This base joins the original COMM/Drop system to the generic binding
instrument logic. Its finite proper outcome cover is earned from actual
original successors, independently of the number of firing receipts or raw
syntax representatives. Structural ask/get steps are still explicit
instruments; they are not granted reduction permission beneath binders.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase

open _root_.CategoryTheory Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedParallelContexts RhoScopedParallelReactiveSystem
open ScopedEncoding ScopedInstruments
open Mettapedia.GSLT.RedexRelativeCongruence
open ScopedInstruments.Controls (rhoTheory rho_equation_iff RhoPacked pack pack_equation)

structure ProperLabel where
  context : Ctx sig
  surrounding : Process context

def Proper (admitted : SourceRule → Prop) (label : ProperLabel)
    (before after : RhoPacked) : Prop :=
  ∃ first second : Process label.context,
    before = ⟨(label.context, Srt.pr), first⟩ ∧
    after = ⟨(label.context, Srt.pr), second⟩ ∧
    ActIPO (reactionRules sourceRules admitted) (arrow label.surrounding)
      (arrow first) (arrow second)

def base (admitted : SourceRule → Prop) : BaseSystem rhoTheory where
  Atom := Empty
  observes atom := atom.elim
  observes_resp atom := atom.elim
  Label := ProperLabel
  act := fun label {_} {_} before after => Proper admitted label (pack before) (pack after)
  act_resp_left := by
    intro label source target first second next related step
    refine ⟨next, ?_, rhoTheory.reflexive next⟩
    rw [← pack_equation related]
    exact step
  act_resp_right := by
    intro label source target start next next' step related
    rw [← pack_equation related]
    exact step

theorem proper_iff_original (admitted : SourceRule → Prop) {context : Ctx sig}
    (label : Process context) (before after : Term sig context Srt.pr) :
    (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, label⟩ before after ↔
      ActIPO (reactionRules sourceRules admitted) (arrow label)
        (arrow (project before)) (arrow (project after)) := by
  constructor
  · rintro ⟨first, second, sourceRead, targetRead, firing⟩
    have firstRead : project before = first := eq_of_heq (Sigma.mk.inj_iff.mp sourceRead).2
    have secondRead : project after = second := eq_of_heq (Sigma.mk.inj_iff.mp targetRead).2
    rw [firstRead, secondRead]
    exact firing
  · intro firing
    exact ⟨project before, project after, rfl, rfl, firing⟩

theorem proper_iff_complete_firing (admitted : SourceRule → Prop) {context : Ctx sig}
    (label : Process context) (before after : Term sig context Srt.pr) :
    (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, label⟩ before after ↔
      Nonempty (Firing (rules := sourceRules) (admitted := admitted)
        (project before) label (project after)) :=
  (proper_iff_original admitted label before after).trans (firing_iff_actIPO _ _ _).symm

theorem proper_iff_computed (admitted : SourceRule → Prop) {context : Ctx sig}
    (label : Process context) (before after : Term sig context Srt.pr) :
    (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, label⟩ before after ↔
      ∃ root : Root sourceRules admitted context,
        label = leastLabel (project before) root ∧
        project after = join root.target (reactionRemainder (project before) root) :=
  (proper_iff_original admitted label before after).trans (actIPO_iff_computed _ _ _)

theorem identity_proper_iff_original_event (admitted : SourceRule → Prop) {context : Ctx sig}
    (before after : Term sig context Srt.pr) :
    (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, zero context⟩ before after ↔
      RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := admitted)
        (project before) (project after) := by
  rw [proper_iff_original, arrow_zero]
  exact (step_iff_actIPO_identity _ _).symm

theorem identity_proper_iff_printed_source (before after : Term sig [] Srt.pr) :
    (base withReflection).act (source := ([], Srt.pr)) (target := ([], Srt.pr))
      ⟨[], zero []⟩ before after ↔ ParallelStepModE before after :=
  (identity_proper_iff_original_event withReflection before after).trans
    (RhoScopedParallelSourceAdequacy.parallelStepModE_iff_event before after).symm

theorem proper_interface (admitted : SourceRule → Prop) (label : ProperLabel)
    {source target : Scope sig} (before : Term sig source.1 source.2)
    (after : Term sig target.1 target.2)
    (firing : (base admitted).act (source := source) (target := target) label before after) :
    source = (label.context, Srt.pr) ∧ target = (label.context, Srt.pr) := by
  obtain ⟨_first, _second, sourceRead, targetRead, _step⟩ := firing
  exact ⟨congrArg Sigma.fst sourceRead, congrArg Sigma.fst targetRead⟩

theorem name_has_no_proper_reaction (admitted : SourceRule → Prop) (label : ProperLabel)
    {context : Ctx sig} (name : Term sig context Srt.nm)
    {target : Scope sig} (after : Term sig target.1 target.2) :
    ¬ (base admitted).act (source := (context, Srt.nm)) (target := target) label name after := by
  intro firing
  have sorts := congrArg Prod.snd
    (proper_interface admitted label (source := (context, Srt.nm)) (target := target) name after firing).1
  cases sorts

def properTargets (admitted : SourceRule → Prop) {context : Ctx sig}
    (label : Process context) (before : Term sig context Srt.pr) : Set (Process context) :=
  {result | ∃ after : Term sig context Srt.pr,
    (base admitted).act (source := (context, Srt.pr)) (target := (context, Srt.pr))
      ⟨context, label⟩ before after ∧ project after = result}

theorem proper_target_iff_catalogue (admitted : SourceRule → Prop) {context : Ctx sig}
    (label : Process context) (before : Term sig context Srt.pr) (result : Process context) :
    result ∈ properTargets admitted label before ↔
      result ∈ RhoScopedFiniteSuccessors.successors admitted (project before) label := by
  rw [RhoScopedFiniteSuccessors.mem_successors_iff]
  constructor
  · rintro ⟨after, proper, rfl⟩
    exact (proper_iff_original admitted label before after).mp proper
  · intro actual
    refine ⟨Quotient.out result, ?_, Quotient.out_eq result⟩
    apply (proper_iff_original admitted label before _).mpr
    simpa only [project, Quotient.out_eq] using actual

theorem proper_targets_finite (admitted : SourceRule → Prop) {context : Ctx sig}
    (label : Process context) (before : Term sig context Srt.pr) :
    (properTargets admitted label before).Finite := by
  apply (RhoScopedFiniteSuccessors.successors admitted (project before) label).finite_toSet.subset
  intro result actual
  exact (proper_target_iff_catalogue admitted label before result).mp actual

theorem instrumented_reconstruction (admitted : SourceRule → Prop)
    {opened : Constructor sig → Prop} (complete : ∀ constructor, opened constructor)
    {context : Ctx sig} {sort : Srt} (before after : Term sig context sort) :
    ScopedInstruments.Bisimilar (base admitted) opened (.term before) (.term after) ↔
      EqClosure rhoSourceE before after :=
  (ScopedInstruments.bisimilar_iff_equation (base admitted) complete before after).trans
    (rho_equation_iff before after)

theorem instrumented_partial_adequacy (admitted : SourceRule → Prop)
    (opened : Constructor sig → Prop) {context : Ctx sig} {sort : Srt}
    (before after : Term sig context sort) :
    ScopedInstruments.LogicallyEquivalent (base admitted) opened before after ↔
      ScopedInstruments.Bisimilar (base admitted) opened (.term before) (.term after) :=
  ScopedInstruments.logicallyEquivalent_iff_bisimilar (base admitted) opened before after

theorem larger_kit_refines (admitted : SourceRule → Prop)
    {smaller larger : Constructor sig → Prop}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {first second : ScopedInstruments.State sig}
    (related : ScopedInstruments.Bisimilar (base admitted) larger first second) :
    ScopedInstruments.Bisimilar (base admitted) smaller first second :=
  ScopedInstruments.bisimilar_mono (base admitted) inclusion related

end Mettapedia.OSLF.Framework.RhoScopedInstrumentProperBase
