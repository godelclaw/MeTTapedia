import Mettapedia.CognitiveArchitecture.Consciousness.InterpretationAssessment
import Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization

/-!
# Interpretation-relative assessment of workspace receipt currency

The general partial-observation framework is instantiated with the existing
workspace's modal queries and executable receipt transitions.  Its outcome is
the operational proposition that a specialist holds a current, linked delivery.
This is an evidence assessment, not an assignment of experienced wellbeing.

A declared current-delivery query suffices for this particular assessment.
Published content alone does not: connected and disconnected executions agree
on content but disagree on linked delivery.  Re-publication with unchanged
content keeps the historical receipt while invalidating its current authority.
No live-host correspondence or experiential interpretation follows from these
Lean model results.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.WorkspaceAssessment

open Mettapedia.CategoryTheory.PartialSections
open Mettapedia.CognitiveArchitecture.Consciousness.InterpretationAssessment
open Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace
open Mettapedia.GSLT.HennessyMilner

open PhenomenalRealization

abbrev WorkspaceState := State Nat Bool

/-- The operational outcome is interpreted through the existing receipt law.
The hypothesis index supplies no additional experiential premise. -/
def receiptModel : Model WorkspaceState ReceiptDescriptions.Query Prop Unit Prop where
  observe state query := (ReceiptDescriptions.full state).values ⟨query, Set.mem_univ _⟩
  interprets _ state outcome := outcome = CurrentDelivery state true

theorem observations_are_full (state : WorkspaceState) :
    total (receiptModel.observe state) = ReceiptDescriptions.full state := by
  apply View.ext
  · rfl
  intro _ _ _
  rfl

/-- Only the already defined current-delivery atom is added to the assay. -/
def currencyContext : Set ReceiptDescriptions.Query :=
  {Formula.atom (Atom.current true)}

def currency (state : WorkspaceState) : View ReceiptDescriptions.Query Prop :=
  restrict currencyContext (ReceiptDescriptions.full state)

theorem currency_refines_full (state : WorkspaceState) :
    currency state ≤ ReceiptDescriptions.full state := restrict_le _ _

/-- Agreement on the declared currency query is precisely agreement on the
existing current-delivery predicate, regardless of other unobserved answers. -/
theorem currency_compatible_iff (origin candidate : WorkspaceState) :
    CompatibleState receiptModel (currency origin) candidate ↔
      (CurrentDelivery origin true ↔ CurrentDelivery candidate true) := by
  constructor
  · intro fits
    have answer := fits.2 (Formula.atom (Atom.current true))
      ⟨Set.mem_univ _, rfl⟩ (Set.mem_univ _)
    exact Iff.of_eq answer
  · intro currentAgreement
    refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
    intro query member _
    have queryEq : query = Formula.atom (Atom.current true) := by
      exact member.2
    subst query
    exact propext currentAgreement

theorem actual_currency_outcome (state : WorkspaceState) :
    CurrentDelivery state true ∈ possible receiptModel Set.univ (currency state) :=
  ⟨(), state, Set.mem_univ _, (currency_compatible_iff state state).mpr Iff.rfl, rfl⟩

/-- Universal assessment quantifies over all compatible operational states,
and the actual state provides its non-vacuity witness. -/
theorem currency_robust_iff (state : WorkspaceState) :
    Robust receiptModel Set.univ (currency state) (fun outcome : Prop => outcome) ↔
      CurrentDelivery state true := by
  constructor
  · intro robust
    exact robust.2 _ (actual_currency_outcome state)
  · intro current
    refine ⟨⟨_, actual_currency_outcome state⟩, ?_⟩
    rintro outcome ⟨_, candidate, _, fits, interpreted⟩
    have candidateCurrent := (currency_compatible_iff state candidate).mp fits |>.mp current
    exact interpreted.symm ▸ candidateCurrent

theorem actual_full_outcome (state : WorkspaceState) :
    CurrentDelivery state true ∈ possible receiptModel Set.univ (ReceiptDescriptions.full state) := by
  refine ⟨(), state, Set.mem_univ _, ?_, rfl⟩
  rw [CompatibleState, observations_are_full]

theorem full_robust_iff (state : WorkspaceState) :
    Robust receiptModel Set.univ (ReceiptDescriptions.full state) (fun outcome : Prop => outcome) ↔
      CurrentDelivery state true := by
  constructor
  · intro robust
    exact robust.2 _ (actual_full_outcome state)
  · intro current
    exact robust_refinement receiptModel Set.univ (currency_refines_full state)
      ((currency_robust_iff state).mpr current) ⟨_, actual_full_outcome state⟩

theorem content_fits_connected :
    CompatibleState receiptModel (ReceiptDescriptions.content ReceiptDescriptions.connected) ReceiptDescriptions.connected := by
  rw [CompatibleState, observations_are_full]
  exact ReceiptDescriptions.content_refines_full _

theorem content_fits_disconnected :
    CompatibleState receiptModel (ReceiptDescriptions.content ReceiptDescriptions.connected) ReceiptDescriptions.disconnected := by
  rw [CompatibleState, observations_are_full, ReceiptDescriptions.content_agrees]
  exact ReceiptDescriptions.content_refines_full _

/-- Both outcomes have complete operational witnesses, rather than unsupported
labels attached to a published transcript. -/
theorem content_has_opposed_delivery_outcomes :
    CurrentDelivery ReceiptDescriptions.connected true ∈
        possible receiptModel Set.univ (ReceiptDescriptions.content ReceiptDescriptions.connected) ∧
      CurrentDelivery ReceiptDescriptions.disconnected true ∈
        possible receiptModel Set.univ (ReceiptDescriptions.content ReceiptDescriptions.connected) ∧
      CurrentDelivery ReceiptDescriptions.connected true ∧
      ¬ CurrentDelivery ReceiptDescriptions.disconnected true :=
  ⟨⟨(), ReceiptDescriptions.connected, Set.mem_univ _, content_fits_connected, rfl⟩,
    ⟨(), ReceiptDescriptions.disconnected, Set.mem_univ _, content_fits_disconnected, rfl⟩,
    ReceiptDescriptions.connected_delivery_current, ReceiptDescriptions.disconnected_delivery_not_current⟩

theorem content_does_not_certify_current_delivery :
    ¬ Robust receiptModel Set.univ (ReceiptDescriptions.content ReceiptDescriptions.connected)
      (fun outcome : Prop => outcome) :=
  robust_false_of_counterexample receiptModel
    content_has_opposed_delivery_outcomes.2.1 ReceiptDescriptions.disconnected_delivery_not_current

theorem connected_currency_certifies_current_delivery :
    Robust receiptModel Set.univ (currency ReceiptDescriptions.connected) (fun outcome : Prop => outcome) :=
  (currency_robust_iff _).mpr ReceiptDescriptions.connected_delivery_current

theorem disconnected_currency_refuses_current_delivery :
    ¬ Robust receiptModel Set.univ (currency ReceiptDescriptions.disconnected)
      (fun outcome : Prop => outcome) := by
  rw [currency_robust_iff]
  exact ReceiptDescriptions.disconnected_delivery_not_current

/-! ## Historical evidence survives without current authority -/

/-- Consume the actual publication and then advance its epoch without changing
the published payload.  These are the existing executable transitions. -/
def advanced : WorkspaceState :=
  step (step ReceiptDescriptions.connected (.consume true))
    (.publish (Agent.ContextEpoch.prepare ReceiptDescriptions.connected.context ReceiptDescriptions.connected.context))

theorem advanced_retains_historical_receipt :
    advanced.evidence true = some
        (Agent.ContextEpoch.prepare ReceiptDescriptions.connected.context ReceiptDescriptions.connected.context.view) ∧
      ¬ CurrentDelivery advanced true :=
  consume_then_publish_retains_stale_receipt ReceiptDescriptions.connected true
    ReceiptDescriptions.connected.context rfl

theorem advanced_content_unchanged :
    advanced.context.view = ReceiptDescriptions.connected.context.view := by
  simp [advanced, step, Agent.ContextEpoch.publish_current]

theorem advanced_content_description_unchanged :
    ReceiptDescriptions.content advanced = ReceiptDescriptions.content ReceiptDescriptions.connected := by
  apply View.ext
  · rfl
  intro query member _
  obtain ⟨history, rfl⟩ := member
  change (advanced.context.view = history) = (ReceiptDescriptions.connected.context.view = history)
  rw [advanced_content_unchanged]

/-- The old currency description is historical information; after the epoch
change it no longer fits the current operational state. -/
theorem old_currency_does_not_fit_advanced :
    ¬ CompatibleState receiptModel (currency ReceiptDescriptions.connected) advanced := by
  intro fits
  exact advanced_retains_historical_receipt.2
    ((currency_compatible_iff _ _).mp fits |>.mp ReceiptDescriptions.connected_delivery_current)

theorem advanced_currency_refuses_current_delivery :
    ¬ Robust receiptModel Set.univ (currency advanced) (fun outcome : Prop => outcome) := by
  rw [currency_robust_iff]
  exact advanced_retains_historical_receipt.2

theorem unchanged_content_can_hide_lost_currency :
    ReceiptDescriptions.content advanced = ReceiptDescriptions.content ReceiptDescriptions.connected ∧
      Robust receiptModel Set.univ (currency ReceiptDescriptions.connected) (fun outcome : Prop => outcome) ∧
      ¬ Robust receiptModel Set.univ (currency advanced) (fun outcome : Prop => outcome) :=
  ⟨advanced_content_description_unchanged, connected_currency_certifies_current_delivery,
    advanced_currency_refuses_current_delivery⟩

end Mettapedia.CognitiveArchitecture.Consciousness.WorkspaceAssessment
