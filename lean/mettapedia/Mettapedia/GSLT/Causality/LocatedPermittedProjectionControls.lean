import Mettapedia.GSLT.Causality.LocatedPermittedProjection
import Mettapedia.GSLT.Causality.LocatedPermittedHistoryControls

/-!
# Complete paid path projection and its funding boundary

Two actual funded receive orders project to different original paths, with
the same complete original endpoint. A nonconstant original valuation is
read identically on each supplied paid path and its projection. An enabled
original receive cannot be lifted from the configuration with no purse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.LocatedProjectionControls

open OccurrenceHistory Controls LocatedHistoryControls

def firstOriginal :
    OccurrencePath persistentReceiver.presentation (leftPart start) (leftPart finish) :=
  locatedOriginalPath persistentReceiver permitted (fun _ => 0) (fun _ => true) firstThenSecond

def secondOriginal :
    OccurrencePath persistentReceiver.presentation (leftPart start) (leftPart finish) :=
  locatedOriginalPath persistentReceiver permitted (fun _ => 0) (fun _ => true) secondThenFirst

theorem first_projection_retains_the_complete_order :
    persistentReceiver.pathEntries firstOriginal =
      [⟨(), takeAgain 1⟩, ⟨(), takeAgain 2⟩] := by
  unfold firstOriginal
  exact (locatedOriginalPath_entries persistentReceiver permitted
    (fun _ => 0) (fun _ => true) firstThenSecond).trans first_order_complete_readout

theorem second_projection_retains_the_complete_order :
    persistentReceiver.pathEntries secondOriginal =
      [⟨(), takeAgain 2⟩, ⟨(), takeAgain 1⟩] := by
  unfold secondOriginal
  exact (locatedOriginalPath_entries persistentReceiver permitted
    (fun _ => 0) (fun _ => true) secondThenFirst).trans second_order_complete_readout

theorem projection_preserves_distinct_actual_histories : firstOriginal ≠ secondOriginal := by
  intro same
  have readings := congrArg persistentReceiver.pathEntries same
  rw [first_projection_retains_the_complete_order,
    second_projection_retains_the_complete_order] at readings
  have impossible : (1 : Nat) = 2 :=
    congrArg (fun entry : persistentReceiver.Entry => (entry.2 : Nat))
      (List.cons.inj readings).1
  cases impossible

def messageValue : ∀ {site : persistentReceiver.Site}, persistentReceiver.Instance site → Nat :=
  fun {_site} => fun value : Nat => 20 * value

theorem supplied_nonconstant_valuation_has_the_original_readout :
    (persistentReceiver.instanceValuation messageValue).onPath firstOriginal =
      (system.instanceValuation fun paid => messageValue paid.1.val).onPath firstThenSecond :=
  locatedOriginalPath_valuation persistentReceiver permitted (fun _ => 0)
    (fun _ => true) messageValue firstThenSecond

theorem both_actual_paths_have_value_sixty :
    (persistentReceiver.instanceValuation messageValue).onPath firstOriginal = 60 ∧
      (persistentReceiver.instanceValuation messageValue).onPath secondOriginal = 60 := by
  constructor
  · rw [persistentReceiver.instanceValuation_onPath,
      first_projection_retains_the_complete_order]
    rfl
  · rw [persistentReceiver.instanceValuation_onPath,
      second_projection_retains_the_complete_order]
    rfl

def unpaidStart : Multiset (Res ⊕ (Nat × List Bool)) := marking twoMessages 0

def unpaidAfterFirst : Multiset (Res ⊕ (Nat × List Bool)) :=
  marking {Res.receiver, Res.message 2, Res.received 1} 0

theorem original_receive_is_actually_enabled_without_a_purse :
    persistentReceiver.Enables (leftPart unpaidStart) (takeAgain 1) := by
  unfold unpaidStart
  rw [leftPart_marking]
  unfold System.Enables
  decide

theorem original_receive_has_no_paid_path_from_the_empty_purse :
    ¬ Nonempty (OccurrencePath system.presentation unpaidStart unpaidAfterFirst) := by
  rintro ⟨path⟩
  have bound := locatedPermitted_firing_bound persistentReceiver permitted
    (fun _ => 0) (fun _ => true) path
  have lengthZero : (system.pathEntries path).length = 0 := by
    change (system.pathEntries path).length ≤ cells (0 : Multiset (Nat × List Bool)) at bound
    simpa only [cells, Multiset.map_zero, Multiset.sum_zero, Nat.le_zero] using bound
  have entriesNil : system.pathEntries path = [] := List.length_eq_zero_iff.mp lengthZero
  have endpoint := system.fires_pathEntries path
  rw [entriesNil] at endpoint
  change unpaidAfterFirst = unpaidStart at endpoint
  have resources := congrArg leftPart endpoint
  change leftPart (marking {Res.receiver, Res.message 2, Res.received 1}
      (0 : Multiset (Nat × List Bool))) = leftPart (marking twoMessages 0) at resources
  rw [leftPart_marking, leftPart_marking] at resources
  exact (by decide : ({Res.receiver, Res.message 2, Res.received 1} : Multiset Res) ≠
    twoMessages) resources

end Mettapedia.GSLT.Causality.ResourceInteraction.LocatedProjectionControls
