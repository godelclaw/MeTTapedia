import Mettapedia.GSLT.Causality.LocatedPermittedHistory

/-!
# Located permission, exact payment and retained ordering controls

Two admitted messages consume successive cells of one located purse. Their
two possible orders reach the same complete endpoint but retain different
original firing lists. The final cell account recovers total spending and
does not recover that list. Separate controls reject an unpermitted firing,
the correct key at another place and a correct key buried below the head.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.LocatedHistoryControls

open OccurrenceHistory Controls

def permitted : ∀ {site : persistentReceiver.Site}, persistentReceiver.Instance site → Prop :=
  fun firing => firing = (1 : Nat) ∨ firing = (2 : Nat)

def system : System (Res ⊕ (Nat × List Bool)) :=
  locatedPermitted persistentReceiver permitted (fun _ => 0) (fun _ => true)

def pick (value : Nat) (permission : value = 1 ∨ value = 2) (tail : List Bool) :
    system.Instance () := (⟨value, permission⟩, tail)

def start : Multiset (Res ⊕ (Nat × List Bool)) :=
  marking twoMessages {(0, [true, true])}

def afterFirst : Multiset (Res ⊕ (Nat × List Bool)) :=
  marking {Res.receiver, Res.message 2, Res.received 1} {(0, [true])}

def afterSecond : Multiset (Res ⊕ (Nat × List Bool)) :=
  marking {Res.receiver, Res.message 1, Res.received 2} {(0, [true])}

def finish : Multiset (Res ⊕ (Nat × List Bool)) :=
  marking {Res.receiver, Res.received 1, Res.received 2} {(0, [])}

def firstThenSecond : OccurrencePath system.presentation start finish :=
  .cons (show Occurrence system.presentation start afterFirst from
      ⟨(), ⟨pick 1 (Or.inl rfl) [true], by unfold System.Enables; decide,
        by change (afterFirst : Multiset (Res ⊕ (Nat × List Bool))) = _; decide⟩⟩)
    (.cons ⟨(), ⟨pick 2 (Or.inr rfl) [], by unfold System.Enables; decide,
      by change (finish : Multiset (Res ⊕ (Nat × List Bool))) = _; decide⟩⟩
      (OccurrencePath.refl (P := system.presentation) finish))

def secondThenFirst : OccurrencePath system.presentation start finish :=
  .cons (show Occurrence system.presentation start afterSecond from
      ⟨(), ⟨pick 2 (Or.inr rfl) [true], by unfold System.Enables; decide,
        by change (afterSecond : Multiset (Res ⊕ (Nat × List Bool))) = _; decide⟩⟩)
    (.cons ⟨(), ⟨pick 1 (Or.inl rfl) [], by unfold System.Enables; decide,
      by change (finish : Multiset (Res ⊕ (Nat × List Bool))) = _; decide⟩⟩
      (OccurrencePath.refl (P := system.presentation) finish))

theorem first_order_complete_readout :
    (system.pathEntries firstThenSecond).map
      (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) (fun _ => true)) =
        [⟨(), takeAgain 1⟩, ⟨(), takeAgain 2⟩] := rfl

theorem second_order_complete_readout :
    (system.pathEntries secondThenFirst).map
      (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) (fun _ => true)) =
        [⟨(), takeAgain 2⟩, ⟨(), takeAgain 1⟩] := rfl

theorem same_endpoint_has_different_original_histories :
    (system.pathEntries firstThenSecond).map
      (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) (fun _ => true)) ≠
    (system.pathEntries secondThenFirst).map
      (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) (fun _ => true)) := by
  rw [first_order_complete_readout, second_order_complete_readout]
  intro same
  have impossible : (1 : Nat) = 2 :=
    congrArg (fun entry : persistentReceiver.Entry => (entry.2 : Nat)) (List.cons.inj same).1
  cases impossible

theorem no_endpoint_decoder_for_original_history :
    ¬ ∃ decoder : system.theory.Term → List persistentReceiver.Entry,
      ∀ {target : system.theory.Term} (path : OccurrencePath system.presentation start target),
        decoder target = (system.pathEntries path).map
          (locatedOriginalEntry persistentReceiver permitted (fun _ => 0) (fun _ => true)) := by
  rintro ⟨decoder, recovers⟩
  exact same_endpoint_has_different_original_histories
    ((recovers firstThenSecond).symm.trans (recovers secondThenFirst))

theorem two_cells_pay_exactly_two_occurrences :
    cells (rightPart start) = 2 ∧ cells (rightPart finish) = 0 ∧
      (system.pathEntries firstThenSecond).length = 2 ∧
      (system.pathEntries secondThenFirst).length = 2 := by
  exact ⟨by decide, by decide, rfl, rfl⟩

theorem supplied_order_has_an_actual_original_path :
    ∃ original : OccurrencePath persistentReceiver.presentation twoMessages (leftPart finish),
      persistentReceiver.pathEntries original = [⟨(), takeAgain 1⟩, ⟨(), takeAgain 2⟩] ∧
      (∀ entry ∈ persistentReceiver.pathEntries original, permitted entry.2) ∧
      cells ({(0, [true, true])} : Multiset (Nat × List Bool)) =
        cells (rightPart finish) + (persistentReceiver.pathEntries original).length := by
  obtain ⟨original, readings, allowed, ledger⟩ :=
    locatedPermitted_original_history_ledger persistentReceiver permitted
      (fun _ => 0) (fun _ => true) firstThenSecond
  exact ⟨original, readings.trans first_order_complete_readout, allowed, ledger⟩

theorem funding_cannot_supply_permission :
    persistentReceiver.Enables {Res.receiver, Res.message 3} (takeAgain 3) ∧
      ((0, [true]) : Nat × List Bool) ∈ ({(0, [true])} : Multiset (Nat × List Bool)) ∧
      ¬ ∃ admitted : (permittedSystem persistentReceiver permitted).Instance (),
        admitted.val = takeAgain 3 ∧ ∃ tail : List Bool,
          system.Enables (marking {Res.receiver, Res.message 3} {(0, [true])}) (admitted, tail) := by
  refine ⟨by unfold System.Enables; decide, by decide, ?_⟩
  intro supplied
  have permission :=
    ((locatedPermitted_admission_iff persistentReceiver permitted (fun _ => 0) (fun _ => true)
      {Res.receiver, Res.message 3} {(0, [true])} (takeAgain 3)).mp supplied).1
  exact (by decide : ¬ (3 = 1 ∨ 3 = 2)) permission

theorem right_key_at_wrong_place_cannot_pay :
    ¬ system.Enables (marking twoMessages {(1, [true])}) (pick 1 (Or.inl rfl) []) :=
  fundedAt_disabled_elsewhere (permittedSystem persistentReceiver permitted)
    (fun _ => (0 : Nat)) (fun _ => true)
    twoMessages {(1, [true])} ⟨takeAgain 1, Or.inl rfl⟩ [] (by decide)

theorem right_key_below_head_cannot_pay :
    ¬ system.Enables (marking twoMessages {(0, [false, true])}) (pick 1 (Or.inl rfl) [false]) := by
  intro enabled
  have present :=
    ((locatedPermitted_enables_iff persistentReceiver permitted (fun _ => 0) (fun _ => true)
      twoMessages {(0, [false, true])} ⟨takeAgain 1, Or.inl rfl⟩ [false]).mp enabled).2
  exact (by decide : ¬ ((0, [true, false]) : Nat × List Bool) ∈
    ({(0, [false, true])} : Multiset (Nat × List Bool))) present

theorem one_purse_serializes_two_individually_enabled_firings :
    system.Enables start (pick 1 (Or.inl rfl) [true]) ∧
      system.Enables start (pick 2 (Or.inr rfl) [true]) ∧
      ¬ system.Concurrent start (pick 1 (Or.inl rfl) [true]) (pick 2 (Or.inr rfl) [true]) := by
  exact ⟨by unfold System.Enables; decide, by unfold System.Enables; decide,
    by unfold System.Concurrent; decide⟩

end Mettapedia.GSLT.Causality.ResourceInteraction.LocatedHistoryControls
