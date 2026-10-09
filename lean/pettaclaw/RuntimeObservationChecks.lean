import RuntimeObservation

namespace RuntimeObservationChecks

open RuntimeObservation

def returnedUnsettled : Facts :=
  { call := ⟨.returned, some 4, none⟩, turnPending := some true,
    channelReady := some true, memory := some ⟨40, 3, 20⟩,
    budget := some ⟨2, 100, 60, 10000⟩, background := some ⟨1, 2, 0, some 45⟩,
    inbox := some ⟨1, some 10, some 10⟩, commands := some ⟨2, 1, 1, 0, 0⟩ }

theorem returned_does_not_mean_settled :
    answer returnedUnsettled .provider = .provider ⟨.returned, some 4, none⟩ ∧
      answer returnedUnsettled .settlement = .settlement (some true) := by decide

theorem unavailable_channel_not_healthy :
    channelUnavailable {} = true ∧ channelHealthy {} = false := by decide

theorem unavailable_memory_not_zero_memory :
    answer ({} : Facts) .index ≠ answer { memory := some ⟨0, 0, 20⟩ } .index := by decide

theorem compact_keeps_owned_background_distinctions :
    answer (compact ⟨returnedUnsettled, [900, 800, 700]⟩) .strands =
      .strands (some ⟨1, 2, 0, some 45⟩) := by decide

theorem compact_keeps_budget :
    answer (compact ⟨returnedUnsettled, []⟩) .resources =
      .resources (some ⟨2, 100, 60, 10000⟩) := by decide

theorem compact_keeps_human_input_age :
    answer (compact ⟨returnedUnsettled, [1000000]⟩) .humanInput =
      .humanInput (some ⟨1, some 10, some 10⟩) := by decide

theorem compact_keeps_receipt_distinctions :
    answer (compact ⟨returnedUnsettled, []⟩) .receipts =
      .receipts (some ⟨2, 1, 1, 0, 0⟩) := by decide

theorem unknown_input_is_not_a_clear_inbox :
    answer ({} : Facts) .humanInput ≠ answer { inbox := some ⟨0, none, none⟩ } .humanInput := by decide

def brokenSettled (facts : Facts) : Facts :=
  if facts.call.phase == .returned then { facts with turnPending := some false }
  else facts

theorem completion_shortcut_detected :
    answer (brokenSettled returnedUnsettled) .settlement ≠
      answer returnedUnsettled .settlement := by decide

def brokenHealthy (facts : Facts) : Facts :=
  { facts with channelReady := some (facts.channelReady.getD true) }

theorem unknown_as_healthy_detected :
    answer (brokenHealthy {}) .channel ≠ answer ({} : Facts) .channel := by decide

def disconnected (facts : Facts) : Answer :=
  answer { facts with channelReady := none } .channel

theorem disconnected_channel_detected :
    disconnected { channelReady := some false } ≠
      answer { channelReady := some false } .channel := by decide

end RuntimeObservationChecks
