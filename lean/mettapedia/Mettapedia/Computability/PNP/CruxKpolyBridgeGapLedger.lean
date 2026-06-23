import Mettapedia.Computability.PNP.CruxKpolyBridgeCurrentStatus

/-!
# PNP crux gap-completed ledger packet

This module contains the optional bookkeeping packet that marks every currently
named gap as covered by construction.  It is deliberately separate from the
live status surface so normal imports do not mistake this ledger object for
mathematical closure of the missing repairs.
-/

namespace Mettapedia.Computability.PNP
/-- The formal packet obtained by adding precisely the current gap list to the
current local packet.  This does not prove those gaps mathematically; it is the
ledger object used to state what a full current-audit closure would have to
cover. -/
def currentPNPGapCompletedPacket : PNPCruxPacket where
  covers repair :=
    currentPNPLocalCruxPacket.covers repair ∨
      repair ∈ currentPNPUncoveredRepairClasses

/-- The gap-completed ledger packet extends the current local packet. -/
theorem currentPNPGapCompletedPacket_extends_current :
    currentPNPGapCompletedPacket.Extends currentPNPLocalCruxPacket := by
  intro repair hCurrent
  exact Or.inl hCurrent

/-- The gap-completed ledger packet covers every currently named gap. -/
theorem currentPNPGapCompletedPacket_covers_current_gaps :
    currentPNPGapCompletedPacket.CoversList currentPNPUncoveredRepairClasses := by
  intro repair hGap
  exact Or.inr hGap

/-- The gap-completed ledger packet covers the selected next marginal target. -/
theorem currentPNPGapCompletedPacket_covers_currentPNPNextMarginalTarget :
    currentPNPGapCompletedPacket.covers currentPNPNextMarginalTarget := by
  exact Or.inr currentPNPNextMarginalTarget_mem_uncovered

/-- Adding exactly the named current gaps is sufficient to make the ledger
stop-grade.  The theorem is bookkeeping, not a claim that the missing
mathematics has been supplied. -/
theorem stopGrade_currentPNPGapCompletedPacket :
    currentPNPGapCompletedPacket.StopGrade := by
  rw [stopGrade_iff_covers_currentPNP_gaps_of_extends_current
    currentPNPGapCompletedPacket_extends_current]
  exact currentPNPGapCompletedPacket_covers_current_gaps

end Mettapedia.Computability.PNP
