import MettapediaFourColor.ResidualSeedRepairCertificate
import MettapediaFourColor.ThreeBlockCore

/-!
# A mixed-pair strategy for the obstructed three-run seed

Seven nonterminal decisions share 34 actual source colourings. Every one of
the 161 unsigned matching cases is checked, including its whole-chord choice
and strict rank descent. This certifies one seed against every Kempe-closed
exterior containing it. It does not assert full D0092 reducibility or a bound
on the number of individual physical component switches.
-/

namespace FourColor.ResidualSeedRepairCertificate

open Color

set_option maxRecDepth 65536

set_option maxHeartbeats 2000000 in
/-- Check all source witnesses and every supplied matching answer. -/
theorem checked : ∀ i : State, check i = true := by decide +kernel

def seedTrace : List Color :=
  trace ((List.finRange 11).map (ThreeBlockCore.word false false false))

def seed : State := ⟨ResidualSeedRepairData.seed, by decide⟩

theorem seed_word : seedTrace.map EdgePerm.e321 = word seed := by decide +kernel

/-- The repair permits changing colour pairs while preserving the entire
exterior observation. No successful next move is supplied as a hypothesis. -/
theorem seed_repair : KempeCoclosure Supports seedTrace := by
  apply kempeCoclosure_of_map EdgePerm.e321
  rw [seed_word]
  exact coclosure checked seed

end FourColor.ResidualSeedRepairCertificate
