import MettapediaFourColor.FourTriangleConstruction
import MettapediaFourColor.FullRankRepair
import FourColor.Bulk.Cfg.Grp10_00

/-!
# Full joint boundary repair for the four-triangle fan and tripod

The existing rank certificates of configurations 33 and 37 cover the entire
proper ten-port domain after colour permutations. Two kernel mask checks and
one common soundness theorem establish repair without using their recorded
contracts. The exact source bridge carries genuine colouring witnesses.

This reuses two classical certificates; it introduces no new colouring table
and removes no certificate from the complete classical assembly.
-/

namespace FourColor.FourTriangleRepair

open KempeBoundarySplit FourTriangleConstruction

set_option maxRecDepth 65536

set_option maxHeartbeats 0 in
-- One comparison of the complete ten-port masks uses kernel big-natural arithmetic.
theorem fan_mask :
    (((2 ^ 3 ^ 9 - 1) ^^^ Bulk.xaccAt 9 9 0) &&&
      ((2 ^ 3 ^ 9 - 1) ^^^ Bulk.knownMask 9 Bulk.Cfg032.R)) = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The same full-domain comparison is independent of the recorded contract.
theorem tripod_mask :
    (((2 ^ 3 ^ 9 - 1) ^^^ Bulk.xaccAt 9 9 0) &&&
      ((2 ^ 3 ^ 9 - 1) ^^^ Bulk.knownMask 9 Bulk.Cfg036.R)) = 0 := by
  decide +kernel

theorem fan_reference : Repairs ((cfmap cf033).map.RingTrace (cfring cf033).reverse) 10 :=
  FullRankRepair.repairs Bulk.Cfg032.cf 9 Bulk.Cfg032.hcf
    Bulk.Cfg032.R Bulk.Cfg032.H Bulk.Cfg032.C
    (by rw [Bulk.Cfg032.hH, Bulk.length_minPerm]) (by decide)
    Bulk.Cfg032.hH Bulk.Cfg032.hgood Bulk.Cfg032.hchoice Bulk.Cfg032.hpairs fan_mask

theorem tripod_reference : Repairs ((cfmap cf037).map.RingTrace (cfring cf037).reverse) 10 :=
  FullRankRepair.repairs Bulk.Cfg036.cf 9 Bulk.Cfg036.hcf
    Bulk.Cfg036.R Bulk.Cfg036.H Bulk.Cfg036.C
    (by rw [Bulk.Cfg036.hH, Bulk.length_minPerm]) (by decide)
    Bulk.Cfg036.hH Bulk.Cfg036.hgood Bulk.Cfg036.hchoice Bulk.Cfg036.hpairs tripod_mask

theorem reference_repair (p : Fin 2) :
    Repairs ((cfmap (config p)).map.RingTrace (cfring (config p)).reverse) 10 := by
  fin_cases p
  · exact fan_reference
  · exact tripod_reference

/-- The ordered boundary includes the checked orientation convention. -/
theorem repair (p : Fin 2) :
    Repairs (GraphTrace (FourTriangleCore.input p).graph (boundary p)) 10 := by
  intro et hlen hzero hsum Q closed outside
  obtain ⟨es, hs, hqs⟩ := reference_repair p et hlen hzero hsum Q closed outside
  exact ⟨es, (ringTrace_iff p es).mp hs, hqs⟩

/-- Reconstruct an actual source colouring compatible with the same exterior. -/
theorem reconstruct (p : Fin 2) (et : List Color) (length : et.length = 10)
    (proper : (0 : Color) ∉ et) (conserved : et.sum = 0)
    (Q : List Color → Prop) (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : (FourTriangleCore.input p).graph.Coloring Color,
      Q (trace ((boundary p).map k)) := by
  obtain ⟨es, ⟨k, rfl⟩, hQ⟩ := repair p et length proper conserved Q closed outside
  exact ⟨k, hQ⟩

end FourColor.FourTriangleRepair
