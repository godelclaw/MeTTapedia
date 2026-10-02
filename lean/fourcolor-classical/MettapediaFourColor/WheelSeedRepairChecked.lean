import MettapediaFourColor.WheelSeedRepairCertificate
import MettapediaFourColor.D3009ColouringExample

/-!
# Repairing the wheel boundary whose two sector histories do not close

All nine retained states and all 132 unsigned exterior pairings are checked.
The result concerns this seed trace and an arbitrary Kempe-closed exterior
containing it. It is not a complete thirteen-port reducibility certificate.
-/
namespace FourColor.WheelSeedRepairCertificate

open Color D3009Colouring CyclicColourRoute

set_option maxRecDepth 65536

set_option maxHeartbeats 2000000 in
-- Check the complete bounded certificate, including its 132 exterior skeletons.
/-- Check genuine source colourings and all supplied whole-chord answers. -/
theorem checked : ∀ i : State, check i = true := by decide +kernel

def seedTrace : List Color := trace ((List.finRange 13).map D3009ColouringExample.bad)

theorem seed_word : seedTrace.map EdgePerm.e231 = word ⟨0, by decide⟩ := by
  decide +kernel

/-- The nonextending boundary admits compatible repair against every closed exterior. -/
theorem seed_repair : KempeCoclosure Supports seedTrace := by
  apply kempeCoclosure_of_map EdgePerm.e231
  rw [seed_word]
  exact coclosure checked ⟨0, by decide⟩

/-- Repaired choices close both sectors, with a shared centre and both seams. -/
theorem repaired_sectors (outside : List Color → Prop) (closed : KempeClosed outside)
    (initial : outside seedTrace) :
    ∃ k : boundaryGraph.Coloring Color,
      outside (trace ((List.finRange 13).map k)) ∧ ∃ z a b,
        (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch k z).Supports
          (route 0 3) a b ∧
        (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch k z).Supports
          (route 3 4) b a := by
  obtain ⟨et, inside, exterior⟩ := seed_repair outside closed initial
  obtain ⟨k, ht, hw⟩ := (graphTrace_iff et).mp inside
  refine ⟨k, ht ▸ exterior, ?_⟩
  exact (WheelColouringGSLT.split_iff (by decide) touch k 3 4 rfl).mp hw

/-- The same repaired trace is realized by the literal Y/H construction. -/
theorem repaired_construction (outside : List Color → Prop) (closed : KempeClosed outside)
    (initial : outside seedTrace) :
    ∃ et, outside et ∧ (cfmap D3009Construction.config).map.RingTrace
      (cfring D3009Construction.config).reverse et := by
  obtain ⟨et, inside, exterior⟩ := seed_repair outside closed initial
  exact ⟨et, exterior, (D3009Construction.ringTrace_iff et).mpr inside⟩

end FourColor.WheelSeedRepairCertificate
