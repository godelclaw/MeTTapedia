import MettapediaFourColor.WheelRepairChecked
import MettapediaFourColor.RuleFanSevenCluster
import MettapediaFourColor.TwoFiveWheelColouring

/-!
# Complete wheel repair and its six compositional descendants

The checked thirteen-port certificate supplies the full repair contract.
One boundary-triangle collapse transports it to every second-five position,
with no new target table. The existing disk and singleton-contract theorems
then reconstruct colourings in the actual ambient map. The same repaired
witness also decomposes into two compatible GSLT sectors.

This closes the local repair premise in shared-fan seven-centre supply.
The joint pair/path/triangle classifications and universal fan supply remain
separate mathematical obligations.
-/

namespace FourColor.WheelFamilyChecked

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open KempeBoundarySplit CyclicColourRoute

theorem source_repair : D3009RepairGeometry.SourceRepair := WheelRepairCertificate.repair

/-- All six target repairs use the same complete source certificate. -/
theorem two_five_repair (p : Fin 6) :
    Repairs (GraphTrace (TwoFiveWheelData.input p).graph (TwoFiveWheelData.input p).boundary) 12 :=
  TwoFiveWheelRepair.transfer source_repair p

/-- Reconstruction retains the entire chosen exterior relation. -/
theorem reconstruct (p : Fin 6) (et : List Color) (length : et.length = 12)
    (proper : (0 : Color) ∉ et) (conserved : et.sum = 0) (Q : List Color → Prop)
    (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : (TwoFiveWheelData.input p).graph.Coloring Color,
      Q (trace ((TwoFiveWheelData.input p).boundary.map k)) :=
  TwoFiveWheelRepair.reconstruct source_repair p et length proper conserved Q closed outside

/-- Both sectors share one centre colour and both seam colours. -/
theorem repaired_sectors (p : Fin 6) (et : List Color) (length : et.length = 12)
    (proper : (0 : Color) ∉ et) (conserved : et.sum = 0) (Q : List Color → Prop)
    (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : (TwoFiveWheelColouring.boundaryGraph p).Coloring Color,
      Q (trace ((List.finRange 12).map k)) ∧
        ∃ z a b,
          (WheelColouringGSLT.semantics (by decide : 2 ≤ 7)
            (TwoFiveWheelColouring.touch p) k z).Supports (route 0 3) a b ∧
          (WheelColouringGSLT.semantics (by decide : 2 ≤ 7)
            (TwoFiveWheelColouring.touch p) k z).Supports (route 3 4) b a :=
  TwoFiveWheelColouring.repaired_sectors p source_repair et length proper conserved Q closed outside

noncomputable section

open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- The original wheel uses its actual injective disk and strict descent. -/
theorem source_colorable (r : D3009Boundary.Occurrence (rotation original minimal)) :
    (DualGraphQuery.map (rotation original minimal)).FourColorable :=
  D3009RepairGeometry.colorable original minimal source_repair r

/-- The same actual-map reconstruction applies to every target position. -/
theorem two_five_colorable (p : Fin 6)
    (r : WheelBoundaryCompletion.Occurrence (WheelBoundaryLayouts.twoFive p)
      (rotation original minimal)) :
    (DualGraphQuery.map (rotation original minimal)).FourColorable :=
  TwoFiveWheelRepairGeometry.colorable p original minimal source_repair r

theorem source_profile_excluded (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd →
      (graph original minimal).degree w = 6) : False :=
  D3009RepairGeometry.profile_excluded original minimal source_repair d seven five six

theorem two_five_profile_excluded (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (q : _) (adj : (graph original minimal).Adj d.fst q)
    (other_five : (graph original minimal).degree q = 5) (distinct : q ≠ d.snd)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd → w ≠ q →
      (graph original minimal).degree w = 6) : False :=
  TwoFiveWheelRepairGeometry.profile_excluded original minimal source_repair
    d seven five q adj other_five distinct six

/-- The same surviving fan now supplies the adjacent pair without a
caller-supplied wheel repair or exterior-colouring oracle. -/
theorem pair_exists (d : (graph original minimal).Dart)
    (fixed : RuleFanSupply.Fixed (rotation original minimal) d)
    (flat : LocalCoverageAssembly.OnBall (graph original minimal) d.snd 3
      (fun v => NearLinearCharge.finalCharge (rotation original minimal) v = 0))
    (bound : LocalCoverageAssembly.OnBall (graph original minimal) d.snd 3
      (fun v => (graph original minimal).degree v ≤ 7)) :
    Nonempty (RuleFanSevenCluster.Pair original minimal d) :=
  RuleFanSevenCluster.pair_exists original minimal source_repair d fixed flat bound

end
end FourColor.WheelFamilyChecked
