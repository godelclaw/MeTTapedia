import Mettapedia.GraphTheory.FourColor.TwoCellSourceRepair
import Mettapedia.GraphTheory.FourColor.DualTruncateKempeTransport
import Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction
import Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample

/-!
# Shared two-cell reconstruction on actual embedded maps

The same incidence-and-pin contract reconstructs an eighteen-vertex prism
expansion and a sixty-vertex dodecahedral expansion. A second dodecahedral
exterior is repaired by two successive source switches. Each switch induces
a saturated region of actual original edges; the second acts on the field
left by the first. Only partial exterior colourings are supplied as data.

These are reconstruction and history consumers. They do not supply a
smaller embedded operation or a universal occurrence theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoCellSourceRepairExamples

open DualTruncateColoring DualTruncateOpenPatch TwoCellSourceRepair
open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Prism

abbrev source := DualTruncateSourceDomainExample.original
abbrev target := rotation source

def frame : Frame source where
  left := 0
  right := 3
  distinct := by decide
  pins := ![1,2,5,4]
  pins_outside := by decide +kernel
  left_neighbours := by decide +kernel
  right_neighbours := by decide +kernel

instance : DecidablePred frame.outside := by unfold Frame.outside; infer_instance
instance : DecidablePred frame.selected := by unfold Frame.selected; infer_instance

def exterior (v : Fin 6) : Color :=
  if v = 0 ∨ v = 3 then 0 else if v = 1 ∨ v = 5 then red else blue

def mask (v : Fin 6) : Prop := v = 2
instance : DecidablePred mask := by unfold mask; infer_instance

theorem exterior_proper : SourcePatchKempe.ExteriorProper source frame.outside exterior := by
  unfold SourcePatchKempe.ExteriorProper
  decide +kernel

theorem no_original_joint_choices : ¬∃ x y, TwoCellBoundaryChoice.Compatible
    (exterior (frame.pins 0)) (exterior (frame.pins 1))
    (exterior (frame.pins 2)) (exterior (frame.pins 3)) x y := by
  rw [TwoCellBoundaryChoice.choices_iff] <;> decide +kernel

theorem region : SourcePatchKempe.Region source frame.outside exterior .bluePurple mask := by
  constructor <;> unfold pairActiveColor Color.twoColor <;> decide +kernel

theorem contract : OnePin source frame exterior .bluePurple mask red blue := by
  constructor
  · decide +kernel
  · decide
  · unfold pairActiveColor Color.twoColor; decide
  · decide +kernel
  · decide
  · decide

def witness : ThreeVertexColoring source :=
  repairedSource frame exterior exterior_proper .bluePurple mask region red blue contract

def repairedExterior := SourcePatchKempe.switched exterior .bluePurple mask
abbrev physicalMask := DualTruncateKempeTransport.edgeMask source frame.selected exterior .bluePurple mask
def field := RotationPatchKempe.switched (edgeColour source exterior) .bluePurple physicalMask

theorem target_tait : target.IsTaitEdgeColoring (colouring source witness) :=
  colouring_nonzero source witness

theorem physical_region :
    RotationPatchKempe.Region target (fun d => ¬vertexRegion source frame.selected d)
      (edgeColour source exterior) .bluePurple physicalMask := by
  apply DualTruncateKempeTransport.physical_region
  · simpa only [frame.outside_eq_not_selected] using exterior_proper
  · simpa only [frame.outside_eq_not_selected] using region

theorem reconstructs : Extends source (vertexRegion source frame.selected) field
    (colouring source witness) := by
  have hc := SourcePatchKempe.switched_exterior source frame.outside exterior
    exterior_proper .bluePurple mask region
  have hj := repaired_joint_choices frame exterior exterior_proper .bluePurple mask
    region red blue contract
  have hi := frame.reconstructed_extends repairedExterior hc blue (red+blue) hj
  have he := DualTruncateKempeTransport.exact_effect source frame.selected exterior .bluePurple mask
    (by simpa only [frame.outside_eq_not_selected] using exterior_proper)
    (by simpa only [frame.outside_eq_not_selected] using region)
  intro d hd i
  exact (hi d hd i).trans (he d hd i)

end Prism

namespace Dodeca

abbrev source := TwoCellCycleObstruction.source
abbrev target := rotation source

def frame : Frame source where
  left := 0
  right := 1
  distinct := by decide
  pins := ![10,19,2,8]
  pins_outside := by decide +kernel
  left_neighbours := by decide +kernel
  right_neighbours := by decide +kernel

instance : DecidablePred frame.outside := by unfold Frame.outside; infer_instance
instance : DecidablePred frame.selected := by unfold Frame.selected; infer_instance

namespace Single

abbrev exterior := TwoCellCycleObstruction.exteriorColour
def mask (v : Fin 20) : Prop := v = 3 ∨ v = 4 ∨ v = 17 ∨ v = 19
instance : DecidablePred mask := by unfold mask; infer_instance

theorem exterior_proper : SourcePatchKempe.ExteriorProper source frame.outside exterior := by
  unfold SourcePatchKempe.ExteriorProper
  decide +kernel

theorem region : SourcePatchKempe.Region source frame.outside exterior .redPurple mask := by
  constructor <;> unfold pairActiveColor Color.twoColor <;> decide +kernel

theorem contract : OnePin source frame exterior .redPurple mask blue red := by
  constructor
  · decide +kernel
  · decide
  · unfold pairActiveColor Color.twoColor; decide
  · decide +kernel
  · decide
  · decide

def witness : ThreeVertexColoring source :=
  repairedSource frame exterior exterior_proper .redPurple mask region blue red contract

def repairedExterior := SourcePatchKempe.switched exterior .redPurple mask
abbrev physicalMask := DualTruncateKempeTransport.edgeMask source frame.selected exterior .redPurple mask
def field := RotationPatchKempe.switched (edgeColour source exterior) .redPurple physicalMask

theorem target_tait : target.IsTaitEdgeColoring (colouring source witness) :=
  colouring_nonzero source witness

theorem physical_region :
    RotationPatchKempe.Region target (fun d => ¬vertexRegion source frame.selected d)
      (edgeColour source exterior) .redPurple physicalMask := by
  apply DualTruncateKempeTransport.physical_region
  · simpa only [frame.outside_eq_not_selected] using exterior_proper
  · simpa only [frame.outside_eq_not_selected] using region

theorem reconstructs : Extends source (vertexRegion source frame.selected) field
    (colouring source witness) := by
  have hc := SourcePatchKempe.switched_exterior source frame.outside exterior
    exterior_proper .redPurple mask region
  have hj := repaired_joint_choices frame exterior exterior_proper .redPurple mask
    region blue red contract
  have hi := frame.reconstructed_extends repairedExterior hc red (blue+red) hj
  have he := DualTruncateKempeTransport.exact_effect source frame.selected exterior .redPurple mask
    (by simpa only [frame.outside_eq_not_selected] using exterior_proper)
    (by simpa only [frame.outside_eq_not_selected] using region)
  intro d hd i
  exact (hi d hd i).trans (he d hd i)

end Single

namespace History

/-- The omitted source vertices carry zero. This is a partial exterior,
not a complete source colouring supplied as a certificate. -/
def word : ByteArray := ByteArray.mk #[0,0,2,3,1,2,1,2,1,3,1,2,1,2,3,1,3,2,1,2]
def exterior (v : Fin 20) : Color :=
  if frame.selected v then 0 else CubicRotationByteCertificate.wordColour word v.val

def mask₁ (v : Fin 20) : Prop := v = 8 ∨ v = 9 ∨ v = 10
def mask₂ (v : Fin 20) : Prop := v = 10 ∨ v = 11
instance : DecidablePred mask₁ := by unfold mask₁; infer_instance
instance : DecidablePred mask₂ := by unfold mask₂; infer_instance

def exterior₁ := SourcePatchKempe.switched exterior .redPurple mask₁
def exterior₂ := SourcePatchKempe.switched exterior₁ .bluePurple mask₂

theorem exterior_proper : SourcePatchKempe.ExteriorProper source frame.outside exterior := by
  unfold SourcePatchKempe.ExteriorProper
  decide +kernel

theorem no_original_joint_choices : ¬∃ x y, TwoCellBoundaryChoice.Compatible
    (exterior (frame.pins 0)) (exterior (frame.pins 1))
    (exterior (frame.pins 2)) (exterior (frame.pins 3)) x y := by
  rw [TwoCellBoundaryChoice.choices_iff] <;> decide +kernel

theorem region₁ : SourcePatchKempe.Region source frame.outside exterior .redPurple mask₁ := by
  constructor <;> unfold pairActiveColor Color.twoColor <;> decide +kernel

theorem exterior₁_proper : SourcePatchKempe.ExteriorProper source frame.outside exterior₁ :=
  SourcePatchKempe.switched_exterior source frame.outside exterior exterior_proper
    .redPurple mask₁ region₁

/-- The second region is checked in the state left by the first step. -/
theorem region₂ : SourcePatchKempe.Region source frame.outside exterior₁ .bluePurple mask₂ := by
  constructor <;> unfold pairActiveColor Color.twoColor <;> decide +kernel

theorem exterior₂_proper : SourcePatchKempe.ExteriorProper source frame.outside exterior₂ :=
  SourcePatchKempe.switched_exterior source frame.outside exterior₁ exterior₁_proper
    .bluePurple mask₂ region₂

theorem joint_choices : TwoCellBoundaryChoice.Compatible
    (exterior₂ (frame.pins 0)) (exterior₂ (frame.pins 1))
    (exterior₂ (frame.pins 2)) (exterior₂ (frame.pins 3)) purple red := by
  unfold TwoCellBoundaryChoice.Compatible
  decide +kernel

def witness : ThreeVertexColoring source :=
  frame.complete exterior₂ exterior₂_proper purple red joint_choices

abbrev physicalMask₁ := DualTruncateKempeTransport.edgeMask source frame.selected exterior .redPurple mask₁
abbrev physicalMask₂ := DualTruncateKempeTransport.edgeMask source frame.selected exterior₁ .bluePurple mask₂
def field₁ := RotationPatchKempe.switched (edgeColour source exterior) .redPurple physicalMask₁
def field₂ := RotationPatchKempe.switched field₁ .bluePurple physicalMask₂

theorem effect₁ : Extends source (vertexRegion source frame.selected) field₁
    (edgeColour source exterior₁) := by
  apply DualTruncateKempeTransport.exact_effect
  · simpa only [frame.outside_eq_not_selected] using exterior_proper
  · simpa only [frame.outside_eq_not_selected] using region₁

theorem physical_region₁ :
    RotationPatchKempe.Region target (fun d => ¬vertexRegion source frame.selected d)
      (edgeColour source exterior) .redPurple physicalMask₁ := by
  apply DualTruncateKempeTransport.physical_region
  · simpa only [frame.outside_eq_not_selected] using exterior_proper
  · simpa only [frame.outside_eq_not_selected] using region₁

theorem physical_region₂ :
    RotationPatchKempe.Region target (fun d => ¬vertexRegion source frame.selected d)
      field₁ .bluePurple physicalMask₂ := by
  apply DualTruncateKempeTransport.physical_region_after _ _ _ _ _ _ _ field₁ effect₁
  · simpa only [frame.outside_eq_not_selected] using exterior₁_proper
  · simpa only [frame.outside_eq_not_selected] using region₂

theorem effect₂ : Extends source (vertexRegion source frame.selected) field₂
    (edgeColour source exterior₂) := by
  apply DualTruncateKempeTransport.exact_effect_after _ _ _ _ _ _ _ field₁ effect₁
  · simpa only [frame.outside_eq_not_selected] using exterior₁_proper
  · simpa only [frame.outside_eq_not_selected] using region₂

theorem target_tait : target.IsTaitEdgeColoring (colouring source witness) :=
  colouring_nonzero source witness

theorem reconstructs : Extends source (vertexRegion source frame.selected) field₂
    (colouring source witness) := by
  have hi := frame.reconstructed_extends exterior₂ exterior₂_proper purple red joint_choices
  intro d hd i
  exact (hi d hd i).trans (effect₂ d hd i)

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

theorem every_complete_sweep (order : List source.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic source)
        (DualTruncateConstructionGSLT.rotationCyclic source) order hn he hcover).trace)
      Fin.elim0 Fin.elim0 :=
  DualTruncateConstructionGSLT.supported_encoded_route source witness order hn he hcover

end History
end Dodeca
end
end Mettapedia.GraphTheory.FourColor.TwoCellSourceRepairExamples
