import MettapediaFourColor.TwoDiamondIntrinsic
import MettapediaFourColor.OpenTangleKempeClosure
import Mettapedia.GraphTheory.FourColor.CycleCapGeometry
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryReindexWitness
import Mettapedia.GraphTheory.FourColor.OpenTangleInternalReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Replacing the shared-tip diamond disk by its boundary cycle

Twenty source vertices are replaced by an eight-cycle. Equal ordered face
returns, equal Euler mass and connected bridgeless interiors preserve the
closed spherical cubic map class in every fixed exterior. All introduced
vertices are counted, so the whole closed map loses exactly twelve vertices.

The colouring implication uses the existing transferred shared-tip repair.
Its exterior Kempe-closure hypothesis remains explicit; geometric class
preservation alone does not establish that hypothesis or occurrence coverage.
`TwoDiamondHubColoring.reconstruct` supplies the stronger implication without
that hypothesis, using a closed reference observation and exact readback.
-/

namespace FourColor.TwoDiamondCycleReplacement

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24TwoEdgeCutMinimality GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph OpenTangleVertexReflection
open OpenTanglePortReplacement OpenTangleReplacementEuler OpenTangleMarkedFace
open OpenTangleRewireFaces
open OpenTangleClosedWitness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Reverse the cycle's outward-port coordinates to match the source order. -/
def coordinates : Fin 8 ≃ Empty ⊕ Fin 8 where
  toFun i := .inr (-i)
  invFun
    | .inl e => nomatch e
    | .inr i => -i
  left_inv := by intro i; simp
  right_inv := by rintro (e | i); exact nomatch e; simp

abbrev cycle := (CycleCap.openCap 8 (by decide)).reindexBoundary coordinates

def cycleIso : OpenTangleIsomorphism.Iso cycle (CycleCap.openCap 8 (by decide)) :=
  OpenTangleIsomorphism.boundaryReindex _ coordinates

theorem cycle_returnCode : returnCode cycle = finRotate 8 := by
  have h := cycleIso.returnCode
  rw [returnCode_asOpen, CycleCap.encode_cap] at h
  change coordinates.permCongr (returnCode cycle) = CycleCap.boundaryPerm 8 at h
  apply Equiv.ext
  intro i
  apply coordinates.injective
  have hi := congrArg (fun p => p (coordinates i)) h
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hi
  exact hi.trans (by
    have hf : ∀ i : Fin 8,
        CycleCap.boundaryPerm 8 (coordinates i) = coordinates (finRotate 8 i) := by
      decide +kernel
    exact hf i)

theorem cycle_eulerMass : eulerMass cycle = 4 := by
  have h := GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts
    cycleIso.darts (openPhi cycle)
  rw [cycleIso.phi_permCongr] at h
  unfold eulerMass
  rw [← h]
  exact CycleCap.eulerMass 8 (by decide)

theorem cycle_connected_bridgeless :
    (sideMultigraph cycle).Connected ∧ (sideMultigraph cycle).Bridgeless :=
  CycleCap.cap_connected_bridgeless 8 (by decide)

theorem cycle_cubic : OpenIsCubic cycle := by
  unfold OpenIsCubic
  decide +kernel

theorem cycle_rotation_cyclic : OpenRotationCyclic cycle := by
  intro d e hv
  have finite : ∀ d e : CycleCap.Dart 8 ⊕ Fin 8,
      cycle.vertOf d = cycle.vertOf e → ∃ n : Fin 3, (cycle.rho ^ n.val) d = e := by
    decide +kernel
  obtain ⟨n,hn⟩ := finite d e hv
  exact ⟨n.val, by rw [zpow_natCast]; exact hn⟩

section Context
universe u
variable {V I B : Type u} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Fin 8)

abbrev original := outside.composeRotationSystem TwoDiamondTangle.piece seam
abbrev reduced := outside.composeRotationSystem cycle seam

/-- The geometric replacement permits arbitrary, including disconnected,
exteriors. No theorem about their colourings is assumed here. -/
theorem replacement_class
    (h : BridgelessSphericalCubicMapData (original outside seam)) :
    BridgelessSphericalCubicMapData (reduced outside seam) := by
  have structural := OpenTangleInternalReplacement.replacement_structural outside
    TwoDiamondTangle.piece cycle seam seam
    ⟨TwoDiamondTangle.piece_connected, TwoDiamondTangle.piece_bridgeless⟩
    cycle_connected_bridgeless
  have heuler : compositeEuler outside TwoDiamondTangle.piece seam =
      compositeEuler outside cycle seam := by
    apply (OpenTanglePortReplacement.euler_eq_iff_mass _ _
      (TwoDiamondTangle.piece_returnCode.trans cycle_returnCode.symm) outside seam).mpr
    exact TwoDiamondTangle.piece_eulerMass.trans cycle_eulerMass.symm
  exact {
    spherical := {
      cubic := isCubic_composeRotationSystem outside cycle seam
        (exterior_isCubic outside _ seam h.spherical.cubic) cycle_cubic
      euler := by
        change compositeEuler outside cycle seam = 2
        rw [← heuler]
        exact h.spherical.euler }
    primalConnected := (structural.mp ⟨h.primalConnected,h.edgeBridgeFree⟩).1
    vertexRotationCyclic := vertexRotationCyclic_composeRotationSystem outside cycle seam
      (exterior_rotationCyclic outside _ seam h.vertexRotationCyclic) cycle_rotation_cyclic
    edgeBridgeFree := (structural.mp ⟨h.primalConnected,h.edgeBridgeFree⟩).2 }

omit [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
/-- Count the complete operation, including all eight replacement vertices. -/
theorem whole_vertex_loss : Fintype.card (V ⊕ Fin 8) + 12 =
    Fintype.card (V ⊕ Fin 20) := by simp

omit [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem replacement_strict : Fintype.card (V ⊕ Fin 8) <
    Fintype.card (V ⊕ Fin 20) := by simp

/-- Restrict the smaller colouring, repair the genuine exterior and glue
with the complete joint-tip interior witness. The exterior may be recoloured. -/
theorem reconstruct
    (h : BridgelessSphericalCubicMapData (original outside seam))
    (hclosed : KempeClosed (OpenTangleKempeRepair.Trace outside seam.symm))
    (hc : RotationSystemTaitColorable (reduced outside seam)) :
    RotationSystemTaitColorable (original outside seam) := by
  obtain ⟨c,hc⟩ := hc
  obtain ⟨r,_,hr,_,_,_⟩ := restrictOpen outside cycle seam c hc
  exact OpenTangleKempeRepair.colorable_of_exterior TwoDiamondTangle.piece outside seam.symm
    TwoDiamondTangle.open_repair
    (GoertzelV24PortTangleCutParity.isCubic_ofOpenTangleData outside
      (exterior_isCubic outside _ seam h.spherical.cubic)) hclosed r hr

/-- A physically certified exterior discharges the closure obligation using
the existing all-width matching theorem. -/
theorem reconstruct_of_noncrossing
    (h : BridgelessSphericalCubicMapData (original outside seam))
    (hnoncrossing : ∀
      (c : GoertzelV24PortTangleGluing.PortTangle.Coloring
        (GoertzelV24PortTangleGluing.ofOpenTangleData outside))
      (hc : GoertzelV24PortTangleGluing.PortTangle.IsProper c),
      Compositional.CyclicBoundaryMatching.IsNoncrossingMatching
        (Compositional.BoundaryKempeSwitch.physicalMateInCoordinates seam.symm
          (GoertzelV24PortTangleGluing.ofOpenTangleData outside)
          (GoertzelV24PortTangleCutParity.isCubic_ofOpenTangleData outside
            (exterior_isCubic outside _ seam h.spherical.cubic)) c hc .bluePurple))
    (hc : RotationSystemTaitColorable (reduced outside seam)) :
    RotationSystemTaitColorable (original outside seam) := by
  apply reconstruct outside seam h _ hc
  exact OpenTangleKempeRepair.closed_of_physical_noncrossing outside seam.symm
    (GoertzelV24PortTangleCutParity.isCubic_ofOpenTangleData outside
      (exterior_isCubic outside _ seam h.spherical.cubic)) hnoncrossing

end Context
end
end FourColor.TwoDiamondCycleReplacement
